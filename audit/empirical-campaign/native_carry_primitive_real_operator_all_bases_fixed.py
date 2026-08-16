#!/usr/bin/env python3
"""Scanner completo do operador primitivo de carry em R^2.

O estado associado ao inteiro positivo n e

    psi_t(n) = n^(-1/2) (cos(-t log n), sin(-t log n)).

Tudo e calculado em coordenadas reais float64.

Camera 2
--------

O cutoff M conserva exatamente o significado de "M centros". A carta C2 usa

    semente:  psi_t(1)
    centros:  c = 4, 8, ..., 4M
    bracket:  psi_t(c-1) - 2 psi_t(c) + psi_t(c+1).

Cada centro tambem e classificado de modo unico como c = 2^k m, com k >= 2
e m impar. Essa classificacao serve apenas para abrir o diagnostico por
profundidade; nenhum peso adicional e inserido no operador.

Cameras naturais b >= 3
-----------------------

A carta saturada usa todos os raios geometricamente distintos ate o meio da
celula posicional:

    h = floor(b/2)
    sementes: psi_t(1), ..., psi_t(h)
    centros:  c = b, 2b, ..., Mb
    raios:    r = 1, ..., h
    bracket:  psi_t(c-r) - 2 psi_t(c) + psi_t(c+r).

Para b impar, h=(b-1)/2 e os pares +/-r representam as b-1 classes nao
centrais. Para b par, h=b/2 e o ultimo raio e antipodal: +h == -h (mod b),
mas c-h e c+h sao pernas geometricas distintas. Exemplo: na C4, r=1 le os
impares e r=2 le os pares divisiveis por 2 mas nao por 4. A camera 2 continua
especial: sua carta canonica alinhada usa centros 4m e somente o setor r=1.

Leitura
-------

Se z_e sao as coordenadas (sementes e brackets), o resultante primitivo e

    R(t) = sum_e z_e.

O zero bruto e R(t) = (0, 0). Para comparar cutoffs, o scanner publica a
visibilidade adimensional

    score(t) = ||R(t)||^2 / (N * sum_e ||z_e||^2),

que pertence a [0, 1] salvo erro de arredondamento. A normalizacao nao altera
os zeros. Nao ha matriz de calibracao depois do bracket.

O backend CPU trabalha em blocos de coordenadas e pode usar varios processos.
O backend CUDA usa um kernel float64 que acumula diretamente nos registradores,
sem construir uma matriz fase de tamanho grade x cutoff.

Este programa e um laboratorio numerico finito. Minimos de uma grade nao sao
uma prova sobre o limite infinito.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import multiprocessing as mp
import os
import platform
import time
from dataclasses import asdict, dataclass
from decimal import Decimal, ROUND_FLOOR, localcontext
from pathlib import Path
from typing import Any, Iterable, Sequence

import numpy as np

try:
    import cupy as cp

    HAS_CUPY = True
except Exception:
    cp = None
    HAS_CUPY = False


SCHEMA = "org.native-carry.primitive-real-rotation/v1"
DEFAULT_CAMERAS = (2,)
FLOAT_TINY = np.finfo(np.float64).tiny
INT64_MAX = np.iinfo(np.int64).max
SHOW_CHOICES = frozenset(
    {
        "score",
        "energy",
        "geometry",
        "depths",
        "radii",
        "green",
        "boundary",
        "return",
        "all",
    }
)


@dataclass(frozen=True)
class DecimalGrid:
    """Grade decimal indexada por inteiros, com rotulos reproduziveis."""

    t_min: Decimal
    t_max: Decimal
    step: Decimal
    count: int
    decimal_places: int

    @classmethod
    def from_strings(cls, t_min: str, t_max: str, step: str) -> "DecimalGrid":
        try:
            lower = Decimal(t_min)
            upper = Decimal(t_max)
            delta = Decimal(step)
        except Exception as exc:
            raise ValueError(f"grade decimal invalida: {exc}") from exc

        if not lower.is_finite() or not upper.is_finite() or not delta.is_finite():
            raise ValueError("tmin, tmax e grid precisam ser decimais finitos")
        if delta <= 0:
            raise ValueError("grid precisa ser positivo")
        if upper < lower:
            raise ValueError("tmax precisa ser maior ou igual a tmin")

        with localcontext() as ctx:
            ctx.prec = max(50, len(t_min) + len(t_max) + len(step) + 16)
            steps_decimal = ((upper - lower) / delta).to_integral_value(
                rounding=ROUND_FLOOR
            )
        count = int(steps_decimal) + 1
        if count > np.iinfo(np.int64).max:
            raise ValueError("grade grande demais para indexacao int64")

        decimal_places = max(
            0,
            -lower.as_tuple().exponent,
            -upper.as_tuple().exponent,
            -delta.as_tuple().exponent,
        )
        return cls(lower, upper, delta, count, decimal_places)

    def decimal_at(self, index: int) -> Decimal:
        if index < 0 or index >= self.count:
            raise IndexError(f"indice {index} fora de [0, {self.count})")
        return self.t_min + self.step * index

    def text_at(self, index: int) -> str:
        return f"{self.decimal_at(index):.{self.decimal_places}f}"

    def float_values(self) -> np.ndarray:
        indices = np.arange(self.count, dtype=np.float64)
        values = float(self.t_min) + float(self.step) * indices
        if values.size > 1 and np.any(values[1:] <= values[:-1]):
            raise ValueError(
                "o passo decimal e pequeno demais para produzir pontos float64 distintos"
            )
        return values

    @property
    def actual_t_max(self) -> Decimal:
        return self.decimal_at(self.count - 1)


@dataclass(frozen=True)
class CameraModel:
    """Dados float64 precomputados de uma camera primitiva."""

    camera: int
    cutoff: int
    geometry: str
    half_range: int
    seed_log: np.ndarray
    seed_amp: np.ndarray
    left_log: np.ndarray
    left_amp: np.ndarray
    center_log: np.ndarray
    center_amp: np.ndarray
    right_log: np.ndarray
    right_amp: np.ndarray
    group_kind: str
    group_values: np.ndarray
    group_labels: np.ndarray
    coordinate_count: int
    bracket_count: int
    largest_center: int

    @property
    def seed_count(self) -> int:
        return int(self.seed_log.size)

    @property
    def memory_bytes(self) -> int:
        arrays = (
            self.seed_log,
            self.seed_amp,
            self.left_log,
            self.left_amp,
            self.center_log,
            self.center_amp,
            self.right_log,
            self.right_amp,
            self.group_values,
            self.group_labels,
        )
        return int(sum(array.nbytes for array in arrays))


@dataclass(frozen=True)
class GridCandidate:
    rank: int
    camera: int
    grid_index: int
    t_decimal: str
    t_float_hex: str
    score: float
    left_score: float | None
    right_score: float | None
    scan_score: float
    log_prominence: float


@dataclass(frozen=True)
class RefinedCandidate:
    camera: int
    grid_index: int
    grid_t_decimal: str
    refined_t: float
    refined_score: float
    method: str


def parse_cameras(text: str) -> tuple[int, ...]:
    try:
        values = tuple(int(part.strip()) for part in text.split(",") if part.strip())
    except ValueError as exc:
        raise ValueError("cameras devem ser inteiros separados por virgula") from exc
    return validate_cameras(values)


def validate_cameras(values: Sequence[int]) -> tuple[int, ...]:
    cameras = tuple(int(value) for value in values)
    if not cameras:
        raise ValueError("selecione pelo menos uma camera")
    if len(set(cameras)) != len(cameras):
        raise ValueError("as cameras precisam ser distintas")
    invalid = [camera for camera in cameras if camera < 2]
    if invalid:
        raise ValueError(f"toda camera precisa ser >= 2; invalidas: {invalid}")
    return cameras


def parse_show(text: str) -> frozenset[str]:
    values = {part.strip().lower() for part in text.split(",") if part.strip()}
    if not values:
        values = {"score"}
    invalid = values - SHOW_CHOICES
    if invalid:
        raise ValueError(
            "canal desconhecido em --show: "
            + ", ".join(sorted(invalid))
            + "; escolha entre "
            + ", ".join(sorted(SHOW_CHOICES))
        )
    if "all" in values:
        values = set(SHOW_CHOICES) - {"all"}
    values.add("score")
    return frozenset(values)


def rotate_unit_axis(angle: Any, xp: Any = np) -> Any:
    """Calcula R(angle)e1 somente pelas duas coordenadas necessarias."""
    theta = xp.asarray(angle, dtype=xp.float64)
    return xp.stack((xp.cos(theta), xp.sin(theta)), axis=-1)


def real_spectral_state(t: float, size: int, xp: Any = np) -> Any:
    """Retorna psi_t(n) para 1 <= n <= size."""
    if size < 2:
        raise ValueError("size precisa ser pelo menos 2")
    if not math.isfinite(float(t)):
        raise ValueError("t precisa ser finito")
    n = xp.arange(1, size + 1, dtype=xp.float64)
    amplitudes = 1.0 / xp.sqrt(n)
    return amplitudes[:, None] * rotate_unit_axis(-float(t) * xp.log(n), xp)


def _logs_and_amplitudes(values: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    real_values = np.asarray(values, dtype=np.float64)
    return np.log(real_values), 1.0 / np.sqrt(real_values)


def _dyadic_depth(values: np.ndarray) -> np.ndarray:
    """v2(n) para um vetor int64 de inteiros positivos."""
    low_bits = np.bitwise_and(values, -values)
    return np.log2(low_bits.astype(np.float64)).astype(np.int16)


def build_camera_model(camera: int, cutoff: int) -> CameraModel:
    """Constroi a camera C2 alinhada ou a carta natural saturada."""
    camera = int(camera)
    cutoff = int(cutoff)
    validate_cameras((camera,))
    if cutoff < 1:
        raise ValueError("cutoff precisa ser pelo menos 1")

    if camera == 2:
        if cutoff > (INT64_MAX - 1) // 4:
            raise ValueError("cutoff C2 excede o intervalo int64")
        centers = 4 * np.arange(1, cutoff + 1, dtype=np.int64)
        seeds = np.array([1], dtype=np.int64)
        left = centers - 1
        right = centers + 1
        groups = _dyadic_depth(centers)
        labels = np.unique(groups)
        half_range = 1
        geometry = "c2_aligned_centers_4m"
        group_kind = "dyadic_depth"
    else:
        # Full saturated positional camera.  Odd bases have radii 1..(b-1)/2.
        # Even bases also contain the antipodal radius b/2; c-b/2 and c+b/2
        # are distinct legs even though they represent the same residue class.
        half_range = camera // 2
        if half_range < 1:
            raise ValueError("camera natural degenerada")
        if cutoff > (INT64_MAX - half_range) // camera:
            raise ValueError("cutoff da camera excede o intervalo int64")
        centers_base = camera * np.arange(1, cutoff + 1, dtype=np.int64)
        radii = np.arange(1, half_range + 1, dtype=np.int64)
        centers = np.repeat(centers_base, half_range)
        tiled_radii = np.tile(radii, cutoff)
        seeds = radii.copy()
        left = centers - tiled_radii
        right = centers + tiled_radii
        groups = tiled_radii.astype(np.int16, copy=False)
        labels = radii.astype(np.int16, copy=False)
        geometry = (
            "natural_saturated_even_antipode"
            if camera % 2 == 0
            else "natural_saturated_odd_width"
        )
        group_kind = "radius"

    seed_log, seed_amp = _logs_and_amplitudes(seeds)
    left_log, left_amp = _logs_and_amplitudes(left)
    center_log, center_amp = _logs_and_amplitudes(centers)
    right_log, right_amp = _logs_and_amplitudes(right)
    bracket_count = int(centers.size)
    coordinate_count = int(seeds.size + bracket_count)

    return CameraModel(
        camera=camera,
        cutoff=cutoff,
        geometry=geometry,
        half_range=half_range,
        seed_log=np.ascontiguousarray(seed_log),
        seed_amp=np.ascontiguousarray(seed_amp),
        left_log=np.ascontiguousarray(left_log),
        left_amp=np.ascontiguousarray(left_amp),
        center_log=np.ascontiguousarray(center_log),
        center_amp=np.ascontiguousarray(center_amp),
        right_log=np.ascontiguousarray(right_log),
        right_amp=np.ascontiguousarray(right_amp),
        group_kind=group_kind,
        group_values=np.ascontiguousarray(groups),
        group_labels=np.ascontiguousarray(labels),
        coordinate_count=coordinate_count,
        bracket_count=bracket_count,
        largest_center=int(centers[-1]),
    )


def _xy_from_log(
    times: np.ndarray, logs: np.ndarray, amplitudes: np.ndarray
) -> tuple[np.ndarray, np.ndarray]:
    angle = -times[:, None] * logs[None, :]
    return (
        amplitudes[None, :] * np.cos(angle),
        amplitudes[None, :] * np.sin(angle),
    )


def evaluate_camera_chunk_numpy(
    t_array: Sequence[float] | np.ndarray,
    model: CameraModel,
    state_block: int,
    *,
    return_balance: bool = False,
) -> np.ndarray | dict[str, np.ndarray | int]:
    """Avalia uma camera em NumPy sem materializar grade x cutoff inteira."""
    times = np.asarray(t_array, dtype=np.float64)
    if times.ndim != 1:
        raise ValueError("t_array precisa ser unidimensional")
    if state_block < 1:
        raise ValueError("state_block precisa ser positivo")

    batch = int(times.size)
    seed_x, seed_y = _xy_from_log(times, model.seed_log, model.seed_amp)
    seed_resultant = np.stack(
        (
            np.sum(seed_x, axis=1, dtype=np.float64),
            np.sum(seed_y, axis=1, dtype=np.float64),
        ),
        axis=1,
    )
    seed_energy_value = float(
        np.sum(model.seed_amp * model.seed_amp, dtype=np.float64)
    )
    seed_energy = np.full(batch, seed_energy_value, dtype=np.float64)

    bracket_resultant = np.zeros((batch, 2), dtype=np.float64)
    bracket_energy = np.zeros(batch, dtype=np.float64)
    for start in range(0, model.bracket_count, state_block):
        stop = min(start + state_block, model.bracket_count)
        sl = slice(start, stop)

        left_x, left_y = _xy_from_log(
            times, model.left_log[sl], model.left_amp[sl]
        )
        center_x, center_y = _xy_from_log(
            times, model.center_log[sl], model.center_amp[sl]
        )
        right_x, right_y = _xy_from_log(
            times, model.right_log[sl], model.right_amp[sl]
        )
        bracket_x = left_x - 2.0 * center_x + right_x
        bracket_y = left_y - 2.0 * center_y + right_y
        bracket_resultant[:, 0] += np.sum(
            bracket_x, axis=1, dtype=np.float64
        )
        bracket_resultant[:, 1] += np.sum(
            bracket_y, axis=1, dtype=np.float64
        )
        bracket_energy += np.sum(
            bracket_x * bracket_x + bracket_y * bracket_y,
            axis=1,
            dtype=np.float64,
        )

    resultant = seed_resultant + bracket_resultant
    total_energy = seed_energy + bracket_energy
    resultant_norm_sq = np.sum(resultant * resultant, axis=1, dtype=np.float64)
    denominator = float(model.coordinate_count) * total_energy
    score = resultant_norm_sq / np.maximum(denominator, FLOAT_TINY)

    if not return_balance:
        return score
    return {
        "score": score,
        "resultant": resultant,
        "resultant_norm_sq": resultant_norm_sq,
        "seed_resultant": seed_resultant,
        "bracket_resultant": bracket_resultant,
        "seed_energy": seed_energy,
        "bracket_energy": bracket_energy,
        "total_energy": total_energy,
        "coordinate_count": model.coordinate_count,
    }


_CPU_MODEL: CameraModel | None = None
_CPU_STATE_BLOCK = 0


def _init_cpu_worker(model: CameraModel, state_block: int) -> None:
    global _CPU_MODEL, _CPU_STATE_BLOCK
    _CPU_MODEL = model
    _CPU_STATE_BLOCK = int(state_block)


def _worker_scan_camera(t_chunk: np.ndarray) -> np.ndarray:
    if _CPU_MODEL is None:
        raise RuntimeError("worker CPU sem modelo inicializado")
    return np.asarray(
        evaluate_camera_chunk_numpy(
            t_chunk, _CPU_MODEL, _CPU_STATE_BLOCK, return_balance=False
        ),
        dtype=np.float64,
    )


CUDA_KERNEL_SOURCE = r"""
extern "C" __global__ void primitive_camera_r2(
    const double* __restrict__ times,
    const double* __restrict__ seed_log,
    const double* __restrict__ seed_amp,
    const double* __restrict__ left_log,
    const double* __restrict__ left_amp,
    const double* __restrict__ center_log,
    const double* __restrict__ center_amp,
    const double* __restrict__ right_log,
    const double* __restrict__ right_amp,
    double* __restrict__ out_seed_x,
    double* __restrict__ out_seed_y,
    double* __restrict__ out_bracket_x,
    double* __restrict__ out_bracket_y,
    double* __restrict__ out_bracket_energy,
    const int batch,
    const int seed_count,
    const int bracket_count
) {
    const int time_index = blockIdx.x;
    if (time_index >= batch) return;

    const double t = times[time_index];
    double seed_x_sum = 0.0;
    double seed_y_sum = 0.0;
    double bracket_x_sum = 0.0;
    double bracket_y_sum = 0.0;
    double bracket_energy_sum = 0.0;

    for (int index = threadIdx.x; index < seed_count; index += blockDim.x) {
        double sine_value, cosine_value;
        sincos(-t * seed_log[index], &sine_value, &cosine_value);
        const double amplitude = seed_amp[index];
        seed_x_sum += amplitude * cosine_value;
        seed_y_sum += amplitude * sine_value;
    }

    for (int index = threadIdx.x; index < bracket_count; index += blockDim.x) {
        double left_sine, left_cosine;
        double center_sine, center_cosine;
        double right_sine, right_cosine;
        sincos(-t * left_log[index], &left_sine, &left_cosine);
        sincos(-t * center_log[index], &center_sine, &center_cosine);
        sincos(-t * right_log[index], &right_sine, &right_cosine);

        const double bracket_x =
            left_amp[index] * left_cosine
            - 2.0 * center_amp[index] * center_cosine
            + right_amp[index] * right_cosine;
        const double bracket_y =
            left_amp[index] * left_sine
            - 2.0 * center_amp[index] * center_sine
            + right_amp[index] * right_sine;

        bracket_x_sum += bracket_x;
        bracket_y_sum += bracket_y;
        bracket_energy_sum += bracket_x * bracket_x + bracket_y * bracket_y;
    }

    for (int offset = 16; offset > 0; offset >>= 1) {
        seed_x_sum += __shfl_down_sync(0xffffffff, seed_x_sum, offset);
        seed_y_sum += __shfl_down_sync(0xffffffff, seed_y_sum, offset);
        bracket_x_sum += __shfl_down_sync(0xffffffff, bracket_x_sum, offset);
        bracket_y_sum += __shfl_down_sync(0xffffffff, bracket_y_sum, offset);
        bracket_energy_sum +=
            __shfl_down_sync(0xffffffff, bracket_energy_sum, offset);
    }

    __shared__ double shared_seed_x[32];
    __shared__ double shared_seed_y[32];
    __shared__ double shared_bracket_x[32];
    __shared__ double shared_bracket_y[32];
    __shared__ double shared_bracket_energy[32];

    const int warp = threadIdx.x >> 5;
    const int lane = threadIdx.x & 31;
    const int warp_count = (blockDim.x + 31) >> 5;
    if (lane == 0) {
        shared_seed_x[warp] = seed_x_sum;
        shared_seed_y[warp] = seed_y_sum;
        shared_bracket_x[warp] = bracket_x_sum;
        shared_bracket_y[warp] = bracket_y_sum;
        shared_bracket_energy[warp] = bracket_energy_sum;
    }
    __syncthreads();

    if (warp == 0) {
        seed_x_sum = lane < warp_count ? shared_seed_x[lane] : 0.0;
        seed_y_sum = lane < warp_count ? shared_seed_y[lane] : 0.0;
        bracket_x_sum = lane < warp_count ? shared_bracket_x[lane] : 0.0;
        bracket_y_sum = lane < warp_count ? shared_bracket_y[lane] : 0.0;
        bracket_energy_sum =
            lane < warp_count ? shared_bracket_energy[lane] : 0.0;

        for (int offset = 16; offset > 0; offset >>= 1) {
            seed_x_sum += __shfl_down_sync(0xffffffff, seed_x_sum, offset);
            seed_y_sum += __shfl_down_sync(0xffffffff, seed_y_sum, offset);
            bracket_x_sum +=
                __shfl_down_sync(0xffffffff, bracket_x_sum, offset);
            bracket_y_sum +=
                __shfl_down_sync(0xffffffff, bracket_y_sum, offset);
            bracket_energy_sum +=
                __shfl_down_sync(0xffffffff, bracket_energy_sum, offset);
        }
        if (lane == 0) {
            out_seed_x[time_index] = seed_x_sum;
            out_seed_y[time_index] = seed_y_sum;
            out_bracket_x[time_index] = bracket_x_sum;
            out_bracket_y[time_index] = bracket_y_sum;
            out_bracket_energy[time_index] = bracket_energy_sum;
        }
    }
}
"""


_CUDA_KERNEL: Any = None


def _get_cuda_kernel() -> Any:
    global _CUDA_KERNEL
    if not HAS_CUPY:
        raise RuntimeError("CuPy nao esta instalado")
    if _CUDA_KERNEL is None:
        _CUDA_KERNEL = cp.RawKernel(
            CUDA_KERNEL_SOURCE, "primitive_camera_r2", options=("--std=c++11",)
        )
    return _CUDA_KERNEL


def cuda_is_available() -> bool:
    if not HAS_CUPY:
        return False
    try:
        return bool(cp.cuda.runtime.getDeviceCount() > 0)
    except Exception:
        return False


def _camera_model_to_cuda(model: CameraModel) -> dict[str, Any]:
    if model.bracket_count > np.iinfo(np.int32).max:
        raise ValueError("camera grande demais para o indice int32 do kernel CUDA")
    return {
        "seed_log": cp.asarray(model.seed_log),
        "seed_amp": cp.asarray(model.seed_amp),
        "left_log": cp.asarray(model.left_log),
        "left_amp": cp.asarray(model.left_amp),
        "center_log": cp.asarray(model.center_log),
        "center_amp": cp.asarray(model.center_amp),
        "right_log": cp.asarray(model.right_log),
        "right_amp": cp.asarray(model.right_amp),
    }


def evaluate_camera_cuda(
    times: np.ndarray,
    model: CameraModel,
    gpu_batch: int,
    gpu_threads: int,
) -> np.ndarray:
    """Avalia uma camera por reducao direta em um kernel CUDA float64."""
    if not cuda_is_available():
        raise RuntimeError("CUDA solicitado, mas nenhum dispositivo CuPy esta disponivel")
    if gpu_batch < 1:
        raise ValueError("gpu_batch precisa ser positivo")
    if gpu_threads < 32 or gpu_threads > 1024 or gpu_threads % 32 != 0:
        raise ValueError("gpu_threads precisa ser multiplo de 32 entre 32 e 1024")

    kernel = _get_cuda_kernel()
    gpu_model = _camera_model_to_cuda(model)
    output = np.empty(times.size, dtype=np.float64)
    seed_energy = float(np.sum(model.seed_amp * model.seed_amp, dtype=np.float64))

    for start in range(0, times.size, gpu_batch):
        stop = min(start + gpu_batch, times.size)
        chunk = np.ascontiguousarray(times[start:stop], dtype=np.float64)
        batch = int(chunk.size)
        times_gpu = cp.asarray(chunk)
        seed_x = cp.zeros(batch, dtype=cp.float64)
        seed_y = cp.zeros(batch, dtype=cp.float64)
        bracket_x = cp.zeros(batch, dtype=cp.float64)
        bracket_y = cp.zeros(batch, dtype=cp.float64)
        bracket_energy = cp.zeros(batch, dtype=cp.float64)

        kernel(
            (batch,),
            (gpu_threads,),
            (
                times_gpu,
                gpu_model["seed_log"],
                gpu_model["seed_amp"],
                gpu_model["left_log"],
                gpu_model["left_amp"],
                gpu_model["center_log"],
                gpu_model["center_amp"],
                gpu_model["right_log"],
                gpu_model["right_amp"],
                seed_x,
                seed_y,
                bracket_x,
                bracket_y,
                bracket_energy,
                np.int32(batch),
                np.int32(model.seed_count),
                np.int32(model.bracket_count),
            ),
        )
        resultant_x = seed_x + bracket_x
        resultant_y = seed_y + bracket_y
        total_energy = seed_energy + bracket_energy
        scores_gpu = (
            resultant_x * resultant_x + resultant_y * resultant_y
        ) / (float(model.coordinate_count) * total_energy)
        output[start:stop] = cp.asnumpy(scores_gpu)

    cp.cuda.Stream.null.synchronize()
    return output


def resolve_backend(requested: str, workload_units: int) -> str:
    if requested == "cpu":
        return "CPU"
    if requested == "cuda":
        if not cuda_is_available():
            raise RuntimeError(
                "CUDA solicitado, mas CuPy/dispositivo CUDA nao esta disponivel"
            )
        return "CUDA"
    if workload_units >= 2_000_000 and cuda_is_available():
        return "CUDA(auto)"
    return "CPU(auto)"


def scan_camera_cpu(
    times: np.ndarray,
    model: CameraModel,
    workers: int,
    cpu_batch: int,
    state_block: int,
) -> tuple[np.ndarray, int]:
    worker_count = (
        min(8, max(1, (os.cpu_count() or 1) - 1))
        if workers <= 0
        else max(1, workers)
    )
    chunks = [
        np.ascontiguousarray(times[start : start + cpu_batch])
        for start in range(0, times.size, cpu_batch)
    ]
    if worker_count == 1 or len(chunks) <= 1:
        scores = np.concatenate(
            [
                np.asarray(
                    evaluate_camera_chunk_numpy(
                        chunk, model, state_block, return_balance=False
                    ),
                    dtype=np.float64,
                )
                for chunk in chunks
            ]
        )
        return scores, 1

    with mp.Pool(
        processes=worker_count,
        initializer=_init_cpu_worker,
        initargs=(model, state_block),
    ) as pool:
        scores = np.concatenate(pool.map(_worker_scan_camera, chunks))
    return scores, worker_count


def scan_camera(
    times: np.ndarray,
    model: CameraModel,
    backend: str,
    workers: int,
    cpu_batch: int,
    state_block: int,
    gpu_batch: int,
    gpu_threads: int,
) -> tuple[np.ndarray, str, int]:
    resolved = resolve_backend(
        backend, workload_units=int(times.size) * int(model.bracket_count)
    )
    if resolved.startswith("CUDA"):
        scores = evaluate_camera_cuda(times, model, gpu_batch, gpu_threads)
        return scores, resolved, 1
    scores, worker_count = scan_camera_cpu(
        times, model, workers, cpu_batch, state_block
    )
    return scores, resolved, worker_count


def _log_prominence_at(
    log_visibility: np.ndarray, index: int, window: int
) -> float:
    left_start = max(0, index - window)
    right_stop = min(log_visibility.size, index + window + 1)
    left = log_visibility[left_start:index]
    right = log_visibility[index + 1 : right_stop]
    if left.size == 0 or right.size == 0:
        return 0.0
    baseline = max(float(np.min(left)), float(np.min(right)))
    return max(0.0, float(log_visibility[index]) - baseline)


def detect_grid_candidates(
    scores: np.ndarray, prominence: float, prominence_window: int
) -> tuple[np.ndarray, dict[int, float]]:
    """Detecta minimos locais; prominencia e medida em -log10(score)."""
    if scores.size < 3:
        return np.empty(0, dtype=np.int64), {}
    middle = scores[1:-1]
    minima = np.flatnonzero(
        (middle <= scores[:-2]) & (middle < scores[2:])
    ).astype(np.int64) + 1
    log_visibility = -np.log10(np.maximum(scores, FLOAT_TINY))
    prominence_by_index = {
        int(index): _log_prominence_at(
            log_visibility, int(index), prominence_window
        )
        for index in minima
    }
    if prominence > 0.0:
        minima = np.asarray(
            [
                index
                for index in minima
                if prominence_by_index[int(index)] >= prominence
            ],
            dtype=np.int64,
        )
    return minima, prominence_by_index


def canonicalize_candidates_on_cpu(
    peak_indices: Iterable[int],
    times: np.ndarray,
    model: CameraModel,
    state_block: int,
    prominence_by_index: dict[int, float],
) -> list[tuple[int, float, float | None, float | None, float]]:
    """Reavalia cada vale e seus vizinhos no backend CPU float64."""
    candidates: dict[int, tuple[float, float | None, float | None, float]] = {}
    count = int(times.size)
    for raw_index in peak_indices:
        raw = int(raw_index)
        neighborhood = [
            index
            for index in (raw - 1, raw, raw + 1)
            if 0 <= index < count
        ]
        neighborhood_scores = np.asarray(
            evaluate_camera_chunk_numpy(
                times[neighborhood], model, state_block, return_balance=False
            ),
            dtype=np.float64,
        )
        index = neighborhood[int(np.argmin(neighborhood_scores))]
        witness_indices = [
            candidate
            for candidate in (index - 1, index, index + 1)
            if 0 <= candidate < count
        ]
        witness_scores = np.asarray(
            evaluate_camera_chunk_numpy(
                times[witness_indices], model, state_block, return_balance=False
            ),
            dtype=np.float64,
        )
        score_by_index = dict(zip(witness_indices, witness_scores))
        center_score = float(score_by_index[index])
        left_score = (
            float(score_by_index[index - 1])
            if index - 1 in score_by_index
            else None
        )
        right_score = (
            float(score_by_index[index + 1])
            if index + 1 in score_by_index
            else None
        )
        if left_score is not None and center_score > left_score:
            continue
        if right_score is not None and center_score > right_score:
            continue
        prominence_value = prominence_by_index.get(raw, 0.0)
        previous = candidates.get(index)
        entry = (center_score, left_score, right_score, prominence_value)
        if previous is None or center_score < previous[0]:
            candidates[index] = entry
    return [(index, *candidates[index]) for index in sorted(candidates)]


def refine_candidate_parabolic(
    index: int,
    times: np.ndarray,
    model: CameraModel,
    state_block: int,
) -> RefinedCandidate | None:
    """Polimento opcional por parabola local em log(score), seguido de reavaliacao."""
    if index <= 0 or index >= times.size - 1:
        return None
    sample_times = times[index - 1 : index + 2]
    sample_scores = np.asarray(
        evaluate_camera_chunk_numpy(
            sample_times, model, state_block, return_balance=False
        ),
        dtype=np.float64,
    )
    y0, y1, y2 = np.log(np.maximum(sample_scores, FLOAT_TINY))
    denominator = y0 - 2.0 * y1 + y2
    if not math.isfinite(float(denominator)) or denominator <= 0.0:
        return None
    spacing = float(sample_times[1] - sample_times[0])
    displacement = 0.5 * float(y0 - y2) / float(denominator) * spacing
    displacement = min(spacing, max(-spacing, displacement))
    refined_t = float(sample_times[1] + displacement)
    refined_score = float(
        np.asarray(
            evaluate_camera_chunk_numpy(
                np.array([refined_t], dtype=np.float64),
                model,
                state_block,
                return_balance=False,
            ),
            dtype=np.float64,
        )[0]
    )
    return RefinedCandidate(
        camera=model.camera,
        grid_index=int(index),
        grid_t_decimal="",
        refined_t=refined_t,
        refined_score=refined_score,
        method="local_log_parabola",
    )


def _vector_norm(vector: np.ndarray) -> float:
    return float(np.sqrt(np.dot(vector, vector)))


def _safe_cosine(first: np.ndarray, second: np.ndarray) -> float | None:
    denominator = _vector_norm(first) * _vector_norm(second)
    if denominator == 0.0:
        return None
    return float(np.dot(first, second) / denominator)


def _group_breakdown(
    t: float, model: CameraModel, state_block: int
) -> list[dict[str, Any]]:
    labels = np.asarray(model.group_labels, dtype=np.int64)
    if labels.size == 0:
        return []
    label_min = int(labels[0])
    group_count = int(labels[-1] - label_min + 1)
    counts = np.zeros(group_count, dtype=np.int64)
    resultant_x = np.zeros(group_count, dtype=np.float64)
    resultant_y = np.zeros(group_count, dtype=np.float64)
    energies = np.zeros(group_count, dtype=np.float64)
    times = np.array([t], dtype=np.float64)

    for start in range(0, model.bracket_count, state_block):
        stop = min(start + state_block, model.bracket_count)
        sl = slice(start, stop)
        left_x, left_y = _xy_from_log(
            times, model.left_log[sl], model.left_amp[sl]
        )
        center_x, center_y = _xy_from_log(
            times, model.center_log[sl], model.center_amp[sl]
        )
        right_x, right_y = _xy_from_log(
            times, model.right_log[sl], model.right_amp[sl]
        )
        bracket_x = (left_x - 2.0 * center_x + right_x)[0]
        bracket_y = (left_y - 2.0 * center_y + right_y)[0]
        group_indices = (
            model.group_values[sl].astype(np.int64, copy=False) - label_min
        )
        counts += np.bincount(group_indices, minlength=group_count)
        resultant_x += np.bincount(
            group_indices, weights=bracket_x, minlength=group_count
        )
        resultant_y += np.bincount(
            group_indices, weights=bracket_y, minlength=group_count
        )
        energies += np.bincount(
            group_indices,
            weights=bracket_x * bracket_x + bracket_y * bracket_y,
            minlength=group_count,
        )

    reports: list[dict[str, Any]] = []
    allowed = set(int(value) for value in labels)
    for offset in range(group_count):
        label = label_min + offset
        if label not in allowed or counts[offset] == 0:
            continue
        norm_sq = (
            resultant_x[offset] * resultant_x[offset]
            + resultant_y[offset] * resultant_y[offset]
        )
        visibility = (
            norm_sq / (float(counts[offset]) * energies[offset])
            if energies[offset] > 0.0
            else math.nan
        )
        reports.append(
            {
                "label": label,
                "count": int(counts[offset]),
                "resultant": [
                    float(resultant_x[offset]),
                    float(resultant_y[offset]),
                ],
                "energy": float(energies[offset]),
                "visibility": float(visibility),
            }
        )
    return reports


def evaluate_mechanism(
    t: float,
    model: CameraModel,
    state_block: int,
    *,
    include_groups: bool,
) -> dict[str, Any]:
    """Abre resultante, energia visivel e energia oculta da camera."""
    if not math.isfinite(t):
        raise ValueError("t precisa ser finito")
    balance = evaluate_camera_chunk_numpy(
        np.array([t], dtype=np.float64),
        model,
        state_block,
        return_balance=True,
    )
    resultant = np.asarray(balance["resultant"], dtype=np.float64)[0]
    seed_resultant = np.asarray(balance["seed_resultant"], dtype=np.float64)[0]
    bracket_resultant = np.asarray(
        balance["bracket_resultant"], dtype=np.float64
    )[0]
    total_energy = float(np.asarray(balance["total_energy"])[0])
    seed_energy = float(np.asarray(balance["seed_energy"])[0])
    bracket_energy = float(np.asarray(balance["bracket_energy"])[0])
    resultant_norm_sq = float(np.dot(resultant, resultant))
    visible_energy = resultant_norm_sq / float(model.coordinate_count)
    hidden_energy = max(0.0, total_energy - visible_energy)
    score = visible_energy / total_energy
    visible_angle = math.degrees(
        math.acos(math.sqrt(min(1.0, max(0.0, score))))
    )

    report: dict[str, Any] = {
        "status": "FINITE_PRIMITIVE_REAL_CAMERA_AUDIT",
        "camera": model.camera,
        "geometry": model.geometry,
        "t": float(t),
        "cutoff": model.cutoff,
        "largest_center": model.largest_center,
        "seed_count": model.seed_count,
        "bracket_count": model.bracket_count,
        "coordinate_count": model.coordinate_count,
        "resultant": resultant.tolist(),
        "resultant_norm_sq": resultant_norm_sq,
        "seed_resultant": seed_resultant.tolist(),
        "bracket_resultant": bracket_resultant.tolist(),
        "seed_energy": seed_energy,
        "bracket_energy": bracket_energy,
        "total_energy": total_energy,
        "visible_energy": visible_energy,
        "hidden_energy": hidden_energy,
        "hidden_fraction": hidden_energy / total_energy,
        "score": score,
        "dimension_free_residual": resultant_norm_sq / total_energy,
        "visible_angle_degrees": visible_angle,
        "seed_bracket_cosine": _safe_cosine(
            seed_resultant, bracket_resultant
        ),
        "seed_bracket_magnitude_ratio": (
            _vector_norm(seed_resultant) / _vector_norm(bracket_resultant)
            if _vector_norm(bracket_resultant) > 0.0
            else None
        ),
        "calibration": "none",
    }
    if include_groups:
        report["group_kind"] = model.group_kind
        report["group_reports"] = _group_breakdown(t, model, state_block)
    return report


def second_difference(values: np.ndarray) -> np.ndarray:
    if values.ndim != 2 or values.shape[1] != 2:
        raise ValueError("values precisa ter shape (N, 2)")
    return values[2:] - 2.0 * values[1:-1] + values[:-2]


def green_return(curvature: np.ndarray, size: int) -> np.ndarray:
    result = np.zeros((size, 2), dtype=np.float64)
    if curvature.size:
        result[2:] = np.cumsum(np.cumsum(curvature, axis=0), axis=0)
    return result


def affine_trace_return(a: np.ndarray, b: np.ndarray, size: int) -> np.ndarray:
    indices = np.arange(size, dtype=np.float64)[:, None]
    return a[None, :] + indices * b[None, :]


def _max_row_norm(values: np.ndarray) -> float:
    if values.size == 0:
        return 0.0
    return float(np.max(np.sqrt(np.sum(values * values, axis=-1))))


def audit_green_boundary_return(t: float, size: int) -> dict[str, Any]:
    """Audita f = G(Bf) + R(Tr f) inteiramente em R^2."""
    state = np.asarray(real_spectral_state(t, size, np), dtype=np.float64)
    curvature = second_difference(state)
    trace_position = state[0]
    trace_slope = state[1] - state[0]
    green = green_return(curvature, size)
    boundary = affine_trace_return(trace_position, trace_slope, size)
    reconstructed = green + boundary

    state_energy = float(np.sum(state * state))
    bracket_energy = float(np.sum(curvature * curvature))
    green_energy = float(np.sum(green * green))
    boundary_energy = float(np.sum(boundary * boundary))
    cross_term = float(2.0 * np.sum(green * boundary))
    reconstructed_energy = green_energy + boundary_energy + cross_term

    return {
        "status": "FINITE_PRIMITIVE_REAL_GREEN_RETURN_AUDIT",
        "identity": "f = G(Bf) + R(Tr f)",
        "t": float(t),
        "size": int(size),
        "trace": {
            "position": trace_position.tolist(),
            "slope": trace_slope.tolist(),
        },
        "endpoints": {
            "state_left": state[0].tolist(),
            "state_right": state[-1].tolist(),
            "green_right": green[-1].tolist(),
            "boundary_right": boundary[-1].tolist(),
            "reconstructed_right": reconstructed[-1].tolist(),
        },
        "errors": {
            "max_reconstruction": _max_row_norm(state - reconstructed),
            "max_green_curvature": _max_row_norm(
                second_difference(green) - curvature
            ),
            "trace_of_green": max(
                _vector_norm(green[0]), _vector_norm(green[1] - green[0])
            ),
            "max_boundary_curvature": _max_row_norm(
                second_difference(boundary)
            ),
        },
        "energy": {
            "state": state_energy,
            "bracket": bracket_energy,
            "green": green_energy,
            "boundary_return": boundary_energy,
            "polarized_cross_term": cross_term,
            "reconstructed": reconstructed_energy,
            "ledger_error": abs(state_energy - reconstructed_energy),
        },
    }


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def package_versions() -> dict[str, str | None]:
    return {
        "python": platform.python_version(),
        "numpy": np.__version__,
        "cupy": getattr(cp, "__version__", None) if HAS_CUPY else None,
    }


def _reference_camera_score(t: float, model: CameraModel) -> float:
    seed_x = 0.0
    seed_y = 0.0
    seed_energy = 0.0
    for log_value, amplitude in zip(model.seed_log, model.seed_amp):
        angle = -t * float(log_value)
        x = float(amplitude) * math.cos(angle)
        y = float(amplitude) * math.sin(angle)
        seed_x += x
        seed_y += y
        seed_energy += x * x + y * y

    bracket_x_sum = 0.0
    bracket_y_sum = 0.0
    bracket_energy = 0.0
    for index in range(model.bracket_count):
        left_angle = -t * float(model.left_log[index])
        center_angle = -t * float(model.center_log[index])
        right_angle = -t * float(model.right_log[index])
        bracket_x = (
            float(model.left_amp[index]) * math.cos(left_angle)
            - 2.0 * float(model.center_amp[index]) * math.cos(center_angle)
            + float(model.right_amp[index]) * math.cos(right_angle)
        )
        bracket_y = (
            float(model.left_amp[index]) * math.sin(left_angle)
            - 2.0 * float(model.center_amp[index]) * math.sin(center_angle)
            + float(model.right_amp[index]) * math.sin(right_angle)
        )
        bracket_x_sum += bracket_x
        bracket_y_sum += bracket_y
        bracket_energy += bracket_x * bracket_x + bracket_y * bracket_y

    resultant_x = seed_x + bracket_x_sum
    resultant_y = seed_y + bracket_y_sum
    return (
        resultant_x * resultant_x + resultant_y * resultant_y
    ) / (float(model.coordinate_count) * (seed_energy + bracket_energy))


def run_self_test(state_block: int, gpu_threads: int) -> int:
    """Testes internos pequenos da geometria, avaliador e backend opcional."""
    tests: list[str] = []

    c2 = build_camera_model(2, 64)
    c2_centers = np.rint(np.exp(c2.center_log)).astype(np.int64)
    expected_centers = 4 * np.arange(1, 65, dtype=np.int64)
    if not np.array_equal(c2_centers, expected_centers):
        raise AssertionError("centros C2 nao sao 4, 8, ..., 4M")
    if c2.seed_count != 1 or not math.isclose(float(c2.seed_amp[0]), 1.0):
        raise AssertionError("semente C2 nao e psi(1)")

    reconstructed: list[int] = []
    horizon = int(expected_centers[-1])
    maximum_depth = int(np.max(c2.group_values))
    for depth in range(2, maximum_depth + 1):
        step = 1 << depth
        odd_limit = horizon // step
        reconstructed.extend(step * odd for odd in range(1, odd_limit + 1, 2))
    if sorted(reconstructed) != expected_centers.tolist():
        raise AssertionError("particao C2 por profundidade nao fecha os M centros")
    tests.append("C2 cutoff/depth partition")

    natural = build_camera_model(9, 7)
    if natural.half_range != 4:
        raise AssertionError("semialcance incorreto para camera 9")
    if natural.bracket_count != 28 or natural.coordinate_count != 32:
        raise AssertionError("contagem incorreta da camera natural")
    tests.append("natural saturated geometry")

    sample_times = np.array([1.25, 7.0, 14.125, 30.425], dtype=np.float64)

    # C4 is not C2.  Its complete saturated chart has r=1 and the antipodal
    # r=2 channel.  C2 agrees only with the r=1 sector at the same centers 4m.
    camera_four = build_camera_model(4, 64)
    if camera_four.half_range != 2:
        raise AssertionError("C4 precisa ter raios r=1 e r=2")
    if camera_four.seed_count != 2 or camera_four.bracket_count != 128:
        raise AssertionError("contagem incorreta da camera C4 completa")
    if not np.array_equal(camera_four.group_labels, np.array([1, 2], dtype=np.int16)):
        raise AssertionError("C4 perdeu o canal antipodal r=2")
    radius_one = camera_four.group_values == 1
    if not (
        np.array_equal(c2.seed_log, camera_four.seed_log[:1])
        and np.array_equal(c2.left_log, camera_four.left_log[radius_one])
        and np.array_equal(c2.center_log, camera_four.center_log[radius_one])
        and np.array_equal(c2.right_log, camera_four.right_log[radius_one])
    ):
        raise AssertionError("C2 deve coincidir apenas com o setor r=1 da C4")
    radius_two_left = np.rint(np.exp(camera_four.left_log[~radius_one])).astype(np.int64)
    radius_two_right = np.rint(np.exp(camera_four.right_log[~radius_one])).astype(np.int64)
    if np.any(radius_two_left % 4 == 0) or np.any(radius_two_right % 4 == 0):
        raise AssertionError("as pernas r=2 da C4 nao podem ser centros C4")
    if np.any(radius_two_left % 2 != 0) or np.any(radius_two_right % 2 != 0):
        raise AssertionError("as pernas r=2 da C4 precisam ter v2 exatamente 1")
    tests.append("C4 complete even camera with antipodal r=2")
    tests.append("C2 equals only the radius-1 sector of C4")

    for camera in (2, 3, 4, 5, 9):
        model = build_camera_model(camera, 17)
        vectorized = np.asarray(
            evaluate_camera_chunk_numpy(
                sample_times, model, max(3, state_block), return_balance=False
            ),
            dtype=np.float64,
        )
        reference = np.array(
            [_reference_camera_score(float(t), model) for t in sample_times],
            dtype=np.float64,
        )
        if not np.allclose(vectorized, reference, rtol=2e-13, atol=2e-15):
            raise AssertionError(f"avaliador NumPy divergiu na camera {camera}")
        if np.any(vectorized < -2e-14) or np.any(vectorized > 1.0 + 2e-12):
            raise AssertionError(f"score fora de [0,1] na camera {camera}")
    tests.append("NumPy/reference float64 parity")

    if cuda_is_available():
        model = build_camera_model(2, 257)
        cpu_scores = np.asarray(
            evaluate_camera_chunk_numpy(
                sample_times, model, max(3, state_block), return_balance=False
            ),
            dtype=np.float64,
        )
        cuda_scores = evaluate_camera_cuda(
            sample_times, model, gpu_batch=sample_times.size, gpu_threads=gpu_threads
        )
        if not np.allclose(cpu_scores, cuda_scores, rtol=2e-11, atol=2e-14):
            raise AssertionError("backend CUDA divergiu do backend CPU")
        tests.append("CUDA/CPU float64 parity")
    else:
        tests.append("CUDA unavailable (test skipped)")

    print("SELF-TEST PRIMITIVE REAL OPERATOR")
    for entry in tests:
        print(f"  PASS  {entry}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Scanner do operador primitivo de carry em R^2 (CPU/CUDA)"
    )
    parser.add_argument("--tmin", "--t-min", dest="tmin", default="1.0")
    parser.add_argument("--tmax", "--t-max", dest="tmax", default="50.0")
    parser.add_argument(
        "--grid", "--dt", dest="grid", default="0.0005", help="passo decimal exato"
    )
    parser.add_argument(
        "--cutoff",
        "--m-cut",
        dest="cutoff",
        type=int,
        default=1024,
        help="numero M de centros por camera",
    )
    camera_group = parser.add_mutually_exclusive_group()
    camera_group.add_argument(
        "--camera",
        "--prime",
        dest="camera_flags",
        action="append",
        type=int,
        help="seleciona uma camera; repita para varrer varias separadamente",
    )
    camera_group.add_argument(
        "--cameras",
        "--primes",
        dest="cameras",
        help="cameras separadas por virgula",
    )
    parser.add_argument(
        "--threshold",
        type=float,
        default=1e-6,
        help="score maximo apos rechecagem CPU; negativo desliga o filtro",
    )
    parser.add_argument(
        "--prominence",
        type=float,
        default=0.0,
        help="prominencia minima aproximada em -log10(score)",
    )
    parser.add_argument(
        "--prominence-window",
        type=int,
        default=16,
        help="semijanela da prominencia aproximada",
    )
    parser.add_argument(
        "--backend", choices=("auto", "cpu", "cuda"), default="auto"
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=0,
        help="processos CPU; 0 escolhe automaticamente",
    )
    parser.add_argument(
        "--cpu-batch",
        type=int,
        default=16,
        help="pontos t por tarefa CPU",
    )
    parser.add_argument(
        "--state-block",
        type=int,
        default=32768,
        help="coordenadas por bloco NumPy",
    )
    parser.add_argument(
        "--gpu-batch",
        type=int,
        default=8192,
        help="pontos t por lote CUDA",
    )
    parser.add_argument(
        "--gpu-threads",
        type=int,
        default=256,
        help="threads CUDA por bloco (multiplo de 32)",
    )
    parser.add_argument(
        "--show",
        default="score",
        help=(
            "lista: score,energy,geometry,depths,radii,"
            "green,boundary,return,all"
        ),
    )
    parser.add_argument(
        "--ledger-size",
        type=int,
        default=15,
        help="tamanho do estado no diagnostico Green/return",
    )
    parser.add_argument(
        "--inspect-t",
        action="append",
        type=float,
        default=[],
        help="abre tambem uma altura explicita; pode ser repetido",
    )
    refinement = parser.add_mutually_exclusive_group()
    refinement.add_argument(
        "--refine",
        action="store_true",
        help="adiciona polimento parabolico local nao canonico",
    )
    refinement.add_argument(
        "--no-refine",
        action="store_false",
        dest="refine",
        help="mantem somente a grade (padrao)",
    )
    parser.set_defaults(refine=False)
    parser.add_argument(
        "--output", "--json-output", dest="output", type=Path, default=None
    )
    parser.add_argument("--csv", dest="csv_output", type=Path, default=None)
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="executa testes internos e encerra",
    )
    return parser


def _print_mechanism(
    report: dict[str, Any], channels: frozenset[str]
) -> None:
    if "geometry" in channels:
        print(f"    geometry            : {report['geometry']}")
        print(f"    largest center      : {report['largest_center']}")
        print(f"    seeds/brackets      : {report['seed_count']}/{report['bracket_count']}")
        print(f"    calibration         : {report['calibration']}")
    if "energy" in channels:
        print(f"    resultant R2        : {report['resultant']}")
        print(f"    resultant norm^2    : {report['resultant_norm_sq']:.12e}")
        print(f"    seed resultant      : {report['seed_resultant']}")
        print(f"    bracket resultant   : {report['bracket_resultant']}")
        print(f"    seed energy         : {report['seed_energy']:.12e}")
        print(f"    bracket energy      : {report['bracket_energy']:.12e}")
        print(f"    total energy        : {report['total_energy']:.12e}")
        print(f"    visible energy      : {report['visible_energy']:.12e}")
        print(f"    hidden energy       : {report['hidden_energy']:.12e}")
        print(f"    hidden fraction     : {report['hidden_fraction']:.12e}")
        print(f"    visible angle       : {report['visible_angle_degrees']:.9f} deg")
        print(f"    dimension-free res. : {report['dimension_free_residual']:.12e}")
        print(f"    seed/bracket cosine : {report['seed_bracket_cosine']}")
    group_kind = report.get("group_kind")
    if group_kind == "dyadic_depth" and "depths" in channels:
        print("    C2 depth channels:")
        for row in report.get("group_reports", []):
            print(
                f"      k={row['label']:<2d} count={row['count']:<8d} "
                f"energy={row['energy']:.9e} "
                f"visibility={row['visibility']:.9e} "
                f"R={row['resultant']}"
            )
    if group_kind == "radius" and "radii" in channels:
        print("    radius channels:")
        for row in report.get("group_reports", []):
            print(
                f"      r={row['label']:<2d} count={row['count']:<8d} "
                f"energy={row['energy']:.9e} "
                f"visibility={row['visibility']:.9e} "
                f"R={row['resultant']}"
            )


def _print_ledger(report: dict[str, Any], channels: frozenset[str]) -> None:
    energy = report["energy"]
    errors = report["errors"]
    if "green" in channels:
        print(f"    finite curvature E  : {energy['bracket']:.12e}")
        print(f"    Green energy        : {energy['green']:.12e}")
        print(f"    Green curvature err : {errors['max_green_curvature']:.12e}")
    if "boundary" in channels:
        print(f"    boundary energy     : {energy['boundary_return']:.12e}")
        print(f"    boundary curvature  : {errors['max_boundary_curvature']:.12e}")
        print(f"    boundary endpoint   : {report['endpoints']['boundary_right']}")
    if "return" in channels:
        print(f"    state energy        : {energy['state']:.12e}")
        print(f"    polarized cross     : {energy['polarized_cross_term']:.12e}")
        print(f"    reconstructed       : {energy['reconstructed']:.12e}")
        print(f"    ledger error        : {energy['ledger_error']:.12e}")
        print(f"    reconstruction err  : {errors['max_reconstruction']:.12e}")


def _write_csv(path: Path, camera_runs: Sequence[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "camera",
                "rank",
                "grid_index",
                "t",
                "score",
                "left_score",
                "right_score",
                "log_prominence",
                "backend",
                "cutoff",
            ],
        )
        writer.writeheader()
        for run in camera_runs:
            for candidate in run["candidates"]:
                writer.writerow(
                    {
                        "camera": candidate["camera"],
                        "rank": candidate["rank"],
                        "grid_index": candidate["grid_index"],
                        "t": candidate["t_decimal"],
                        "score": f"{candidate['score']:.17e}",
                        "left_score": candidate["left_score"],
                        "right_score": candidate["right_score"],
                        "log_prominence": candidate["log_prominence"],
                        "backend": run["runtime"]["backend"],
                        "cutoff": run["model"]["cutoff"],
                    }
                )


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)

    if args.state_block < 1:
        parser.error("state-block precisa ser positivo")
    if args.gpu_threads < 32 or args.gpu_threads > 1024 or args.gpu_threads % 32:
        parser.error("gpu-threads precisa ser multiplo de 32 entre 32 e 1024")
    if args.self_test:
        return run_self_test(args.state_block, args.gpu_threads)

    try:
        grid = DecimalGrid.from_strings(args.tmin, args.tmax, args.grid)
        selected_cameras = (
            validate_cameras(args.camera_flags)
            if args.camera_flags
            else parse_cameras(args.cameras)
            if args.cameras
            else DEFAULT_CAMERAS
        )
        show_channels = parse_show(args.show)
    except ValueError as exc:
        parser.error(str(exc))

    if args.cutoff < 1:
        parser.error("cutoff precisa ser pelo menos 1")
    if args.prominence < 0.0:
        parser.error("prominence precisa ser nao negativa")
    if args.prominence_window < 1:
        parser.error("prominence-window precisa ser positivo")
    if args.workers < 0:
        parser.error("workers precisa ser >= 0")
    if args.cpu_batch < 1:
        parser.error("cpu-batch precisa ser positivo")
    if args.gpu_batch < 1:
        parser.error("gpu-batch precisa ser positivo")
    if args.ledger_size < 2:
        parser.error("ledger-size precisa ser pelo menos 2")
    if any(not math.isfinite(value) for value in args.inspect_t):
        parser.error("inspect-t precisa ser finito")

    threshold = None if args.threshold < 0.0 else float(args.threshold)
    try:
        times = grid.float_values()
    except ValueError as exc:
        parser.error(str(exc))

    print("=" * 92)
    print(" NATIVE-CARRY PRIMITIVE OPERATOR — REAL FLOAT64 ROTATION OVER R^2")
    print("=" * 92)
    print(
        f" Interval            : {grid.decimal_at(0):.15f} "
        f"<= t <= {grid.actual_t_max:.15f}"
    )
    print(
        " Exact grid law      : "
        f"t_k = {format(grid.t_min, 'f')} + k * {format(grid.step, 'f')}"
    )
    print(f" Grid points         : {grid.count}")
    print(f" Cameras             : {selected_cameras}")
    print(f" Cutoff M            : {args.cutoff} centers per camera")
    print(" State amplitude      : n^(-1/2), fixed by quadratic carry mass")
    print(" Coordinate field     : R^2, float64")
    print(" Post-bracket map     : none")
    print(f" Requested backend    : {args.backend}")
    print(f" Diagnostics          : {', '.join(sorted(show_channels))}")
    print(f" Refinement           : {'local parabola' if args.refine else 'disabled'}")
    print("-" * 92)

    all_started = time.time()
    camera_runs: list[dict[str, Any]] = []
    need_mechanism = bool(
        {"energy", "geometry", "depths", "radii"} & show_channels
    )
    need_groups = bool({"depths", "radii"} & show_channels)
    need_ledger = bool({"green", "boundary", "return"} & show_channels)

    for camera in selected_cameras:
        model = build_camera_model(camera, args.cutoff)
        print(
            f" Camera {camera}: geometry={model.geometry}, "
            f"seeds={model.seed_count:,}, brackets={model.bracket_count:,}, "
            f"largest_center={model.largest_center:,}, "
            f"model={model.memory_bytes / (1024 ** 2):.2f} MiB"
        )
        started = time.time()
        try:
            scores, backend_name, worker_count = scan_camera(
                times,
                model,
                args.backend,
                args.workers,
                args.cpu_batch,
                args.state_block,
                args.gpu_batch,
                args.gpu_threads,
            )
        except (RuntimeError, ValueError) as exc:
            parser.error(str(exc))

        raw_indices, prominence_by_index = detect_grid_candidates(
            scores, args.prominence, args.prominence_window
        )
        cpu_candidates = canonicalize_candidates_on_cpu(
            raw_indices,
            times,
            model,
            args.state_block,
            prominence_by_index,
        )

        kept: list[GridCandidate] = []
        discarded: list[dict[str, Any]] = []
        for (
            index,
            center_score,
            left_score,
            right_score,
            prominence_value,
        ) in cpu_candidates:
            entry = {
                "grid_index": int(index),
                "t_decimal": grid.text_at(index),
                "score": center_score,
            }
            if threshold is not None and center_score > threshold:
                discarded.append({**entry, "reason": "above_threshold"})
                continue
            kept.append(
                GridCandidate(
                    rank=len(kept) + 1,
                    camera=camera,
                    grid_index=int(index),
                    t_decimal=grid.text_at(index),
                    t_float_hex=float(times[index]).hex(),
                    score=center_score,
                    left_score=left_score,
                    right_score=right_score,
                    scan_score=float(scores[index]),
                    log_prominence=float(prominence_value),
                )
            )

        refined: list[RefinedCandidate] = []
        if args.refine:
            for candidate in kept:
                result = refine_candidate_parabolic(
                    candidate.grid_index, times, model, args.state_block
                )
                if result is not None:
                    refined.append(
                        RefinedCandidate(
                            camera=result.camera,
                            grid_index=result.grid_index,
                            grid_t_decimal=candidate.t_decimal,
                            refined_t=result.refined_t,
                            refined_score=result.refined_score,
                            method=result.method,
                        )
                    )

        diagnostic_times: list[tuple[str, float, int | None]] = [
            (
                candidate.t_decimal,
                float(times[candidate.grid_index]),
                candidate.grid_index,
            )
            for candidate in kept
        ]
        diagnostic_times.extend(
            (repr(value), float(value), None) for value in args.inspect_t
        )
        diagnostics: list[dict[str, Any]] = []
        for label, value, grid_index in diagnostic_times:
            row: dict[str, Any] = {
                "t_label": label,
                "t": value,
                "grid_index": grid_index,
            }
            if need_mechanism:
                row["mechanism"] = evaluate_mechanism(
                    value,
                    model,
                    args.state_block,
                    include_groups=need_groups,
                )
            if need_ledger:
                row["green_boundary_return"] = audit_green_boundary_return(
                    value, args.ledger_size
                )
            diagnostics.append(row)

        elapsed = time.time() - started
        print(
            f"   backend={backend_name}, workers={worker_count}, "
            f"raw_valleys={len(raw_indices)}, kept={len(kept)}, "
            f"elapsed={elapsed:.3f}s"
        )
        for candidate in kept:
            print(
                f"   #{candidate.rank:02d} k={candidate.grid_index:<9d} "
                f"t={Decimal(candidate.t_decimal):.15f} "
                f"score={candidate.score:.12e} "
                f"prom={candidate.log_prominence:.4f}"
            )
            matching = next(
                (
                    row
                    for row in diagnostics
                    if row["grid_index"] == candidate.grid_index
                    and row["t_label"] == candidate.t_decimal
                ),
                None,
            )
            if matching and "mechanism" in matching:
                _print_mechanism(matching["mechanism"], show_channels)
            if matching and "green_boundary_return" in matching:
                _print_ledger(
                    matching["green_boundary_return"], show_channels
                )

        for row in diagnostics[len(kept) :]:
            print(f"   inspect t={row['t']:.15f}")
            if "mechanism" in row:
                _print_mechanism(row["mechanism"], show_channels)
            if "green_boundary_return" in row:
                _print_ledger(row["green_boundary_return"], show_channels)

        model_payload = {
            "camera": camera,
            "geometry": model.geometry,
            "cutoff": model.cutoff,
            "half_range": model.half_range,
            "seed_count": model.seed_count,
            "bracket_count": model.bracket_count,
            "coordinate_count": model.coordinate_count,
            "largest_center": model.largest_center,
            "group_kind": model.group_kind,
            "group_labels": [int(value) for value in model.group_labels],
            "memory_bytes": model.memory_bytes,
        }
        run_payload = {
            "model": model_payload,
            "selection": {
                "threshold": threshold,
                "prominence_log10": args.prominence,
                "prominence_window": args.prominence_window,
                "raw_peak_count": len(raw_indices),
                "kept_count": len(kept),
                "discarded_count": len(discarded),
                "published_scores_backend": "CPU NumPy float64",
                "refinement_requested": args.refine,
                "grid_only_is_canonical": True,
            },
            "candidates": [asdict(candidate) for candidate in kept],
            "discarded": discarded,
            "refined_noncanonical": [asdict(candidate) for candidate in refined],
            "diagnostics": diagnostics,
            "runtime": {
                "backend": backend_name,
                "workers": worker_count,
                "elapsed_seconds": elapsed,
            },
        }
        camera_runs.append(run_payload)
        print("-" * 92)

    total_elapsed = time.time() - all_started
    payload: dict[str, Any] = {
        "schema": SCHEMA,
        "status": "FINITE_PRIMITIVE_REAL_GRID_AUDIT",
        "operator": {
            "state": "n^(-1/2) * (cos(-t log n), sin(-t log n))",
            "camera_2": "seed psi(1) plus brackets at centers 4,8,...,4M",
            "camera_ge_3": "saturated centered brackets of natural width",
            "bracket": "psi(c-r) - 2 psi(c) + psi(c+r)",
            "post_bracket_map": "none",
            "coordinate_field": "R^2",
            "score": "norm(sum_e z_e)^2 / (N * sum_e norm(z_e)^2)",
        },
        "grid": {
            "tmin": format(grid.t_min, "f"),
            "requested_tmax": format(grid.t_max, "f"),
            "actual_tmax": format(grid.actual_t_max, "f"),
            "spacing": format(grid.step, "f"),
            "count": grid.count,
            "law": "t_k = tmin + k * grid",
        },
        "cameras": camera_runs,
        "diagnostic_channels": sorted(show_channels),
        "runtime": {
            "elapsed_seconds": total_elapsed,
            "versions": package_versions(),
            "script_sha256": file_sha256(Path(__file__).resolve()),
        },
    }

    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(
            json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False)
            + "\n",
            encoding="utf-8",
        )
        print(f"JSON written to {args.output}")
    if args.csv_output is not None:
        _write_csv(args.csv_output, camera_runs)
        print(f"CSV written to {args.csv_output}")

    print(
        f"Completed {len(selected_cameras)} camera(s) in {total_elapsed:.3f}s"
    )
    print("=" * 92)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
