#!/usr/bin/env python3
"""Guarded branch-and-bound audit of transverse carry coercivity.

For a finite native carry readout C_M, define

    Chi_M(sigma,t) = C_M [n^(-sigma) exp(-i t log n)],
    E_M(sigma,t)   = ||Chi_M(sigma,t)||^2,
    delta          = sigma-1/2.

The target coefficient on a compact rectangle K is

    c_(M,K) = inf_{(sigma,t) in K, delta != 0} E_M(sigma,t)/delta^2.

Equivalently, c is admissible when

    F_(M,c)(sigma,t) = E_M(sigma,t)-c delta^2 >= 0

throughout K.  This laboratory avoids division by delta^2 in the certificate.
Each rectangular cell receives two analytic lower bounds:

1. a Hessian lower bound, with Hessian variation controlled by explicit third-
   derivative majorants;
2. a direct norm-Taylor lower bound for ||Chi_M||.

The derivative majorants are finite sums determined by the fixed primitive
camera matrix.  If C[:,n] is the n-th column, then for every mixed derivative
of total order k on sigma >= sigma_min,

    ||D^k Chi_M|| <=
      || (sum_n |C_jn| n^(-sigma_min) (log n)^k)_j ||_2.

The cell test is therefore analytic, not a sample-grid test.  Center jets are
computed in float64 and protected by an explicit floating guard; witnesses are
independently reevaluated by row-wise long-double summation.  Accordingly the
output is a guarded validated-numerics certificate, not a formal interval or
proof-assistant theorem.

At a critical-time valley, write

    v=partial_sigma Chi,  w=partial_sigma^2 Chi,
    kappa=||v||^2,
    a=Re <Chi,w>,
    b=Re <Chi,i w>,
    D=kappa^2-a^2-b^2.

Then exactly

    Hess(E)=2 [[kappa+a,b],[b,kappa-a]],
    det Hess(E)=4D,
    t_M'(1/2)=-b/(kappa-a),
    L_M''(1/2)=2D/(kappa-a)

for an interior temporal minimizer with kappa-a>0.  The finite residual also
creates a microscopic minimizer of E/delta^2 at delta=O(||Chi||).  The audit
reports this layer separately from the fixed-delta cutoff behavior.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import asdict, dataclass
import heapq
import json
import math
from pathlib import Path
import time
from typing import Any, Iterable, Sequence

import numpy as np
from scipy.optimize import minimize_scalar

import native_carry_sigma_deformed_operator_lab as sigma_lab
import native_carry_primitive_real_operator_all_bases_fixed as native


DEFAULT_WINDOWS = (
    (13.8, 14.4),
    (20.7, 21.3),
    (24.7, 25.3),
    (30.1, 30.8),
    (32.6, 33.2),
    (37.2, 38.0),
)


@dataclass(frozen=True)
class Cell:
    sigma: float
    time: float
    sigma_radius: float
    time_radius: float
    depth: int = 0


@dataclass(frozen=True)
class CellBound:
    lower_bound: float
    raw_lower_bound: float
    hessian_lower_bound: float
    norm_taylor_lower_bound: float
    floating_guard: float
    center_f: float
    center_energy: float
    minimum_hessian_eigenvalue_bound: float
    third_derivative_bound: float


@dataclass(frozen=True)
class BranchResult:
    status: str
    coefficient: float
    certified: bool
    cells_created: int
    certified_leaf_count: int
    maximum_depth: int
    elapsed_seconds: float
    smallest_certified_cell_lower_bound: float | None
    unresolved_cell: dict[str, Any] | None
    counterexample: dict[str, Any] | None


def parse_ints(text: str, minimum: int = 1) -> tuple[int, ...]:
    values = tuple(sorted({int(part.strip()) for part in text.split(",") if part.strip()}))
    if not values or any(value < minimum for value in values):
        raise ValueError(f"provide integers >= {minimum}")
    return values


def parse_windows(text: str) -> tuple[tuple[float, float], ...]:
    rows: list[tuple[float, float]] = []
    for chunk in text.split(","):
        left_text, right_text = chunk.strip().split(":")
        left, right = float(left_text), float(right_text)
        if not (math.isfinite(left) and math.isfinite(right) and left < right):
            raise ValueError(f"invalid window: {chunk!r}")
        rows.append((left, right))
    if not rows:
        raise ValueError("provide at least one window")
    return tuple(rows)


def parse_certificate_map(text: str) -> dict[int, float]:
    if not text.strip():
        return {}
    output: dict[int, float] = {}
    for chunk in text.split(","):
        cutoff_text, coefficient_text = chunk.strip().split(":")
        cutoff, coefficient = int(cutoff_text), float(coefficient_text)
        if cutoff < 1 or not math.isfinite(coefficient) or coefficient < 0.0:
            raise ValueError(f"invalid cutoff:coefficient pair {chunk!r}")
        output[cutoff] = coefficient
    return output


class TransverseSystem:
    """Fixed finite native readout plus analytic sigma/time jets."""

    def __init__(self, cameras: Sequence[int], cutoff: int):
        built = sigma_lab.build_native_matrix(tuple(cameras), int(cutoff))
        self.cameras = tuple(int(value) for value in cameras)
        self.cutoff = int(cutoff)
        self.camera = np.asarray(built["camera"], dtype=np.float64)
        self.numbers = np.asarray(built["numbers"], dtype=np.float64)
        self.logarithms = np.asarray(built["logarithms"], dtype=np.float64)
        self.size = int(built["size"])
        self.abs_camera = np.abs(self.camera)
        self.log_powers = np.vstack(
            [self.logarithms**order for order in range(6)]
        )
        self._majorant_cache: dict[tuple[float, int], np.ndarray] = {}

    def moments(self, sigma: float, time_value: float, maximum_order: int = 4) -> np.ndarray:
        if maximum_order < 0 or maximum_order > 5:
            raise ValueError("maximum_order must lie in [0,5]")
        state = self.numbers ** (-float(sigma)) * np.exp(
            -1j * float(time_value) * self.logarithms
        )
        # columns are M_k=C[(log n)^k n^-sigma exp(-it log n)]
        return self.camera @ (
            state[None, :] * self.log_powers[: maximum_order + 1]
        ).T

    def derivative_majorants(self, sigma_minimum: float, maximum_order: int = 4) -> np.ndarray:
        key = (float(sigma_minimum), int(maximum_order))
        cached = self._majorant_cache.get(key)
        if cached is not None:
            return cached
        amplitudes = self.numbers ** (-float(sigma_minimum))
        # For each order, first bound every camera row by its absolute sum,
        # then take the Euclidean norm across camera outputs.
        row_bounds = self.abs_camera @ (
            amplitudes[None, :] * self.log_powers[: maximum_order + 1]
        ).T
        bounds = np.linalg.norm(row_bounds, axis=0)
        self._majorant_cache[key] = bounds
        return bounds

    def energy_jet(
        self, sigma: float, time_value: float, coefficient: float = 0.0
    ) -> dict[str, Any]:
        moments = self.moments(sigma, time_value, maximum_order=4)
        chi = moments[:, 0]
        m1 = moments[:, 1]
        m2 = moments[:, 2]
        sigma_tangent = -m1
        time_tangent = 1j * sigma_tangent
        sigma_sigma = m2
        sigma_time = 1j * m2
        time_time = -m2

        energy = float(np.vdot(chi, chi).real)
        delta = float(sigma - 0.5)
        gradient_energy = np.asarray(
            [
                2.0 * float(np.vdot(chi, sigma_tangent).real),
                2.0 * float(np.vdot(chi, time_tangent).real),
            ],
            dtype=np.float64,
        )
        hessian_energy = np.asarray(
            [
                [
                    2.0
                    * float(
                        (
                            np.vdot(sigma_tangent, sigma_tangent)
                            + np.vdot(chi, sigma_sigma)
                        ).real
                    ),
                    2.0
                    * float(
                        (
                            np.vdot(sigma_tangent, time_tangent)
                            + np.vdot(chi, sigma_time)
                        ).real
                    ),
                ],
                [
                    0.0,
                    2.0
                    * float(
                        (
                            np.vdot(time_tangent, time_tangent)
                            + np.vdot(chi, time_time)
                        ).real
                    ),
                ],
            ],
            dtype=np.float64,
        )
        hessian_energy[1, 0] = hessian_energy[0, 1]

        f_value = energy - coefficient * delta * delta
        f_gradient = gradient_energy.copy()
        f_gradient[0] -= 2.0 * coefficient * delta
        f_hessian = hessian_energy.copy()
        f_hessian[0, 0] -= 2.0 * coefficient

        kappa = float(np.vdot(sigma_tangent, sigma_tangent).real)
        chi_w = np.vdot(chi, m2)
        a_value = float(chi_w.real)
        b_value = float((1j * chi_w).real)
        discriminant = kappa * kappa - a_value * a_value - b_value * b_value
        temporal_curvature_half = kappa - a_value
        if temporal_curvature_half > 0.0:
            optimal_time_slope = -b_value / temporal_curvature_half
            envelope_second = 2.0 * discriminant / temporal_curvature_half
            local_envelope_coefficient = discriminant / temporal_curvature_half
        else:
            optimal_time_slope = None
            envelope_second = None
            local_envelope_coefficient = None

        return {
            "sigma": float(sigma),
            "time": float(time_value),
            "delta": delta,
            "chi": chi,
            "moments": moments,
            "moment_norms": np.linalg.norm(moments, axis=0),
            "energy": energy,
            "energy_gradient": gradient_energy,
            "energy_hessian": hessian_energy,
            "F": f_value,
            "F_gradient": f_gradient,
            "F_hessian": f_hessian,
            "kappa": kappa,
            "a": a_value,
            "b": b_value,
            "discriminant": discriminant,
            "hessian_trace": float(np.trace(hessian_energy)),
            "hessian_determinant": float(np.linalg.det(hessian_energy)),
            "hessian_eigenvalues": np.linalg.eigvalsh(hessian_energy),
            "temporal_curvature_half": temporal_curvature_half,
            "optimal_time_slope": optimal_time_slope,
            "envelope_second_derivative": envelope_second,
            "local_envelope_coefficient": local_envelope_coefficient,
            "cauchy_riemann_error": float(
                np.linalg.norm(time_tangent - 1j * sigma_tangent)
            ),
        }

    def energy(self, sigma: float, time_value: float) -> float:
        chi = self.moments(sigma, time_value, maximum_order=0)[:, 0]
        return float(np.vdot(chi, chi).real)

    def longdouble_energy(self, sigma: float, time_value: float) -> float:
        """Independent row-wise extended-precision evaluation."""
        numbers = np.arange(1, self.size + 1, dtype=np.longdouble)
        logs = np.log(numbers)
        amplitude = np.exp(-np.longdouble(sigma) * logs)
        angle = -np.longdouble(time_value) * logs
        real_state = amplitude * np.cos(angle)
        imaginary_state = amplitude * np.sin(angle)
        total = np.longdouble(0.0)
        for row in self.camera.astype(np.longdouble):
            real_value = np.sum(row * real_state, dtype=np.longdouble)
            imaginary_value = np.sum(row * imaginary_state, dtype=np.longdouble)
            total += real_value * real_value + imaginary_value * imaginary_value
        return float(total)


def scalar_quadratic_minimum(gradient: float, curvature: float, radius: float) -> float:
    if curvature > 0.0:
        displacement = min(radius, max(-radius, -gradient / curvature))
        return gradient * displacement + 0.5 * curvature * displacement**2
    left = -gradient * radius + 0.5 * curvature * radius**2
    right = gradient * radius + 0.5 * curvature * radius**2
    return min(left, right)


def cell_lower_bound(
    system: TransverseSystem,
    cell: Cell,
    coefficient: float,
    guard_multiplier: float,
) -> CellBound:
    if coefficient < 0.0:
        raise ValueError("coefficient must be nonnegative")
    jet = system.energy_jet(cell.sigma, cell.time, coefficient)
    moment_norms = np.asarray(jet["moment_norms"], dtype=np.float64)
    radius_l1 = cell.sigma_radius + cell.time_radius
    global_bounds = system.derivative_majorants(
        cell.sigma - cell.sigma_radius, maximum_order=4
    )
    local_bounds = np.asarray(
        [
            moment_norms[order] + global_bounds[order + 1] * radius_l1
            for order in range(4)
        ],
        dtype=np.float64,
    )

    # Every mixed third derivative of E is bounded by this expression.
    third_bound = float(
        2.0 * local_bounds[0] * local_bounds[3]
        + 6.0 * local_bounds[1] * local_bounds[2]
    )
    center_hessian = np.asarray(jet["F_hessian"], dtype=np.float64)
    center_minimum_eigenvalue = float(np.linalg.eigvalsh(center_hessian)[0])
    # Every Hessian entry varies by at most third_bound*radius_l1.
    # A 2x2 matrix with entries bounded by q has operator norm <=2q.
    hessian_floor = center_minimum_eigenvalue - 2.0 * third_bound * radius_l1
    gradient = np.asarray(jet["F_gradient"], dtype=np.float64)
    quadratic_remainder_minimum = scalar_quadratic_minimum(
        float(gradient[0]), hessian_floor, cell.sigma_radius
    ) + scalar_quadratic_minimum(
        float(gradient[1]), hessian_floor, cell.time_radius
    )
    hessian_lower = float(jet["F"] + quadratic_remainder_minimum)

    # Independent direct lower bound on ||Chi|| from its center jet.
    chi_lower = max(
        0.0,
        float(moment_norms[0])
        - float(moment_norms[1]) * radius_l1
        - 0.5 * float(local_bounds[2]) * radius_l1**2,
    )
    delta_center = cell.sigma - 0.5
    maximum_delta = max(
        abs(delta_center - cell.sigma_radius),
        abs(delta_center + cell.sigma_radius),
    )
    norm_lower = chi_lower**2 - coefficient * maximum_delta**2
    raw_lower = max(hessian_lower, norm_lower)

    scale = (
        1.0
        + abs(float(jet["F"]))
        + float(np.sum(np.abs(gradient))) * radius_l1
        + abs(hessian_floor)
        * (cell.sigma_radius**2 + cell.time_radius**2)
        + third_bound * radius_l1**3
    )
    floating_guard = (
        float(guard_multiplier) * np.finfo(np.float64).eps * scale
    )
    guarded_lower = float(np.nextafter(raw_lower - floating_guard, -np.inf))
    return CellBound(
        lower_bound=guarded_lower,
        raw_lower_bound=float(raw_lower),
        hessian_lower_bound=hessian_lower,
        norm_taylor_lower_bound=float(norm_lower),
        floating_guard=float(floating_guard),
        center_f=float(jet["F"]),
        center_energy=float(jet["energy"]),
        minimum_hessian_eigenvalue_bound=float(hessian_floor),
        third_derivative_bound=third_bound,
    )


def split_cell(cell: Cell) -> tuple[Cell, Cell]:
    # sigma and t have the same analytic derivative scale because
    # partial_t Chi=i partial_sigma Chi.  Split the larger coordinate radius.
    if cell.time_radius >= cell.sigma_radius:
        child_radius = 0.5 * cell.time_radius
        return (
            Cell(
                cell.sigma,
                cell.time - child_radius,
                cell.sigma_radius,
                child_radius,
                cell.depth + 1,
            ),
            Cell(
                cell.sigma,
                cell.time + child_radius,
                cell.sigma_radius,
                child_radius,
                cell.depth + 1,
            ),
        )
    child_radius = 0.5 * cell.sigma_radius
    return (
        Cell(
            cell.sigma - child_radius,
            cell.time,
            child_radius,
            cell.time_radius,
            cell.depth + 1,
        ),
        Cell(
            cell.sigma + child_radius,
            cell.time,
            child_radius,
            cell.time_radius,
            cell.depth + 1,
        ),
    )


def initial_cells(
    sigma_minimum: float,
    sigma_maximum: float,
    time_minimum: float,
    time_maximum: float,
    sigma_bins: int,
    time_bins: int,
) -> Iterable[Cell]:
    sigma_edges = np.linspace(sigma_minimum, sigma_maximum, sigma_bins + 1)
    time_edges = np.linspace(time_minimum, time_maximum, time_bins + 1)
    for sigma_left, sigma_right in zip(sigma_edges[:-1], sigma_edges[1:]):
        for time_left, time_right in zip(time_edges[:-1], time_edges[1:]):
            yield Cell(
                sigma=0.5 * (sigma_left + sigma_right),
                time=0.5 * (time_left + time_right),
                sigma_radius=0.5 * (sigma_right - sigma_left),
                time_radius=0.5 * (time_right - time_left),
            )


def branch_and_bound(
    system: TransverseSystem,
    coefficient: float,
    sigma_range: tuple[float, float],
    time_range: tuple[float, float],
    *,
    sigma_bins: int = 8,
    time_bins: int = 120,
    maximum_cells: int = 500_000,
    minimum_sigma_radius: float = 5.0e-10,
    minimum_time_radius: float = 8.0e-10,
    guard_multiplier: float = 4096.0,
) -> BranchResult:
    start = time.perf_counter()
    queue: list[tuple[float, int, Cell, CellBound]] = []
    identifier = 0
    for cell in initial_cells(
        sigma_range[0],
        sigma_range[1],
        time_range[0],
        time_range[1],
        sigma_bins,
        time_bins,
    ):
        bound = cell_lower_bound(system, cell, coefficient, guard_multiplier)
        heapq.heappush(queue, (bound.lower_bound, identifier, cell, bound))
        identifier += 1

    certified_leaves = 0
    maximum_depth = 0
    smallest_certified: float | None = None
    while queue:
        _, _, cell, bound = heapq.heappop(queue)
        maximum_depth = max(maximum_depth, cell.depth)
        if bound.lower_bound >= 0.0:
            certified_leaves += 1
            smallest_certified = (
                bound.lower_bound
                if smallest_certified is None
                else min(smallest_certified, bound.lower_bound)
            )
            continue

        # A negative center value is already a concrete counterexample to the
        # proposed coefficient; no cell enclosure is needed for that direction.
        if bound.center_f < -bound.floating_guard:
            jet = system.energy_jet(cell.sigma, cell.time, coefficient)
            extended_energy = system.longdouble_energy(cell.sigma, cell.time)
            delta = cell.sigma - 0.5
            counterexample = {
                "sigma": cell.sigma,
                "time": cell.time,
                "delta": delta,
                "float64_energy": float(jet["energy"]),
                "longdouble_energy": extended_energy,
                "energy_cross_precision_absolute_error": abs(
                    extended_energy - float(jet["energy"])
                ),
                "quotient": extended_energy / (delta * delta),
                "F_float64": float(jet["F"]),
                "cell": asdict(cell),
                "cell_bound": asdict(bound),
            }
            return BranchResult(
                status="COUNTEREXAMPLE_FOUND",
                coefficient=float(coefficient),
                certified=False,
                cells_created=identifier,
                certified_leaf_count=certified_leaves,
                maximum_depth=maximum_depth,
                elapsed_seconds=time.perf_counter() - start,
                smallest_certified_cell_lower_bound=smallest_certified,
                unresolved_cell=None,
                counterexample=counterexample,
            )

        if identifier >= maximum_cells or (
            cell.sigma_radius <= minimum_sigma_radius
            and cell.time_radius <= minimum_time_radius
        ):
            return BranchResult(
                status="RESOURCE_LIMIT_UNRESOLVED",
                coefficient=float(coefficient),
                certified=False,
                cells_created=identifier,
                certified_leaf_count=certified_leaves,
                maximum_depth=maximum_depth,
                elapsed_seconds=time.perf_counter() - start,
                smallest_certified_cell_lower_bound=smallest_certified,
                unresolved_cell={
                    "cell": asdict(cell),
                    "cell_bound": asdict(bound),
                    "remaining_queue_size": len(queue),
                },
                counterexample=None,
            )

        for child in split_cell(cell):
            child_bound = cell_lower_bound(
                system, child, coefficient, guard_multiplier
            )
            heapq.heappush(
                queue,
                (child_bound.lower_bound, identifier, child, child_bound),
            )
            identifier += 1

    return BranchResult(
        status="CERTIFIED_NONNEGATIVE_ON_COMPACT",
        coefficient=float(coefficient),
        certified=True,
        cells_created=identifier,
        certified_leaf_count=certified_leaves,
        maximum_depth=maximum_depth,
        elapsed_seconds=time.perf_counter() - start,
        smallest_certified_cell_lower_bound=smallest_certified,
        unresolved_cell=None,
        counterexample=None,
    )


def critical_valley(
    system: TransverseSystem, window: tuple[float, float], index: int
) -> dict[str, Any]:
    result = minimize_scalar(
        lambda value: system.energy(0.5, float(value)),
        bounds=window,
        method="bounded",
        options={"xatol": 5.0e-14, "maxiter": 700},
    )
    time_value = float(result.x)
    jet = system.energy_jet(0.5, time_value)
    energy = float(jet["energy"])
    sigma_gradient = float(jet["energy_gradient"][0])
    local_coefficient = jet["local_envelope_coefficient"]
    if energy > 0.0 and sigma_gradient != 0.0 and local_coefficient is not None:
        predicted_delta = -2.0 * energy / sigma_gradient
        predicted_ratio = float(
            local_coefficient - sigma_gradient**2 / (4.0 * energy)
        )
    else:
        predicted_delta = None
        predicted_ratio = local_coefficient
    return {
        "valley_index": index,
        "window": list(window),
        "critical_time": time_value,
        "critical_energy": energy,
        "critical_resultant_norm": math.sqrt(max(0.0, energy)),
        "sigma_gradient": sigma_gradient,
        "kappa": float(jet["kappa"]),
        "a": float(jet["a"]),
        "b": float(jet["b"]),
        "discriminant": float(jet["discriminant"]),
        "hessian_trace": float(jet["hessian_trace"]),
        "hessian_determinant": float(jet["hessian_determinant"]),
        "hessian_eigenvalues": np.asarray(
            jet["hessian_eigenvalues"], dtype=float
        ).tolist(),
        "temporal_curvature_half": float(jet["temporal_curvature_half"]),
        "optimal_time_slope": jet["optimal_time_slope"],
        "envelope_second_derivative": jet["envelope_second_derivative"],
        "local_envelope_coefficient": local_coefficient,
        "predicted_microscopic_delta": predicted_delta,
        "predicted_microscopic_quotient": predicted_ratio,
        "cauchy_riemann_error": float(jet["cauchy_riemann_error"]),
    }


def refine_microscopic_witness(
    system: TransverseSystem,
    valley: dict[str, Any],
    delta_minimum: float = 1.0e-13,
    delta_maximum: float = 1.0e-2,
) -> dict[str, Any] | None:
    predicted = valley["predicted_microscopic_delta"]
    if predicted is None or predicted == 0.0 or not math.isfinite(float(predicted)):
        return None
    sign = -1.0 if predicted < 0.0 else 1.0
    center_log_delta = math.log(
        min(delta_maximum, max(delta_minimum, abs(float(predicted))))
    )
    lower_log = max(math.log(delta_minimum), center_log_delta - 3.0)
    upper_log = min(math.log(delta_maximum), center_log_delta + 3.0)
    time_center = float(valley["critical_time"])
    window_left, window_right = map(float, valley["window"])
    local_time_window = (
        max(window_left, time_center - 0.02),
        min(window_right, time_center + 0.02),
    )
    cache: dict[float, tuple[float, float, float]] = {}

    def quotient_at_log_delta(log_delta: float) -> float:
        key = float(log_delta)
        cached = cache.get(key)
        if cached is not None:
            return cached[0]
        delta = sign * math.exp(key)
        sigma = 0.5 + delta
        temporal = minimize_scalar(
            lambda value: system.energy(sigma, float(value)),
            bounds=local_time_window,
            method="bounded",
            options={"xatol": 5.0e-14, "maxiter": 500},
        )
        energy = float(temporal.fun)
        quotient = energy / (delta * delta)
        cache[key] = (quotient, float(temporal.x), energy)
        return quotient

    result = minimize_scalar(
        quotient_at_log_delta,
        bounds=(lower_log, upper_log),
        method="bounded",
        options={"xatol": 2.0e-10, "maxiter": 120},
    )
    log_delta = float(result.x)
    quotient = quotient_at_log_delta(log_delta)
    _, time_value, float64_energy = cache[log_delta]
    delta = sign * math.exp(log_delta)
    sigma = 0.5 + delta
    longdouble_energy = system.longdouble_energy(sigma, time_value)
    return {
        "sigma": sigma,
        "time": time_value,
        "delta": delta,
        "float64_energy": float64_energy,
        "longdouble_energy": longdouble_energy,
        "float64_quotient": quotient,
        "longdouble_quotient": longdouble_energy / (delta * delta),
        "energy_cross_precision_absolute_error": abs(
            longdouble_energy - float64_energy
        ),
        "optimizer_success": bool(result.success),
        "optimizer_evaluations": int(result.nfev),
        "source_valley_index": int(valley["valley_index"]),
    }


def one_cutoff_survey(
    cameras: Sequence[int],
    cutoff: int,
    windows: Sequence[tuple[float, float]],
) -> tuple[TransverseSystem, dict[str, Any]]:
    system = TransverseSystem(cameras, cutoff)
    valleys = [
        critical_valley(system, window, index)
        for index, window in enumerate(windows, start=1)
    ]
    predicted_candidates = [
        row
        for row in valleys
        if row["predicted_microscopic_quotient"] is not None
        and math.isfinite(float(row["predicted_microscopic_quotient"]))
    ]
    controlling = min(
        predicted_candidates,
        key=lambda row: float(row["predicted_microscopic_quotient"]),
    )
    witness = refine_microscopic_witness(system, controlling)
    return system, {
        "cutoff": int(cutoff),
        "ambient_dimension": system.size,
        "camera_rank": int(np.linalg.matrix_rank(system.camera, tol=1.0e-11)),
        "valleys": valleys,
        "controlling_predicted_valley_index": int(controlling["valley_index"]),
        "microscopic_upper_witness": witness,
    }


def flatten_rows(report: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for item in report["cutoff_rows"]:
        witness = item.get("microscopic_upper_witness") or {}
        certificate = item.get("coercivity_certificate") or {}
        rows.append(
            {
                "cutoff": item["cutoff"],
                "ambient_dimension": item["ambient_dimension"],
                "certified_lower_coefficient": (
                    certificate.get("coefficient")
                    if certificate.get("certified")
                    else None
                ),
                "certificate_status": certificate.get("status"),
                "certificate_cells_created": certificate.get("cells_created"),
                "certificate_elapsed_seconds": certificate.get("elapsed_seconds"),
                "upper_witness_quotient": witness.get("longdouble_quotient"),
                "upper_witness_sigma": witness.get("sigma"),
                "upper_witness_time": witness.get("time"),
                "upper_witness_delta": witness.get("delta"),
                "controlling_valley_index": item.get(
                    "controlling_predicted_valley_index"
                ),
            }
        )
    return rows


def write_csv(path: Path, rows: Sequence[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def run_lab(args: argparse.Namespace) -> dict[str, Any]:
    cameras = native.parse_cameras(args.cameras)
    cutoffs = parse_ints(args.cutoffs)
    windows = parse_windows(args.windows)
    certificates = parse_certificate_map(args.certify)
    if args.sigma_max <= args.sigma_min:
        raise ValueError("sigma-max must exceed sigma-min")
    if args.t_max <= args.t_min:
        raise ValueError("t-max must exceed t-min")
    if not (args.sigma_min < 0.5 < args.sigma_max):
        raise ValueError("the sigma compact must contain 1/2 in its interior")

    cutoff_rows: list[dict[str, Any]] = []
    for cutoff in cutoffs:
        system, row = one_cutoff_survey(cameras, cutoff, windows)
        if cutoff in certificates:
            result = branch_and_bound(
                system,
                certificates[cutoff],
                (args.sigma_min, args.sigma_max),
                (args.t_min, args.t_max),
                sigma_bins=args.sigma_bins,
                time_bins=args.time_bins,
                maximum_cells=args.maximum_cells,
                minimum_sigma_radius=args.minimum_sigma_radius,
                minimum_time_radius=args.minimum_time_radius,
                guard_multiplier=args.guard_multiplier,
            )
            row["coercivity_certificate"] = asdict(result)
        cutoff_rows.append(row)

    certified = [
        row
        for row in cutoff_rows
        if row.get("coercivity_certificate", {}).get("certified")
    ]
    witness_rows = [
        row for row in cutoff_rows if row.get("microscopic_upper_witness")
    ]
    minimum_certified = min(
        (
            float(row["coercivity_certificate"]["coefficient"])
            for row in certified
        ),
        default=None,
    )
    minimum_upper_witness = min(
        (
            float(row["microscopic_upper_witness"]["longdouble_quotient"])
            for row in witness_rows
        ),
        default=None,
    )
    return {
        "schema": "org.native-carry.transverse-coercivity-certificate/v1",
        "status": "GUARDED_TRANSVERSE_COERCIVITY_INTERVALS_AUDITED",
        "configuration": {
            "cameras": list(cameras),
            "cutoffs": list(cutoffs),
            "sigma_compact": [args.sigma_min, args.sigma_max],
            "time_compact": [args.t_min, args.t_max],
            "valley_windows": [list(window) for window in windows],
            "requested_certificate_coefficients": {
                str(key): value for key, value in certificates.items()
            },
            "branch": {
                "sigma_bins": args.sigma_bins,
                "time_bins": args.time_bins,
                "maximum_cells": args.maximum_cells,
                "minimum_sigma_radius": args.minimum_sigma_radius,
                "minimum_time_radius": args.minimum_time_radius,
                "guard_multiplier": args.guard_multiplier,
            },
        },
        "target": {
            "energy": "E_M(sigma,t)=||C_M[n^(-sigma) exp(-it log n)]||^2",
            "quotient": "E_M(sigma,t)/(sigma-1/2)^2",
            "smooth_test": "F_M,c=E_M-c(sigma-1/2)^2",
            "coercivity_number": (
                "c_M,K=inf_(sigma,t in K,sigma!=1/2) "
                "E_M(sigma,t)/(sigma-1/2)^2"
            ),
        },
        "analytic_cell_certificate": {
            "derivative_bound": (
                "mixed order-k derivatives are bounded by finite absolute "
                "camera sums weighted by n^(-sigma_min)(log n)^k"
            ),
            "third_energy_bound": "2 B0 B3+6 B1 B2",
            "hessian_transport": (
                "lambda_min Hess(F) on a cell is bounded from the center "
                "Hessian and the third-derivative majorant"
            ),
            "second_bound": (
                "a direct Taylor lower bound on ||Chi|| is combined with the "
                "Hessian bound; the stronger lower bound certifies the cell"
            ),
            "numerical_class": (
                "float64 center jets with explicit guard and independent "
                "long-double witness reevaluation; not formal interval arithmetic"
            ),
        },
        "finite_residual_layer": {
            "statement": (
                "At finite cutoff, E_M(1/2,t_M)>0 and partial_sigma E_M may be "
                "nonzero. The quotient minimum can occur at delta=O(||Chi_M||), "
                "below the limiting tangent coefficient kappa."
            ),
            "quadratic_prediction": (
                "delta_*=-2E0/g and q_*=c_local-g^2/(4E0), where "
                "g=partial_sigma E and c_local=D/(kappa-a)"
            ),
            "limit_warning": (
                "pointwise fixed-delta convergence and the cutoff-wise infimum "
                "need not commute"
            ),
        },
        "cutoff_rows": cutoff_rows,
        "headline": {
            "minimum_requested_coefficient_certified_across_successful_cutoffs": (
                minimum_certified
            ),
            "minimum_longdouble_upper_witness_across_survey": (
                minimum_upper_witness
            ),
            "all_requested_certificates_passed": bool(
                certificates
                and len(certified) == len(certificates)
                and all(cutoff in cutoffs for cutoff in certificates)
            ),
        },
        "scope": {
            "closed": (
                "finite compact coercivity for each coefficient whose branch "
                "audit returns CERTIFIED_NONNEGATIVE_ON_COMPACT"
            ),
            "not_closed": (
                "a cutoff-uniform positive liminf; the reported sequence must "
                "be extended and its lower certificates stabilized"
            ),
        },
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cameras", default="2,3,4,5,6,7")
    parser.add_argument(
        "--cutoffs", default="64,128,256,512,1024,2048,4096"
    )
    parser.add_argument(
        "--windows",
        default=(
            "13.8:14.4,20.7:21.3,24.7:25.3,"
            "30.1:30.8,32.6:33.2,37.2:38.0"
        ),
    )
    parser.add_argument("--sigma-min", type=float, default=0.49)
    parser.add_argument("--sigma-max", type=float, default=0.51)
    parser.add_argument("--t-min", type=float, default=10.0)
    parser.add_argument("--t-max", type=float, default=40.0)
    parser.add_argument(
        "--certify",
        default="64:9.5,128:10.3,256:9.5,512:10,1024:8.8,2048:5,4096:4",
        help="comma-separated cutoff:coefficient lower-bound attempts",
    )
    parser.add_argument("--sigma-bins", type=int, default=8)
    parser.add_argument("--time-bins", type=int, default=120)
    parser.add_argument("--maximum-cells", type=int, default=500_000)
    parser.add_argument("--minimum-sigma-radius", type=float, default=5.0e-10)
    parser.add_argument("--minimum-time-radius", type=float, default=8.0e-10)
    parser.add_argument("--guard-multiplier", type=float, default=4096.0)
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("--csv-out", type=Path)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    try:
        if args.sigma_bins < 1 or args.time_bins < 1:
            raise ValueError("sigma-bins and time-bins must be positive")
        if args.maximum_cells < 1:
            raise ValueError("maximum-cells must be positive")
        if args.guard_multiplier < 0.0:
            raise ValueError("guard-multiplier must be nonnegative")
        report = run_lab(args)
    except ValueError as exc:
        parser.error(str(exc))
    payload = json.dumps(report, indent=2, sort_keys=True)
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(payload + "\n", encoding="utf-8")
    if args.csv_out is not None:
        write_csv(args.csv_out, flatten_rows(report))
    print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
