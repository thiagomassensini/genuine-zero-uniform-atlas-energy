#!/usr/bin/env python3
"""Carry-weighted Green atlas normalized by its quadratic frame.

For each positional base b, integers are reorganized into b-adic towers

    n = b**k m,  b does not divide m.

On every tower the physical amplitude ratio is q_b=b**(-1/2), and the exact
weighted TFVD is used:

    B_q x(k) = q x(k) - 2 x(k+1) + q**(-1) x(k+2),
    Tr_q x = (x(0), q**(-1)x(1)-x(0)),
    G_q B_q + R_q Tr_q = I.

The completed canonical quadratic analysis is

    A_q = q**(-1) (I-qU)**2.

For several bases, their tower analyses A_b are stacked and normalized by the
quadratic frame F=sum_b A_b* A_b:

    V = stack_b(A_b) F**(-1/2),   V*V=I.

This keeps the native primitive operator unchanged.  It supplies the
carry-scaled conservative atlas in which its resultants are observed.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence

import numpy as np

import native_carry_collective_operator_lab as collective
import native_carry_primitive_real_operator_all_bases_fixed as native


@dataclass(frozen=True)
class TowerChart:
    base: int
    q: float
    analysis_raw: np.ndarray
    synthesis_raw: np.ndarray
    canonical_analysis: np.ndarray
    raw_port_kinds: tuple[str, ...]
    canonical_port_kinds: tuple[str, ...]
    towers: tuple[tuple[int, tuple[int, ...]], ...]


def weighted_tfvd_block(
    length: int, q: float
) -> tuple[np.ndarray, np.ndarray, np.ndarray, tuple[str, ...], tuple[str, ...]]:
    if length < 1:
        raise ValueError("tower length must be positive")
    if not 0.0 < q < 1.0:
        raise ValueError("q must lie in (0,1)")

    if length == 1:
        raw_analysis = np.ones((1, 1), dtype=np.float64)
        raw_synthesis = np.ones((1, 1), dtype=np.float64)
        canonical = np.asarray([[1.0 / q]], dtype=np.float64)
        return raw_analysis, raw_synthesis, canonical, ("trace_value",), ("boundary",)

    bracket = np.zeros((max(0, length - 2), length), dtype=np.float64)
    for row in range(length - 2):
        bracket[row, row] = q
        bracket[row, row + 1] = -2.0
        bracket[row, row + 2] = 1.0 / q

    trace = np.zeros((2, length), dtype=np.float64)
    trace[0, 0] = 1.0
    trace[1, 0] = -1.0
    trace[1, 1] = 1.0 / q
    raw_analysis = np.vstack((bracket, trace))

    green = np.zeros((length, max(0, length - 2)), dtype=np.float64)
    for row in range(2, length):
        for column in range(row - 1):
            distance = row - 1 - column
            green[row, column] = distance * q**distance
    boundary_return = np.zeros((length, 2), dtype=np.float64)
    for depth in range(length):
        boundary_return[depth, 0] = q**depth
        boundary_return[depth, 1] = depth * q**depth
    raw_synthesis = np.hstack((green, boundary_return))

    canonical = np.zeros((length, length), dtype=np.float64)
    canonical[0, 0] = 1.0 / q
    canonical[1, 0] = -2.0
    canonical[1, 1] = 1.0 / q
    for row in range(2, length):
        canonical[row, row - 2] = q
        canonical[row, row - 1] = -2.0
        canonical[row, row] = 1.0 / q

    raw_kinds = tuple(["bulk"] * (length - 2) + ["trace_value", "trace_slope"])
    canonical_kinds = tuple(["boundary", "boundary"] + ["bulk"] * (length - 2))
    return raw_analysis, raw_synthesis, canonical, raw_kinds, canonical_kinds


def tower_partition(base: int, size: int) -> tuple[tuple[int, tuple[int, ...]], ...]:
    towers: list[tuple[int, tuple[int, ...]]] = []
    covered: list[int] = []
    for core in range(1, size + 1):
        if core % base == 0:
            continue
        values: list[int] = []
        number = core
        while number <= size:
            values.append(number)
            covered.append(number)
            number *= base
        towers.append((core, tuple(values)))
    if sorted(covered) != list(range(1, size + 1)):
        raise AssertionError("b-adic towers do not partition the ambient integers")
    return tuple(towers)


def build_tower_chart(base: int, size: int) -> TowerChart:
    q = base ** -0.5
    towers = tower_partition(base, size)
    raw_analysis = np.zeros((size, size), dtype=np.float64)
    raw_synthesis = np.zeros((size, size), dtype=np.float64)
    canonical = np.zeros((size, size), dtype=np.float64)
    raw_kinds: list[str] = []
    canonical_kinds: list[str] = []
    port_start = 0
    for _, numbers in towers:
        length = len(numbers)
        block_j, block_s, block_a, block_raw_kinds, block_canonical_kinds = (
            weighted_tfvd_block(length, q)
        )
        ports = np.arange(port_start, port_start + length, dtype=np.int64)
        vertices = np.asarray(numbers, dtype=np.int64) - 1
        raw_analysis[np.ix_(ports, vertices)] = block_j
        raw_synthesis[np.ix_(vertices, ports)] = block_s
        canonical[np.ix_(ports, vertices)] = block_a
        raw_kinds.extend(block_raw_kinds)
        canonical_kinds.extend(block_canonical_kinds)
        port_start += length
    return TowerChart(
        base=base,
        q=q,
        analysis_raw=raw_analysis,
        synthesis_raw=raw_synthesis,
        canonical_analysis=canonical,
        raw_port_kinds=tuple(raw_kinds),
        canonical_port_kinds=tuple(canonical_kinds),
        towers=towers,
    )


def inverse_positive_sqrt(matrix: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    if float(eigenvalues[0]) <= 0.0:
        raise RuntimeError("quadratic frame is not positive definite")
    inverse_sqrt = (
        eigenvectors * (1.0 / np.sqrt(eigenvalues))[None, :]
    ) @ eigenvectors.T
    sqrt = (eigenvectors * np.sqrt(eigenvalues)[None, :]) @ eigenvectors.T
    return inverse_sqrt, sqrt


def exact_gap(base: int) -> float:
    q = base ** -0.5
    return (1.0 - q) ** 4 / q**2


def chart_audit(
    chart: TowerChart,
    state: np.ndarray,
    native_row: np.ndarray,
    time_value: float,
) -> dict[str, Any]:
    size = state.size
    identity = np.eye(size, dtype=np.float64)
    raw_ports = chart.analysis_raw @ state
    reconstructed = chart.synthesis_raw @ raw_ports
    canonical_ports = chart.canonical_analysis @ state
    port_change = chart.canonical_analysis @ chart.synthesis_raw
    canonical_from_raw = port_change @ raw_ports

    bulk_mask = np.asarray(
        [kind == "bulk" for kind in chart.raw_port_kinds], dtype=bool
    )
    trace_mask = ~bulk_mask
    bulk_resultant = native_row @ (
        chart.synthesis_raw[:, bulk_mask] @ raw_ports[bulk_mask]
    )
    boundary_resultant = native_row @ (
        chart.synthesis_raw[:, trace_mask] @ raw_ports[trace_mask]
    )
    direct_resultant = native_row @ state

    canonical_bulk_mask = np.asarray(
        [kind == "bulk" for kind in chart.canonical_port_kinds], dtype=bool
    )
    canonical_boundary_mask = ~canonical_bulk_mask
    quadratic_energy = float(np.vdot(canonical_ports, canonical_ports).real)
    bulk_quadratic_energy = float(
        np.vdot(
            canonical_ports[canonical_bulk_mask],
            canonical_ports[canonical_bulk_mask],
        ).real
    )
    boundary_quadratic_energy = float(
        np.vdot(
            canonical_ports[canonical_boundary_mask],
            canonical_ports[canonical_boundary_mask],
        ).real
    )

    singular = np.linalg.svd(chart.canonical_analysis, compute_uv=False)
    raw_singular = np.linalg.svd(chart.analysis_raw, compute_uv=False)
    maximum_ratio_error = 0.0
    maximum_boundary_phase_error = 0.0
    maximum_boundary_phase_modulus_error = 0.0
    boundary_phase_count = 0
    unresolved_singleton_towers = 0
    phase_ratio = chart.q * np.exp(-1j * time_value * math.log(chart.base))
    expected_boundary_phase = np.exp(-1j * time_value * math.log(chart.base))
    for _, numbers in chart.towers:
        if len(numbers) < 2:
            unresolved_singleton_towers += 1
            continue
        tower_values = state[np.asarray(numbers, dtype=np.int64) - 1]
        ratios = tower_values[1:] / tower_values[:-1]
        maximum_ratio_error = max(
            maximum_ratio_error, float(np.max(np.abs(ratios - phase_ratio)))
        )
        gamma_zero = tower_values[0]
        gamma_one = tower_values[1] / chart.q - tower_values[0]
        boundary_phase = 1.0 + gamma_one / gamma_zero
        maximum_boundary_phase_error = max(
            maximum_boundary_phase_error,
            float(abs(boundary_phase - expected_boundary_phase)),
        )
        maximum_boundary_phase_modulus_error = max(
            maximum_boundary_phase_modulus_error,
            abs(abs(boundary_phase) - 1.0),
        )
        boundary_phase_count += 1

    return {
        "base": chart.base,
        "q": chart.q,
        "tower_count": len(chart.towers),
        "maximum_tower_depth_count": max(len(numbers) for _, numbers in chart.towers),
        "tfvd_identity_error": float(
            np.linalg.norm(chart.synthesis_raw @ chart.analysis_raw - identity, ord=2)
        ),
        "tfvd_reverse_identity_error": float(
            np.linalg.norm(chart.analysis_raw @ chart.synthesis_raw - identity, ord=2)
        ),
        "state_reconstruction_error": float(np.linalg.norm(reconstructed - state)),
        "canonical_from_raw_port_error": float(
            np.linalg.norm(canonical_from_raw - canonical_ports)
        ),
        "physical_tower_ratio_error": maximum_ratio_error,
        "boundary_phase_port": {
            "identity": "1+Gamma1/Gamma0=exp(-it log b)",
            "resolved_tower_count": boundary_phase_count,
            "cutoff_singleton_tower_count": unresolved_singleton_towers,
            "maximum_phase_error": maximum_boundary_phase_error,
            "maximum_unit_modulus_error": maximum_boundary_phase_modulus_error,
        },
        "raw_chart_condition_number": float(raw_singular[0] / raw_singular[-1]),
        "canonical_min_singular_squared": float(singular[-1] ** 2),
        "canonical_max_singular_squared": float(singular[0] ** 2),
        "exact_infinite_tower_gap": exact_gap(chart.base),
        "quadratic_energy": quadratic_energy,
        "quadratic_bulk_energy": bulk_quadratic_energy,
        "quadratic_boundary_energy": boundary_quadratic_energy,
        "quadratic_ledger_error": abs(
            quadratic_energy - bulk_quadratic_energy - boundary_quadratic_energy
        ),
        "native_bulk_resultant": [
            float(complex(bulk_resultant).real),
            float(complex(bulk_resultant).imag),
        ],
        "native_boundary_resultant": [
            float(complex(boundary_resultant).real),
            float(complex(boundary_resultant).imag),
        ],
        "native_direct_resultant": [
            float(complex(direct_resultant).real),
            float(complex(direct_resultant).imag),
        ],
        "native_balance_error": float(
            abs(bulk_resultant + boundary_resultant - direct_resultant)
        ),
    }


def standalone_green_scaling_audit(
    bases: Sequence[int], lengths: Sequence[int]
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for base in bases:
        q = base ** -0.5
        for length in lengths:
            raw, synthesis, canonical, _, _ = weighted_tfvd_block(length, q)
            singular = np.linalg.svd(canonical, compute_uv=False)
            green = synthesis[:, : max(0, length - 2)]
            rows.append(
                {
                    "base": int(base),
                    "q": q,
                    "length": int(length),
                    "identity_error": float(
                        np.linalg.norm(synthesis @ raw - np.eye(length), ord=2)
                    ),
                    "green_norm": float(np.linalg.norm(green, ord=2)) if green.size else 0.0,
                    "green_young_bound": q / (1.0 - q) ** 2,
                    "canonical_gap": float(singular[-1] ** 2),
                    "exact_infinite_gap": exact_gap(int(base)),
                    "canonical_condition": float(singular[0] / singular[-1]),
                }
            )

    q_control = 1.0
    controls: list[dict[str, Any]] = []
    for length in lengths:
        # q=1 control is constructed explicitly because the physical helper
        # intentionally requires q<1.
        canonical = np.zeros((length, length), dtype=np.float64)
        canonical[0, 0] = 1.0
        if length > 1:
            canonical[1, 0] = -2.0
            canonical[1, 1] = 1.0
        for row in range(2, length):
            canonical[row, row - 2] = 1.0
            canonical[row, row - 1] = -2.0
            canonical[row, row] = 1.0
        singular = np.linalg.svd(canonical, compute_uv=False)
        controls.append(
            {
                "q": q_control,
                "length": int(length),
                "canonical_gap": float(singular[-1] ** 2),
                "canonical_condition": float(singular[0] / singular[-1]),
            }
        )
    return {
        "weighted_rows": rows,
        "unweighted_q_equal_1_control": controls,
        "interpretation": (
            "q=b^(-1/2) keeps the Green kernel r q^r summable and the completed "
            "quadratic analysis uniformly coercive; q=1 loses the infinite gap."
        ),
    }


def quadratic_frame_audit(
    charts: Sequence[TowerChart],
    logarithmic_generator: np.ndarray,
    state: np.ndarray,
    amplitude: np.ndarray,
    camera_matrix: np.ndarray,
) -> dict[str, Any]:
    stacked = np.vstack([chart.canonical_analysis for chart in charts])
    frame = stacked.T @ stacked
    inverse_sqrt, _ = inverse_positive_sqrt(frame)
    atlas_analysis = stacked @ inverse_sqrt
    identity = np.eye(state.size, dtype=np.float64)
    sync_projection_action = atlas_analysis @ (atlas_analysis.T @ (atlas_analysis @ state))
    atlas_state = atlas_analysis @ state
    reconstructed = atlas_analysis.T @ atlas_state

    atlas_readout = camera_matrix @ atlas_analysis.T
    native_direct = camera_matrix @ state
    native_atlas = atlas_readout @ atlas_state

    camera_gram = camera_matrix @ camera_matrix.T
    gram_eigenvalues, gram_eigenvectors = np.linalg.eigh(camera_gram)
    gram_inverse_sqrt = (
        gram_eigenvectors * (1.0 / np.sqrt(gram_eigenvalues))[None, :]
    ) @ gram_eigenvectors.T
    normalized_camera_readout = gram_inverse_sqrt @ atlas_readout
    normalized_input = atlas_analysis @ (amplitude / np.linalg.norm(amplitude))
    visible = normalized_camera_readout @ (
        atlas_analysis @ (state / np.linalg.norm(amplitude))
    )
    visible_energy = float(np.vdot(visible, visible).real)

    generator_action_error = float(
        np.linalg.norm(
            atlas_analysis @ (logarithmic_generator @ state)
            - atlas_analysis
            @ (
                logarithmic_generator
                @ (atlas_analysis.T @ atlas_state)
            )
        )
    )
    frame_eigenvalues = np.linalg.eigvalsh(frame)
    expected_lower = sum(exact_gap(chart.base) for chart in charts)
    return {
        "atlas_dimension": int(atlas_analysis.shape[0]),
        "state_dimension": int(state.size),
        "quadratic_frame_min_eigenvalue": float(frame_eigenvalues[0]),
        "quadratic_frame_max_eigenvalue": float(frame_eigenvalues[-1]),
        "sum_of_exact_infinite_base_gaps": expected_lower,
        "margin_above_sum_gap": float(frame_eigenvalues[0] - expected_lower),
        "parseval_error": float(
            np.linalg.norm(atlas_analysis.T @ atlas_analysis - identity, ord=2)
        ),
        "state_energy": float(np.vdot(state, state).real),
        "atlas_energy": float(np.vdot(atlas_state, atlas_state).real),
        "energy_error": abs(
            float(np.vdot(state, state).real)
            - float(np.vdot(atlas_state, atlas_state).real)
        ),
        "state_reconstruction_error": float(np.linalg.norm(reconstructed - state)),
        "sync_projector_fixed_point_error": float(
            np.linalg.norm(sync_projection_action - atlas_state)
        ),
        "native_readout_error": float(np.max(np.abs(native_atlas - native_direct))),
        "log_generator_coherent_action_error": generator_action_error,
        "normalized_readout_coisometry_error": float(
            np.linalg.norm(
                normalized_camera_readout @ normalized_camera_readout.conjugate().T
                - np.eye(camera_matrix.shape[0]),
                ord=2,
            )
        ),
        "normalized_input_energy_error": abs(
            1.0 - float(np.vdot(normalized_input, normalized_input).real)
        ),
        "visible_characteristic_energy": visible_energy,
        "hidden_characteristic_energy": 1.0 - visible_energy,
        "characteristic_identity": (
            "Phi(t)=(CC*)^(-1/2) C V* exp(-it VLV*) V alpha/||alpha|| "
            "=(CC*)^(-1/2) C exp(-itL) alpha/||alpha||"
        ),
    }


def refine_collective_time(
    models: Sequence[native.CameraModel], state_block: int
) -> tuple[float, float]:
    def objective(value: float) -> float:
        _, scores, _ = collective.evaluate_one(value, models, state_block)
        return float(np.sum(scores))

    return collective.golden_minimize(objective, 14.12, 14.15, steps=70)


def run_lab(args: argparse.Namespace) -> dict[str, Any]:
    cameras = native.parse_cameras(args.cameras)
    models = [native.build_camera_model(camera, args.cutoff) for camera in cameras]
    camera_matrix, size = collective.native_readout_matrix(models)
    blind_time, score_sum = refine_collective_time(models, args.state_block)
    numbers = np.arange(1, size + 1, dtype=np.float64)
    amplitude = numbers ** -0.5
    state = amplitude * np.exp(-1j * blind_time * np.log(numbers))
    logarithmic_generator = np.diag(np.log(numbers))
    charts = [build_tower_chart(camera, size) for camera in cameras]

    chart_rows = [
        chart_audit(chart, state, camera_matrix[index], blind_time)
        for index, chart in enumerate(charts)
    ]
    return {
        "schema": "org.native-carry.quadratic-weighted-green-atlas/v1",
        "status": "FINITE_CARRY_WEIGHTED_QUADRATIC_GREEN_AUDIT",
        "native_operator_authority": (
            "native_carry_primitive_real_operator_all_bases_fixed.py"
        ),
        "configuration": {
            "cameras": list(cameras),
            "cutoff": args.cutoff,
            "ambient_dimension": size,
            "refined_blind_time": blind_time,
            "sum_native_scores": score_sum,
        },
        "scale_correction": {
            "mass": "b^(-k)",
            "amplitude": "q_b^k=b^(-k/2)",
            "weighted_green_kernel": "r q_b^r",
            "weighted_return": "q_b^k(a+kb)",
            "boundary_transport_ports": (
                "Gamma_in=x_0; Gamma_out=q_b^(-1)x_1=Gamma_0+Gamma_1"
            ),
            "native_boundary_phase": (
                "Gamma_out/Gamma_in=exp(-it log b)"
            ),
            "quadratic_analysis": "A_q=q^(-1)(I-qU)^2",
            "atlas_normalization": "V=stack(A_b) [sum_b A_b* A_b]^(-1/2)",
        },
        "camera_tower_charts": chart_rows,
        "quadratic_frame": quadratic_frame_audit(
            charts,
            logarithmic_generator,
            state,
            amplitude,
            camera_matrix,
        ),
        "green_scaling": standalone_green_scaling_audit(
            cameras, (8, 16, 32, 64)
        ),
        "interpretation": {
            "physical_green": (
                "Green is built in vertical carry depth and already contains the "
                "quadratic amplitude q_b=b^(-1/2)."
            ),
            "conservation": (
                "The multibase atlas is Parseval only after normalization by its "
                "carry-quadratic frame, not by an after-the-fact Euclidean Green metric."
            ),
            "native_resultant": (
                "Native camera rows are unchanged and are exactly recovered after "
                "weighted TFVD reconstruction and quadratic-frame synthesis."
            ),
            "boundary_phase": (
                "Quadratic carry scaling absorbs the radial q_b factor, so the "
                "resolved endpoint transport has unit modulus and retains only "
                "exp(-it log b)."
            ),
            "remaining_gate": (
                "Construct the maximal Green-symmetric endpoint relation for the "
                "quadratically normalized atlas and its infinite local-energy limit."
            ),
        },
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cameras", default="2,3,4,5,6,7")
    parser.add_argument("--cutoff", type=int, default=32)
    parser.add_argument("--state-block", type=int, default=512)
    parser.add_argument("--output", type=Path)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    if args.cutoff < 1 or args.state_block < 1:
        parser.error("cutoff and state-block must be positive")
    report = run_lab(args)
    payload = json.dumps(report, indent=2, sort_keys=True)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload + "\n", encoding="utf-8")
    print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
