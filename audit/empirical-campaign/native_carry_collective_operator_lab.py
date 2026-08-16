#!/usr/bin/env python3
"""Collective-observation laboratory for the native real carry operator.

This file does not replace or recalibrate the native operator implemented in
``native_carry_primitive_real_operator_all_bases_fixed.py``.  It unfolds the
same finite operator into three factors:

    psi(t) = exp(-i t L) a,       L_nn = log(n),  a_n = n^(-1/2),
    B_b psi = native seeds and centered brackets of camera b,
    C_b psi = Sigma_b B_b psi = native primitive resultant R_b.

Complex notation is used only as a lossless shorthand for the two real
coordinates (x, y).  No complex calibration is applied.  For a finite family
of cameras, C stacks the native resultants and

    K = C* C

is the derived positive self-adjoint collective-visibility operator.  The
native simultaneous-blindness condition is

    C psi(t) = 0  <=>  <psi(t), K psi(t)> = 0.

The native score is also retained.  Its denominator is the time-dependent
coordinate energy ||B_b psi(t)||^2, so K represents its raw numerator, not the
whole normalized score.

This is a finite numerical audit, not an infinite-dimensional theorem.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, Callable, Sequence

import numpy as np

import native_carry_primitive_real_operator_all_bases_fixed as native


def positive_integers_from_logs(logs: np.ndarray) -> np.ndarray:
    values = np.rint(np.exp(logs)).astype(np.int64)
    if np.any(values < 1) or not np.allclose(
        logs, np.log(values.astype(np.float64)), rtol=0.0, atol=4.0e-14
    ):
        raise AssertionError("camera logs do not reconstruct positive integers")
    return values


def model_integer_data(model: native.CameraModel) -> dict[str, np.ndarray]:
    return {
        "seed": positive_integers_from_logs(model.seed_log),
        "left": positive_integers_from_logs(model.left_log),
        "center": positive_integers_from_logs(model.center_log),
        "right": positive_integers_from_logs(model.right_log),
    }


def native_camera_row(model: native.CameraModel, ambient_size: int) -> np.ndarray:
    """Collapse exactly the native seeds/brackets into their resultant row."""
    data = model_integer_data(model)
    largest = max(int(np.max(values)) for values in data.values())
    if ambient_size < largest:
        raise ValueError("ambient space is smaller than the camera support")

    row = np.zeros(ambient_size, dtype=np.float64)
    np.add.at(row, data["seed"] - 1, 1.0)
    np.add.at(row, data["left"] - 1, 1.0)
    np.add.at(row, data["center"] - 1, -2.0)
    np.add.at(row, data["right"] - 1, 1.0)
    return row


def native_readout_matrix(
    models: Sequence[native.CameraModel],
) -> tuple[np.ndarray, int]:
    integer_data = [model_integer_data(model) for model in models]
    ambient_size = max(
        int(np.max(values)) for data in integer_data for values in data.values()
    )
    rows = np.vstack(
        [native_camera_row(model, ambient_size) for model in models]
    )
    return rows, ambient_size


def complex_state(time_value: float, ambient_size: int) -> np.ndarray:
    numbers = np.arange(1, ambient_size + 1, dtype=np.float64)
    return numbers ** -0.5 * np.exp(-1j * float(time_value) * np.log(numbers))


def evaluate_models(
    times: np.ndarray,
    models: Sequence[native.CameraModel],
    state_block: int,
    time_block: int,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return native complex resultants, scores, and coordinate energies."""
    times = np.asarray(times, dtype=np.float64)
    resultants = np.empty((times.size, len(models)), dtype=np.complex128)
    scores = np.empty((times.size, len(models)), dtype=np.float64)
    coordinate_energies = np.empty_like(scores)

    for start in range(0, times.size, time_block):
        stop = min(start + time_block, times.size)
        time_slice = times[start:stop]
        for camera_index, model in enumerate(models):
            balance = native.evaluate_camera_chunk_numpy(
                time_slice, model, state_block, return_balance=True
            )
            real_resultant = np.asarray(balance["resultant"], dtype=np.float64)
            resultants[start:stop, camera_index] = (
                real_resultant[:, 0] + 1j * real_resultant[:, 1]
            )
            scores[start:stop, camera_index] = np.asarray(
                balance["score"], dtype=np.float64
            )
            coordinate_energies[start:stop, camera_index] = np.asarray(
                balance["total_energy"], dtype=np.float64
            )
    return resultants, scores, coordinate_energies


def evaluate_one(
    time_value: float,
    models: Sequence[native.CameraModel],
    state_block: int,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    resultants, scores, energies = evaluate_models(
        np.asarray([time_value], dtype=np.float64),
        models,
        state_block,
        time_block=1,
    )
    return resultants[0], scores[0], energies[0]


def golden_minimize(
    function: Callable[[float], float], lower: float, upper: float, steps: int = 60
) -> tuple[float, float]:
    ratio = (math.sqrt(5.0) - 1.0) / 2.0
    x_left = upper - ratio * (upper - lower)
    x_right = lower + ratio * (upper - lower)
    y_left = function(x_left)
    y_right = function(x_right)
    for _ in range(steps):
        if y_left <= y_right:
            upper = x_right
            x_right, y_right = x_left, y_left
            x_left = upper - ratio * (upper - lower)
            y_left = function(x_left)
        else:
            lower = x_left
            x_left, y_left = x_right, y_right
            x_right = lower + ratio * (upper - lower)
            y_right = function(x_right)
    point = 0.5 * (lower + upper)
    return point, function(point)


def native_equivalence_audit(
    models: Sequence[native.CameraModel],
    camera_matrix: np.ndarray,
    ambient_size: int,
    state_block: int,
) -> dict[str, Any]:
    sample_times = np.asarray([1.25, 7.0, 14.135, 30.425], dtype=np.float64)
    native_resultants, _, _ = evaluate_models(
        sample_times, models, state_block, time_block=sample_times.size
    )
    matrix_resultants = np.vstack(
        [camera_matrix @ complex_state(float(time), ambient_size) for time in sample_times]
    )
    errors = np.abs(native_resultants - matrix_resultants)
    return {
        "sample_times": sample_times.tolist(),
        "maximum_absolute_error": float(np.max(errors)),
        "maximum_relative_error": float(
            np.max(errors / np.maximum(np.abs(native_resultants), 1.0e-300))
        ),
        "passed": bool(np.max(errors) < 2.0e-12),
        "identity": "R_b(t) = C_b exp(-i t diag(log n)) a",
    }


def local_minimum_indices(values: np.ndarray) -> np.ndarray:
    if values.size < 3:
        return np.empty(0, dtype=np.int64)
    return np.flatnonzero(
        (values[1:-1] <= values[:-2]) & (values[1:-1] < values[2:])
    ).astype(np.int64) + 1


def collective_scan(
    times: np.ndarray,
    models: Sequence[native.CameraModel],
    state_block: int,
    time_block: int,
    maximum_minima: int,
    deep_threshold: float,
) -> tuple[dict[str, Any], float]:
    resultants, scores, coordinate_energies = evaluate_models(
        times, models, state_block, time_block
    )
    raw_visibility = np.sum(np.abs(resultants) ** 2, axis=1)
    native_score_sum = np.sum(scores, axis=1)
    minima = local_minimum_indices(native_score_sum)
    minima = minima[np.argsort(times[minima])][:maximum_minima]

    rows: list[dict[str, Any]] = []
    for index in minima:
        lower = float(times[index - 1])
        upper = float(times[index + 1])

        def objective(value: float) -> float:
            _, camera_scores, _ = evaluate_one(value, models, state_block)
            return float(np.sum(camera_scores))

        refined_time, refined_score_sum = golden_minimize(objective, lower, upper)
        camera_resultants, camera_scores, camera_energies = evaluate_one(
            refined_time, models, state_block
        )
        rows.append(
            {
                "grid_time": float(times[index]),
                "refined_time": refined_time,
                "sum_native_scores": refined_score_sum,
                "raw_K_visibility": float(np.sum(np.abs(camera_resultants) ** 2)),
                "cameras": [
                    {
                        "camera": model.camera,
                        "resultant": [
                            float(camera_resultants[position].real),
                            float(camera_resultants[position].imag),
                        ],
                        "resultant_norm": float(abs(camera_resultants[position])),
                        "native_score": float(camera_scores[position]),
                        "coordinate_energy": float(camera_energies[position]),
                    }
                    for position, model in enumerate(models)
                ],
            }
        )

    if not rows:
        minimum_index = int(np.argmin(native_score_sum))
        first_time = float(times[minimum_index])
    else:
        first_time = float(rows[0]["refined_time"])

    report = {
        "grid": {
            "t_min": float(times[0]),
            "t_max": float(times[-1]),
            "points": int(times.size),
            "spacing": float(times[1] - times[0]) if times.size > 1 else None,
        },
        "number_of_local_minima": int(local_minimum_indices(native_score_sum).size),
        "reported_minima": rows,
        "deep_collective_minima": [
            row for row in rows if row["sum_native_scores"] <= deep_threshold
        ],
        "deep_threshold_for_sum_native_scores": deep_threshold,
        "raw_visibility_minimum_on_grid": float(np.min(raw_visibility)),
        "native_score_sum_minimum_on_grid": float(np.min(native_score_sum)),
        "maximum_coordinate_energy_drift_fraction": float(
            np.max(
                (np.max(coordinate_energies, axis=0) - np.min(coordinate_energies, axis=0))
                / np.maximum(np.mean(coordinate_energies, axis=0), native.FLOAT_TINY)
            )
        ),
        "normalization_warning": (
            "K=C*C gives the raw-resultant numerator. Native scores additionally divide "
            "by each camera's time-dependent bracket-coordinate energy. Both have the "
            "same exact simultaneous zeros, but need not rank finite nonzero valleys identically."
        ),
    }
    return report, first_time


def operator_audit(
    time_value: float,
    models: Sequence[native.CameraModel],
    camera_matrix: np.ndarray,
    ambient_size: int,
    state_block: int,
) -> dict[str, Any]:
    state = complex_state(time_value, ambient_size)
    resultants = camera_matrix @ state
    gram = camera_matrix @ camera_matrix.T
    gram_eigenvalues = np.linalg.eigvalsh(gram)
    rank = int(np.linalg.matrix_rank(camera_matrix, tol=1.0e-11))

    row_projection = camera_matrix.T @ (
        np.linalg.pinv(gram, rcond=1.0e-13) @ resultants
    )
    hidden_state = state - row_projection
    state_energy = float(np.vdot(state, state).real)
    row_projection_energy = float(np.vdot(row_projection, row_projection).real)
    hidden_energy = float(np.vdot(hidden_state, hidden_state).real)

    numbers = np.arange(1, ambient_size + 1, dtype=np.float64)
    logarithms = np.log(numbers)
    k_state = camera_matrix.T @ resultants
    commutator_action = logarithms * k_state - camera_matrix.T @ (
        camera_matrix @ (logarithms * state)
    )
    derivative_from_commutator = float(
        (1j * np.vdot(state, commutator_action)).real
    )
    step = 1.0e-6
    energy_plus = float(
        np.linalg.norm(camera_matrix @ complex_state(time_value + step, ambient_size)) ** 2
    )
    energy_minus = float(
        np.linalg.norm(camera_matrix @ complex_state(time_value - step, ambient_size)) ** 2
    )
    derivative_finite_difference = (energy_plus - energy_minus) / (2.0 * step)

    phases = np.exp(-1j * time_value * logarithms)
    transported_rows = camera_matrix * phases[None, :]
    transported_gram = transported_rows @ transported_rows.conjugate().T

    native_resultants, _, _ = evaluate_one(time_value, models, state_block)
    result_error = float(np.max(np.abs(native_resultants - resultants)))
    return {
        "time": time_value,
        "ambient_dimension": ambient_size,
        "camera_count": len(models),
        "rank_C": rank,
        "nullity_C": ambient_size - rank,
        "nonzero_spectrum_of_K_via_CC_star": gram_eigenvalues.tolist(),
        "smallest_gram_eigenvalue": float(gram_eigenvalues[0]),
        "largest_gram_eigenvalue": float(gram_eigenvalues[-1]),
        "state_energy": state_energy,
        "raw_visibility_energy": float(np.vdot(resultants, resultants).real),
        "row_space_projection_energy": row_projection_energy,
        "hidden_kernel_energy": hidden_energy,
        "projection_pythagoras_error": abs(
            state_energy - row_projection_energy - hidden_energy
        ),
        "native_resultant_matrix_error": result_error,
        "K_properties": {
            "definition": "K = C* C (real form: K tensor I_2)",
            "self_adjoint": True,
            "positive_semidefinite": True,
            "native_operator_replacement": False,
        },
        "commutator_clock": {
            "identity": "d_t <psi,K psi> = i <psi,[L,K] psi>",
            "derivative_from_commutator": derivative_from_commutator,
            "derivative_finite_difference": derivative_finite_difference,
            "absolute_error": abs(
                derivative_from_commutator - derivative_finite_difference
            ),
        },
        "unitary_conjugacy_negative_test": {
            "camera_gram_drift": float(
                np.linalg.norm(transported_gram - gram, ord=2)
            ),
            "conclusion": (
                "The logarithmic phase alone is a right unitary gauge: "
                "C D_t D_t* C* = C C*. It moves the fixed-mass state relative "
                "to ker(C), but does not create a t-dependent spectrum of K."
            ),
        },
    }


def incidence_and_holonomy_audit(
    time_value: float,
    camera_matrix: np.ndarray,
    models: Sequence[native.CameraModel],
    ambient_size: int,
) -> dict[str, Any]:
    supports = camera_matrix != 0.0
    overlap = supports.astype(np.int64) @ supports.astype(np.int64).T
    adjacency = overlap > 0
    np.fill_diagonal(adjacency, False)

    visited = {0}
    frontier = [0]
    while frontier:
        node = frontier.pop()
        for neighbor in np.flatnonzero(adjacency[node]):
            neighbor_value = int(neighbor)
            if neighbor_value not in visited:
                visited.add(neighbor_value)
                frontier.append(neighbor_value)

    resultants = camera_matrix @ complex_state(time_value, ambient_size)
    if np.any(np.abs(resultants) < 1.0e-12):
        time_value += 0.271828
        resultants = camera_matrix @ complex_state(time_value, ambient_size)
    phases = resultants / np.abs(resultants)
    loop_product = 1.0 + 0.0j
    for index in range(len(phases)):
        next_index = (index + 1) % len(phases)
        loop_product *= phases[next_index] / phases[index]

    return {
        "natural_complex": (
            "integer vertices n -> native seed/bracket coordinates (b,e) -> camera ports b"
        ),
        "gluing_rule": "the same integer state psi_t(n) feeds every base containing n",
        "support_overlap_matrix": overlap.tolist(),
        "camera_overlap_graph_connected": len(visited) == len(models),
        "scalar_resultant_cycle": {
            "time": time_value,
            "loop_product": [float(loop_product.real), float(loop_product.imag)],
            "distance_to_trivial_holonomy": float(abs(loop_product - 1.0)),
            "conclusion": (
                "Pairwise phases made only from scalar camera resultants telescope. "
                "They are a vertex gauge, so a nontrivial native holonomy would need "
                "richer overlap/port transport than phase ratios R_c/R_b."
            ),
        },
    }


def boundary_balance_audit(
    time_value: float,
    models: Sequence[native.CameraModel],
    state_block: int,
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for model in models:
        mechanism = native.evaluate_mechanism(
            time_value, model, state_block, include_groups=False
        )
        seed = np.asarray(mechanism["seed_resultant"], dtype=np.float64)
        bracket = np.asarray(mechanism["bracket_resultant"], dtype=np.float64)
        rows.append(
            {
                "camera": model.camera,
                "seed_resultant": seed.tolist(),
                "bracket_resultant": bracket.tolist(),
                "port_resultant": mechanism["resultant"],
                "seed_bracket_cosine": mechanism["seed_bracket_cosine"],
                "seed_bracket_magnitude_ratio": mechanism[
                    "seed_bracket_magnitude_ratio"
                ],
                "hidden_fraction": mechanism["hidden_fraction"],
            }
        )
    return {
        "time": time_value,
        "camera_ports": rows,
        "interpretation": (
            "The native zero is a seed/bracket port-balance condition inside every "
            "camera. Keeping the resultant as a port preserves information that would "
            "be lost by imposing a boundary condition before the cameras are glued."
        ),
    }


def run_lab(args: argparse.Namespace) -> dict[str, Any]:
    cameras = native.parse_cameras(args.cameras)
    models = [native.build_camera_model(camera, args.cutoff) for camera in cameras]
    camera_matrix, ambient_size = native_readout_matrix(models)
    times = np.arange(
        args.t_min,
        args.t_max + 0.5 * args.grid,
        args.grid,
        dtype=np.float64,
    )
    scan, reference_time = collective_scan(
        times,
        models,
        args.state_block,
        args.time_block,
        args.maximum_minima,
        args.deep_threshold,
    )
    return {
        "schema": "org.native-carry.collective-observation-lab/v1",
        "status": "FINITE_NATIVE_CARRY_COLLECTIVE_AUDIT",
        "authority": "native_carry_primitive_real_operator_all_bases_fixed.py",
        "configuration": {
            "cameras": list(cameras),
            "cutoff": args.cutoff,
            "state_block": args.state_block,
            "time_block": args.time_block,
        },
        "factorization": {
            "state": "psi_t(n)=n^(-1/2) exp(-i t log n), complex shorthand for R^2",
            "native_analysis": "B_b = seeds plus centered carry brackets",
            "native_readout": "C_b = Sigma_b B_b",
            "collective_readout": "C = stack_b C_b",
            "derived_visibility": "K = C* C",
            "blindness": "C psi_t = 0 iff <psi_t,K psi_t> = 0",
        },
        "native_equivalence": native_equivalence_audit(
            models, camera_matrix, ambient_size, args.state_block
        ),
        "collective_scan": scan,
        "operator_audit": operator_audit(
            reference_time,
            models,
            camera_matrix,
            ambient_size,
            args.state_block,
        ),
        "incidence_and_holonomy": incidence_and_holonomy_audit(
            reference_time + 0.271828,
            camera_matrix,
            models,
            ambient_size,
        ),
        "boundary_balance": boundary_balance_audit(
            reference_time, models, args.state_block
        ),
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cameras", default="2,3,4,5,6,7")
    parser.add_argument("--cutoff", type=int, default=256)
    parser.add_argument("--t-min", type=float, default=10.0)
    parser.add_argument("--t-max", type=float, default=50.0)
    parser.add_argument("--grid", type=float, default=0.002)
    parser.add_argument("--maximum-minima", type=int, default=20)
    parser.add_argument("--deep-threshold", type=float, default=1.0e-6)
    parser.add_argument("--state-block", type=int, default=512)
    parser.add_argument("--time-block", type=int, default=256)
    parser.add_argument("--output", type=Path)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    if args.cutoff < 1:
        parser.error("cutoff must be positive")
    if args.t_max <= args.t_min:
        parser.error("t-max must be larger than t-min")
    if args.grid <= 0.0:
        parser.error("grid must be positive")
    if args.maximum_minima < 1 or args.state_block < 1 or args.time_block < 1:
        parser.error("block sizes and maximum-minima must be positive")
    if args.deep_threshold < 0.0:
        parser.error("deep-threshold must be nonnegative")

    report = run_lab(args)
    payload = json.dumps(report, indent=2, sort_keys=True)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload + "\n", encoding="utf-8")
    print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
