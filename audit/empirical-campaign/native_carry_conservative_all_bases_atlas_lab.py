#!/usr/bin/env python3
"""Finite conservative all-bases atlas for the native carry geometry.

The native real operator is not modified.  This laboratory constructs a
kinematic observation layer around it, using every positional base b > 1.

For n > 1 let

    k_b(n) = max{k : b**k divides n},
    x_b(n) = k_b(n) log(b).

Only finitely many bases are active at each n.  Their all-bases weights are

    omega_b(n) = x_b(n) / sum_c x_c(n).

The analysis map

    (A f)_(b,n) = sqrt(omega_b(n)) f(n)

plus an explicit seed/boundary channel for n=1 is an isometry.  Thus A* A=I,
and Pi=A A* is the orthogonal projector from arbitrary local camera data onto
the globally compatible atlas.  The weighting is a proposed conservative
equalization derived from carry depth and base scale; it is not inserted into
the native primitive resultant.

Complex numbers are only shorthand for the native real two-plane.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, Sequence

import numpy as np

import native_carry_collective_operator_lab as collective
import native_carry_primitive_real_operator_all_bases_fixed as native


def positional_depth(base: int, number: int) -> int:
    if base < 2 or number < 1:
        raise ValueError("base must be > 1 and number must be positive")
    depth = 0
    quotient = number
    while quotient % base == 0:
        quotient //= base
        depth += 1
    return depth


def is_prime(number: int) -> bool:
    if number < 2:
        return False
    if number % 2 == 0:
        return number == 2
    divisor = 3
    while divisor * divisor <= number:
        if number % divisor == 0:
            return False
        divisor += 2
    return True


def depth_scale_table(
    ambient_size: int, bases: Sequence[int]
) -> tuple[np.ndarray, np.ndarray]:
    depths = np.zeros((len(bases), ambient_size), dtype=np.int16)
    for base_index, base in enumerate(bases):
        for number in range(base, ambient_size + 1, base):
            depths[base_index, number - 1] = positional_depth(base, number)
    scales = depths.astype(np.float64) * np.log(
        np.asarray(bases, dtype=np.float64)
    )[:, None]
    return depths, scales


def all_bases_weights(
    ambient_size: int,
) -> tuple[tuple[int, ...], np.ndarray, np.ndarray, np.ndarray]:
    bases = tuple(range(2, ambient_size + 1))
    depths, scales = depth_scale_table(ambient_size, bases)
    normalizer = np.sum(scales, axis=0, dtype=np.float64)
    weights = np.divide(
        scales,
        normalizer[None, :],
        out=np.zeros_like(scales),
        where=normalizer[None, :] > 0.0,
    )
    return bases, depths, scales, weights


def analysis_matrix(
    bases: Sequence[int], weights: np.ndarray
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return A and row labels (base, number); base 0 is the seed port."""
    ambient_size = weights.shape[1]
    active_base_indices, active_number_indices = np.nonzero(weights > 0.0)
    row_count = 1 + active_base_indices.size
    analysis = np.zeros((row_count, ambient_size), dtype=np.float64)
    row_bases = np.empty(row_count, dtype=np.int64)
    row_numbers = np.empty(row_count, dtype=np.int64)

    analysis[0, 0] = 1.0
    row_bases[0] = 0
    row_numbers[0] = 1
    rows = np.arange(1, row_count, dtype=np.int64)
    analysis[rows, active_number_indices] = np.sqrt(
        weights[active_base_indices, active_number_indices]
    )
    row_bases[rows] = np.asarray(bases, dtype=np.int64)[active_base_indices]
    row_numbers[rows] = active_number_indices + 1
    return analysis, row_bases, row_numbers


def frame_audit(
    analysis: np.ndarray,
    row_numbers: np.ndarray,
    ambient_size: int,
    time_value: float,
) -> dict[str, Any]:
    identity = np.eye(ambient_size, dtype=np.float64)
    frame_operator = analysis.T @ analysis
    frame_error = float(np.linalg.norm(frame_operator - identity, ord=2))

    state = collective.complex_state(time_value, ambient_size)
    observed = analysis @ state
    reconstructed = analysis.T @ observed
    state_energy = float(np.vdot(state, state).real)
    observed_energy = float(np.vdot(observed, observed).real)

    logarithms = np.log(np.arange(1, ambient_size + 1, dtype=np.float64))
    observed_logs = np.log(row_numbers.astype(np.float64))
    intertwining_error = float(
        np.linalg.norm(
            analysis * logarithms[None, :]
            - observed_logs[:, None] * analysis,
            ord=2,
        )
    )

    rng = np.random.default_rng(20260805)
    arbitrary = rng.normal(size=analysis.shape[0]) + 1j * rng.normal(
        size=analysis.shape[0]
    )
    projected = analysis @ (analysis.T @ arbitrary)
    projected_twice = analysis @ (analysis.T @ projected)
    coherent = analysis @ state
    coherent_projection = analysis @ (analysis.T @ coherent)

    return {
        "ambient_dimension": ambient_size,
        "atlas_channel_dimension": int(analysis.shape[0]),
        "rank_A": int(np.linalg.matrix_rank(analysis, tol=1.0e-12)),
        "A_star_A_minus_I_operator_norm": frame_error,
        "state_energy": state_energy,
        "atlas_energy": observed_energy,
        "energy_error": abs(state_energy - observed_energy),
        "reconstruction_error": float(np.linalg.norm(reconstructed - state)),
        "log_generator_intertwining_error": intertwining_error,
        "synchronization_projector": {
            "definition": "Pi_sync = A A*",
            "self_adjoint": True,
            "positive": True,
            "idempotence_error_on_random_vector": float(
                np.linalg.norm(projected_twice - projected)
            ),
            "coherent_state_fixed_point_error": float(
                np.linalg.norm(coherent_projection - coherent)
            ),
            "random_incompatibility_removed_norm": float(
                np.linalg.norm(arbitrary - projected)
            ),
        },
    }


def prime_subatlas_compatibility(
    ambient_size: int,
) -> dict[str, Any]:
    primes = tuple(number for number in range(2, ambient_size + 1) if is_prime(number))
    depths, scales = depth_scale_table(ambient_size, primes)
    del depths
    normalizer = np.sum(scales, axis=0, dtype=np.float64)
    logarithms = np.log(np.arange(1, ambient_size + 1, dtype=np.float64))
    error = np.abs(normalizer[1:] - logarithms[1:])
    return {
        "prime_count": len(primes),
        "maximum_log_factorization_error": float(np.max(error)),
        "identity": "sum_p v_p(n) log(p) = log(n)",
        "role": (
            "The prime valuation frame is recovered as a special subatlas. "
            "The conservative construction itself is defined for all bases."
        ),
    }


def horizontal_vertical_audit(
    source_bases: Sequence[int],
    weights: np.ndarray,
    all_bases: Sequence[int],
    analysis: np.ndarray,
    row_bases: np.ndarray,
    ambient_size: int,
    time_value: float,
) -> dict[str, Any]:
    state = collective.complex_state(time_value, ambient_size)
    numbers = np.arange(1, ambient_size + 1, dtype=np.int64)
    rows: list[dict[str, Any]] = []
    weight_sums = np.sum(weights, axis=0, dtype=np.float64)

    for source_base in source_bases:
        horizontal_mask = numbers % source_base != 0
        horizontal_state = state * horizontal_mask
        atlas_state = analysis @ horizontal_state
        boundary_energy = float(abs(horizontal_state[0]) ** 2)
        other_vertical_mask = (row_bases != 0) & (row_bases != source_base)
        other_vertical_energy = float(
            np.vdot(
                atlas_state[other_vertical_mask],
                atlas_state[other_vertical_mask],
            ).real
        )
        horizontal_energy = float(
            np.vdot(horizontal_state, horizontal_state).real
        )
        unresolved_numbers = [
            int(number)
            for number in numbers[horizontal_mask]
            if number > 1 and weight_sums[number - 1] == 0.0
        ]
        rows.append(
            {
                "source_base": int(source_base),
                "horizontal_energy": horizontal_energy,
                "vertical_energy_in_other_bases": other_vertical_energy,
                "seed_boundary_energy": boundary_energy,
                "ledger_error": abs(
                    horizontal_energy - other_vertical_energy - boundary_energy
                ),
                "unresolved_positive_integers_above_seed": unresolved_numbers,
            }
        )

    example_number = min(12, ambient_size)
    active_example = []
    for base_index, base in enumerate(all_bases):
        if weights[base_index, example_number - 1] > 0.0:
            active_example.append(
                {
                    "base": int(base),
                    "depth": positional_depth(int(base), example_number),
                    "weight": float(weights[base_index, example_number - 1]),
                }
            )

    return {
        "rows": rows,
        "exact_statement": (
            "For h in the horizontal complement of base b, all components n>1 "
            "are resolved by vertical channels of bases c != b. The n=1 seed "
            "remains an explicit boundary port."
        ),
        "example": {
            "number": example_number,
            "base_10_QR": (
                {
                    "quotient": example_number // 10,
                    "remainder": example_number % 10,
                }
                if ambient_size >= 12
                else None
            ),
            "active_vertical_cameras": active_example,
        },
    }


def local_tower_mass_audit(
    bases: Sequence[int], ambient_size: int
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    maximum_error = 0.0
    maximum_exponential_error = 0.0
    for base in bases:
        base_rows: list[dict[str, Any]] = []
        cores = [core for core in range(1, min(base + 3, ambient_size + 1)) if core % base]
        for core in cores:
            depth = 1
            while True:
                number = (base**depth) * core
                if number > ambient_size:
                    break
                x_vertical = depth * math.log(base)
                global_mass = 1.0 / number
                local_mass = (base ** (-depth)) / core
                exponential_mass = math.exp(-x_vertical) / core
                maximum_error = max(maximum_error, abs(global_mass - local_mass))
                maximum_exponential_error = max(
                    maximum_exponential_error,
                    abs(global_mass - exponential_mass),
                )
                base_rows.append(
                    {
                        "number": number,
                        "core": core,
                        "depth": depth,
                        "x_vertical": x_vertical,
                        "global_mass_1_over_n": global_mass,
                        "local_mass_b_to_minus_k_over_core": local_mass,
                    }
                )
                depth += 1
        rows.append({"base": int(base), "samples": base_rows})
    return {
        "maximum_mass_identity_error": maximum_error,
        "maximum_exp_minus_x_identity_error": maximum_exponential_error,
        "rows": rows,
        "identity": "1/n = b^(-k)/m = exp(-k log b)/m when n=b^k m",
    }


def qr_chart_audit(
    bases: Sequence[int], ambient_size: int, time_value: float
) -> dict[str, Any]:
    state = collective.complex_state(time_value, ambient_size)
    state_energy = float(np.vdot(state, state).real)
    rows: list[dict[str, Any]] = []
    for base in bases:
        cells: dict[tuple[int, int], complex] = {}
        for number in range(1, ambient_size + 1):
            cells[(number // base, number % base)] = state[number - 1]
        reconstructed = np.zeros_like(state)
        for (quotient, remainder), value in cells.items():
            number = base * quotient + remainder
            reconstructed[number - 1] = value
        chart_energy = float(sum(abs(value) ** 2 for value in cells.values()))
        rows.append(
            {
                "base": int(base),
                "chart_energy_error": abs(chart_energy - state_energy),
                "reconstruction_error": float(np.linalg.norm(reconstructed - state)),
                "unique_cell_count": len(cells),
            }
        )
    return {
        "rows": rows,
        "interpretation": (
            "The QR chart n <-> (q_b,r_b) is a relabelling of the same orthogonal "
            "number basis. Transition between bases preserves coefficients and norm."
        ),
    }


def native_bracket_routing_audit(
    models: Sequence[native.CameraModel],
    camera_matrix: np.ndarray,
    analysis: np.ndarray,
    all_bases: Sequence[int],
    weights: np.ndarray,
    ambient_size: int,
    time_value: float,
) -> dict[str, Any]:
    base_to_index = {base: index for index, base in enumerate(all_bases)}
    weight_sum = np.sum(weights, axis=0, dtype=np.float64)
    rows: list[dict[str, Any]] = []
    maximum_horizontal_routing_error = 0.0

    for model in models:
        data = collective.model_integer_data(model)
        horizontal_occurrences = 0
        boundary_occurrences = 0
        camera_maximum_error = 0.0
        for role in ("seed", "left", "right"):
            for raw_number in data[role]:
                number = int(raw_number)
                if number % model.camera == 0:
                    continue
                horizontal_occurrences += 1
                if number == 1:
                    boundary_occurrences += 1
                    continue
                source_weight = (
                    weights[base_to_index[model.camera], number - 1]
                    if model.camera in base_to_index
                    else 0.0
                )
                other_vertical_weight = weight_sum[number - 1] - source_weight
                error = abs(other_vertical_weight - 1.0)
                camera_maximum_error = max(camera_maximum_error, error)
                maximum_horizontal_routing_error = max(
                    maximum_horizontal_routing_error, error
                )
        rows.append(
            {
                "camera": model.camera,
                "horizontal_seed_leg_occurrences": horizontal_occurrences,
                "seed_boundary_occurrences_at_n_1": boundary_occurrences,
                "maximum_other_vertical_weight_error": camera_maximum_error,
            }
        )

    state = collective.complex_state(time_value, ambient_size)
    reconstructed = analysis.T @ (analysis @ state)
    native_before = camera_matrix @ state
    native_after = camera_matrix @ reconstructed
    atlas_readout = camera_matrix @ analysis.T
    atlas_state = analysis @ state
    atlas_native_resultant = atlas_readout @ atlas_state
    projected_readout = (atlas_readout @ analysis) @ analysis.T
    rng = np.random.default_rng(314159)
    arbitrary_atlas_state = rng.normal(size=analysis.shape[0]) + 1j * rng.normal(
        size=analysis.shape[0]
    )
    incoherent_atlas_state = arbitrary_atlas_state - analysis @ (
        analysis.T @ arbitrary_atlas_state
    )
    return {
        "rows": rows,
        "maximum_horizontal_routing_error": maximum_horizontal_routing_error,
        "state_reconstruction_error": float(np.linalg.norm(reconstructed - state)),
        "native_resultant_error_after_conservative_roundtrip": float(
            np.max(np.abs(native_after - native_before))
        ),
        "atlas_native_readout_error": float(
            np.max(np.abs(atlas_native_resultant - native_before))
        ),
        "readout_sync_projector_invariance_error": float(
            np.linalg.norm(projected_readout - atlas_readout, ord=2)
        ),
        "readout_of_incoherent_complement_norm": float(
            np.linalg.norm(atlas_readout @ incoherent_atlas_state)
        ),
        "interpretation": (
            "Native bracket legs remain labelled by n. Every horizontal leg n>1 "
            "is fully routed into vertical channels of other all-base cameras; n=1 "
            "is retained as a boundary/seed port."
        ),
    }


def coherent_fiber_vectors(weights: np.ndarray) -> np.ndarray:
    """Unit coherent direction a(n), including a separate n=1 seed axis."""
    ambient_size = weights.shape[1]
    fibers = np.zeros((ambient_size, weights.shape[0] + 1), dtype=np.float64)
    fibers[0, 0] = 1.0
    fibers[1:, 1:] = np.sqrt(weights[:, 1:].T)
    return fibers


def covariant_native_bracket_audit(
    models: Sequence[native.CameraModel],
    weights: np.ndarray,
    ambient_size: int,
    time_value: float,
    state_block: int,
) -> dict[str, Any]:
    """Lift native edge differences to the conservative coherent fibers."""
    fibers = coherent_fiber_vectors(weights)
    fiber_norm_errors = np.abs(
        np.sum(fibers * fibers, axis=1, dtype=np.float64) - 1.0
    )
    state = collective.complex_state(time_value, ambient_size)

    maximum_edge_synthesis_error = 0.0
    maximum_edge_energy_error = 0.0
    maximum_camera_resultant_error = 0.0
    rows: list[dict[str, Any]] = []

    for model in models:
        data = collective.model_integer_data(model)
        covariant_bracket_sum = 0.0 + 0.0j
        edge_energy = 0.0
        for left, center, right in zip(
            data["left"], data["center"], data["right"]
        ):
            center_index = int(center) - 1
            for endpoint in (int(left), int(right)):
                endpoint_index = endpoint - 1
                current = fibers[endpoint_index].astype(np.complex128) * (
                    state[endpoint_index] - state[center_index]
                )
                synthesized = np.vdot(fibers[endpoint_index], current)
                scalar_difference = state[endpoint_index] - state[center_index]
                maximum_edge_synthesis_error = max(
                    maximum_edge_synthesis_error,
                    float(abs(synthesized - scalar_difference)),
                )
                current_energy = float(np.vdot(current, current).real)
                scalar_energy = float(abs(scalar_difference) ** 2)
                maximum_edge_energy_error = max(
                    maximum_edge_energy_error,
                    abs(current_energy - scalar_energy),
                )
                edge_energy += current_energy
                covariant_bracket_sum += synthesized

        seed_sum = np.sum(state[data["seed"] - 1], dtype=np.complex128)
        covariant_resultant = seed_sum + covariant_bracket_sum
        native_balance = native.evaluate_camera_chunk_numpy(
            np.asarray([time_value], dtype=np.float64),
            model,
            state_block,
            return_balance=True,
        )
        native_xy = np.asarray(native_balance["resultant"], dtype=np.float64)[0]
        native_resultant = complex(float(native_xy[0]), float(native_xy[1]))
        error = float(abs(covariant_resultant - native_resultant))
        maximum_camera_resultant_error = max(maximum_camera_resultant_error, error)
        rows.append(
            {
                "camera": model.camera,
                "covariant_edge_energy": edge_energy,
                "covariant_resultant": [
                    float(covariant_resultant.real),
                    float(covariant_resultant.imag),
                ],
                "native_resultant": [
                    float(native_resultant.real),
                    float(native_resultant.imag),
                ],
                "resultant_error": error,
            }
        )

    test_numbers = sorted(
        set([1, min(2, ambient_size), min(3, ambient_size), min(12, ambient_size), ambient_size])
    )
    maximum_flatness_error = 0.0
    if len(test_numbers) >= 3:
        for first, middle, last in zip(
            test_numbers[:-2], test_numbers[1:-1], test_numbers[2:]
        ):
            a_first = fibers[first - 1]
            a_middle = fibers[middle - 1]
            a_last = fibers[last - 1]
            transport_first_middle = np.outer(a_middle, a_first)
            transport_middle_last = np.outer(a_last, a_middle)
            transport_first_last = np.outer(a_last, a_first)
            maximum_flatness_error = max(
                maximum_flatness_error,
                float(
                    np.linalg.norm(
                        transport_middle_last @ transport_first_middle
                        - transport_first_last,
                        ord=2,
                    )
                ),
            )

    return {
        "coherent_fiber": "a(n)=(sqrt(omega_b(n)))_b, with seed axis at n=1",
        "transport": "T_(u->v)=|a(v)><a(u)|",
        "covariant_difference": "nabla_A y(u,v)=y(v)-T_(u->v)y(u)",
        "maximum_fiber_unit_norm_error": float(np.max(fiber_norm_errors)),
        "maximum_transport_flatness_error": maximum_flatness_error,
        "maximum_edge_synthesis_error": maximum_edge_synthesis_error,
        "maximum_edge_energy_error": maximum_edge_energy_error,
        "maximum_native_camera_resultant_error": maximum_camera_resultant_error,
        "rows": rows,
        "identity": (
            "nabla_A(Af)(u,v)=a(v)(f(v)-f(u)); synthesizing the two "
            "center-to-leg currents gives f(c-r)-2f(c)+f(c+r)"
        ),
    }


def run_lab(args: argparse.Namespace) -> dict[str, Any]:
    source_cameras = native.parse_cameras(args.cameras)
    models = [
        native.build_camera_model(camera, args.cutoff)
        for camera in source_cameras
    ]
    camera_matrix, ambient_size = collective.native_readout_matrix(models)
    all_bases, depths, scales, weights = all_bases_weights(ambient_size)
    analysis, row_bases, row_numbers = analysis_matrix(all_bases, weights)

    weight_sums = np.sum(weights, axis=0, dtype=np.float64)
    all_base_normalizer = np.sum(scales, axis=0, dtype=np.float64)
    return {
        "schema": "org.native-carry.conservative-all-bases-atlas/v1",
        "status": "FINITE_CONSERVATIVE_ALL_BASES_AUDIT",
        "native_operator_authority": (
            "native_carry_primitive_real_operator_all_bases_fixed.py"
        ),
        "configuration": {
            "native_source_cameras": list(source_cameras),
            "native_cutoff": args.cutoff,
            "ambient_integer_maximum": ambient_size,
            "conservative_atlas_bases": [2, ambient_size],
            "time": args.time,
        },
        "proposed_all_bases_equalization": {
            "depth": "k_b(n)=max{k:b^k divides n}",
            "dimensionless_vertical_scale": "x_b(n)=k_b(n) log b",
            "weight": "omega_b(n)=x_b(n)/sum_c x_c(n)",
            "maximum_partition_of_unity_error_for_n_gt_1": float(
                np.max(np.abs(weight_sums[1:] - 1.0))
            ),
            "minimum_all_base_normalizer_ratio_to_log_n": float(
                np.min(
                    all_base_normalizer[1:]
                    / np.log(np.arange(2, ambient_size + 1, dtype=np.float64))
                )
            ),
            "maximum_active_depth": int(np.max(depths)),
            "warning": (
                "These weights conservatively equalize redundant all-base verticals. "
                "They do not alter native seeds, brackets, resultants, or scores."
            ),
        },
        "frame_and_synchronization": frame_audit(
            analysis, row_numbers, ambient_size, args.time
        ),
        "prime_subatlas_check": prime_subatlas_compatibility(ambient_size),
        "horizontal_to_other_verticals": horizontal_vertical_audit(
            source_cameras,
            weights,
            all_bases,
            analysis,
            row_bases,
            ambient_size,
            args.time,
        ),
        "local_vertical_mass": local_tower_mass_audit(
            source_cameras, ambient_size
        ),
        "qr_chart_unitarity": qr_chart_audit(
            source_cameras, ambient_size, args.time
        ),
        "native_bracket_routing": native_bracket_routing_audit(
            models,
            camera_matrix,
            analysis,
            all_bases,
            weights,
            ambient_size,
            args.time,
        ),
        "covariant_native_brackets": covariant_native_bracket_audit(
            models,
            weights,
            ambient_size,
            args.time,
            state_block=512,
        ),
        "conservative_system": {
            "state_space": "H_N = C^N (real lift H_N tensor R^2)",
            "log_generator": "L=diag(log n)=L*",
            "unitary_orbit": "U_t=exp(-itL)",
            "atlas_analysis": "A* A=I",
            "compatibility_projector": "Pi_sync=A A*",
            "native_ports_after_atlas": "C_native A*",
            "collective_visibility_on_atlas": "A C_native* C_native A*",
        },
        "infinite_limit_warning": (
            "The frame construction extends naturally to l2. The native critical "
            "amplitude n^(-1/2) is not globally in l2 because sum 1/n diverges, "
            "so its infinite realization needs a rigged/local-energy or renormalized setting."
        ),
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cameras", default="2,3,4,5,6,7")
    parser.add_argument("--cutoff", type=int, default=32)
    parser.add_argument("--time", type=float, default=14.134725141734695)
    parser.add_argument("--output", type=Path)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    if args.cutoff < 1:
        parser.error("cutoff must be positive")
    if not math.isfinite(args.time):
        parser.error("time must be finite")
    report = run_lab(args)
    payload = json.dumps(report, indent=2, sort_keys=True)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload + "\n", encoding="utf-8")
    print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
