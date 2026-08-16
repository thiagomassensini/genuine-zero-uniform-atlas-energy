#!/usr/bin/env python3
"""Identify the Pythagorean residual with native Green return ports.

The Pythagorean measure laboratory produces, for every active incidence
(b,n), the residual coefficient

    mu_R(b,n) = omega_b(n) (1-1/b).

Camera by camera this residual is not the two-dimensional affine return of a
long Green tower: their local ranks differ.  Globally, however, the coherent
residual fiber over a fixed integer n has rank one.  This script rotates that
fiber to the native depth-one node-output fiber

    q_c Gamma_out(c,n/c) = x_n,  k_c(n)=1.

Let rho(n)=sum_b mu_R(b,n) and
theta(n)=sum_{c:k_c(n)=1} omega_c(n).  Define

    (R_mu f)_(b,n) = sqrt(mu_R(b,n)) f(n),
    (O_node f)_(c,n)
      = sqrt(rho(n) omega_c(n)/theta(n)) f(n),  k_c(n)=1.

Then R_mu*R_mu=O_node*O_node=diag(rho), so their whitened analyses are
isometries and

    U_node = O_hat R_hat*

is the canonical partial isometry satisfying U_node R_mu=O_node.  It is
fiberwise in n, independent of t, and exactly intertwines log(n).

The native raw trace of a resolved tower follows from node values by the
fixed chart map

    (x_m,x_bm) -> (x_m, q_b**(-1)x_bm-x_m).

This map is not Euclidean-unitary, but it is unitary after whitening by the
metric induced by the native return synthesis q_b**k(a+k c).
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import native_carry_collective_operator_lab as collective
import native_carry_conservative_all_bases_atlas_lab as conservative
import native_carry_primitive_real_operator_all_bases_fixed as native
import native_carry_quadratic_weighted_green_atlas_lab as green


def parse_sizes(text: str) -> tuple[int, ...]:
    values = tuple(int(part.strip()) for part in text.split(",") if part.strip())
    if not values or any(value < 4 for value in values):
        raise ValueError("all sizes must be integers >= 4")
    return values


def positive_sqrt(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    if float(eigenvalues[0]) <= 0.0:
        raise RuntimeError("matrix must be positive definite")
    return (eigenvectors * np.sqrt(eigenvalues)[None, :]) @ eigenvectors.T


def build_residual_and_node_maps(
    size: int,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, dict[str, Any]]:
    bases, depths, _, weights = conservative.all_bases_weights(size)
    base_array = np.asarray(bases, dtype=np.float64)[:, None]
    residual_mass = np.sum(weights * (1.0 - 1.0 / base_array), axis=0)
    depth_one_mass = np.sum(weights * (depths == 1), axis=0)
    residual_mass[0] = 1.0
    depth_one_mass[0] = 1.0

    residual_rows: list[np.ndarray] = [
        np.eye(1, size, 0, dtype=np.float64)[0]
    ]
    residual_labels: list[int] = [1]
    node_rows: list[np.ndarray] = [np.eye(1, size, 0, dtype=np.float64)[0]]
    node_labels: list[int] = [1]

    for base_index, base in enumerate(bases):
        active_numbers = np.flatnonzero(depths[base_index] > 0) + 1
        for number in active_numbers:
            row = np.zeros(size, dtype=np.float64)
            row[number - 1] = math.sqrt(
                float(weights[base_index, number - 1])
                * (1.0 - 1.0 / float(base))
            )
            residual_rows.append(row)
            residual_labels.append(int(number))

        endpoint_numbers = np.flatnonzero(depths[base_index] == 1) + 1
        for number in endpoint_numbers:
            row = np.zeros(size, dtype=np.float64)
            row[number - 1] = math.sqrt(
                float(residual_mass[number - 1])
                * float(weights[base_index, number - 1])
                / float(depth_one_mass[number - 1])
            )
            node_rows.append(row)
            node_labels.append(int(number))

    residual = np.vstack(residual_rows)
    node = np.vstack(node_rows)
    metadata = {
        "residual_port_dimension": int(residual.shape[0]),
        "native_node_output_dimension": int(node.shape[0]),
        "minimum_residual_mass": float(np.min(residual_mass[1:])),
        "maximum_residual_mass": float(np.max(residual_mass[1:])),
        "minimum_depth_one_mass": float(np.min(depth_one_mass[1:])),
        "depth_one_lower_bound_pass": bool(
            np.min(depth_one_mass[1:]) + 1.0e-12 >= 1.0 / 3.0
        ),
    }
    return (
        residual,
        node,
        np.asarray(residual_labels, dtype=np.int64),
        np.asarray(node_labels, dtype=np.int64),
        {"residual_mass": residual_mass, **metadata},
    )


def local_rank_obstruction(size: int) -> dict[str, Any]:
    chart = green.build_tower_chart(2, size)
    core_one = next(numbers for core, numbers in chart.towers if core == 1)
    length = len(core_one)
    residual_rank = max(0, length - 1)
    native_return_rank = min(2, length)
    return {
        "base": 2,
        "tower_core": 1,
        "tower_length": length,
        "local_residual_rank": residual_rank,
        "native_affine_return_rank": native_return_rank,
        "local_unitary_possible": residual_rank == native_return_rank,
        "conclusion": (
            "For tower length >=4 the residual cannot equal the affine Green "
            "return camera by camera. The valid identification must first "
            "glue equal integer labels across cameras."
        ),
    }


def native_trace_return_audit(
    size: int,
    reconstructed_state: np.ndarray,
) -> dict[str, Any]:
    maximum_trace_error = 0.0
    maximum_return_error = 0.0
    maximum_metric_unitary_error = 0.0
    maximum_raw_euclidean_unitary_error = 0.0
    resolved_tower_count = 0
    singleton_count = 0

    for base in range(2, size + 1):
        chart = green.build_tower_chart(base, size)
        trace_mask = np.asarray(
            [kind != "bulk" for kind in chart.raw_port_kinds], dtype=bool
        )
        trace = chart.analysis_raw[trace_mask]
        return_synthesis = chart.synthesis_raw[:, trace_mask]
        maximum_trace_error = max(
            maximum_trace_error,
            float(np.linalg.norm(trace @ reconstructed_state - trace, ord=2)),
        )
        native_return = return_synthesis @ trace
        maximum_return_error = max(
            maximum_return_error,
            float(
                np.linalg.norm(
                    native_return @ reconstructed_state - native_return,
                    ord=2,
                )
            ),
        )

        for _, numbers in chart.towers:
            length = len(numbers)
            if length < 2:
                singleton_count += 1
                continue
            resolved_tower_count += 1
            _, block_synthesis, _, _, _ = green.weighted_tfvd_block(
                length, chart.q
            )
            affine_return = block_synthesis[:, -2:]
            node_to_trace = np.asarray(
                [[1.0, 0.0], [-1.0, 1.0 / chart.q]], dtype=np.float64
            )
            raw_error = np.linalg.norm(
                node_to_trace.T @ node_to_trace - np.eye(2), ord=2
            )
            maximum_raw_euclidean_unitary_error = max(
                maximum_raw_euclidean_unitary_error, float(raw_error)
            )

            trace_metric = affine_return.T @ affine_return
            node_metric = node_to_trace.T @ trace_metric @ node_to_trace
            whitened_chart = (
                positive_sqrt(trace_metric)
                @ node_to_trace
                @ np.linalg.inv(positive_sqrt(node_metric))
            )
            metric_error = np.linalg.norm(
                whitened_chart.T @ whitened_chart - np.eye(2), ord=2
            )
            maximum_metric_unitary_error = max(
                maximum_metric_unitary_error, float(metric_error)
            )

    return {
        "resolved_tower_count": resolved_tower_count,
        "singleton_tower_count": singleton_count,
        "maximum_native_trace_reconstruction_error": maximum_trace_error,
        "maximum_native_return_reconstruction_error": maximum_return_error,
        "maximum_raw_node_to_trace_euclidean_unitarity_defect": (
            maximum_raw_euclidean_unitary_error
        ),
        "maximum_whitened_node_to_trace_unitarity_error": (
            maximum_metric_unitary_error
        ),
        "node_to_trace": (
            "C_b=[[1,0],[-1,q_b^(-1)]], sending "
            "(x_m,x_bm) to (x_m,q_b^(-1)x_bm-x_m)"
        ),
        "metric_statement": (
            "C_b is not Euclidean-unitary. It is an isometry from the node "
            "metric C_b* R_b*R_b C_b to the native trace metric R_b*R_b; "
            "after whitening its polar representative is unitary."
        ),
    }


def one_size_audit(size: int) -> dict[str, Any]:
    residual, node, residual_labels, node_labels, metadata = (
        build_residual_and_node_maps(size)
    )
    residual_mass = np.asarray(metadata.pop("residual_mass"), dtype=np.float64)
    inverse_mass_sqrt = np.diag(1.0 / np.sqrt(residual_mass))
    residual_isometry = residual @ inverse_mass_sqrt
    node_isometry = node @ inverse_mass_sqrt
    identification = node_isometry @ residual_isometry.T

    residual_log = np.diag(np.log(residual_labels.astype(np.float64)))
    node_log = np.diag(np.log(node_labels.astype(np.float64)))
    node_synthesis = np.linalg.pinv(node, rcond=1.0e-12)
    reconstructed_state = node_synthesis @ identification @ residual

    return {
        "ambient_dimension": size,
        **metadata,
        "local_rank_obstruction": local_rank_obstruction(size),
        "residual_gram_to_node_gram_error": float(
            np.linalg.norm(residual.T @ residual - node.T @ node, ord=2)
        ),
        "residual_whitened_isometry_error": float(
            np.linalg.norm(
                residual_isometry.T @ residual_isometry - np.eye(size), ord=2
            )
        ),
        "node_whitened_isometry_error": float(
            np.linalg.norm(
                node_isometry.T @ node_isometry - np.eye(size), ord=2
            )
        ),
        "U_node_R_mu_minus_O_node_error": float(
            np.linalg.norm(identification @ residual - node, ord=2)
        ),
        "log_generator_intertwining_error": float(
            np.linalg.norm(
                node_log @ identification - identification @ residual_log,
                ord=2,
            )
        ),
        "state_reconstruction_through_identification_error": float(
            np.linalg.norm(reconstructed_state - np.eye(size), ord=2)
        ),
        "native_trace_and_return": native_trace_return_audit(
            size, reconstructed_state
        ),
    }


def native_characteristic_audit(
    cameras_text: str, cutoff: int, time_value: float
) -> dict[str, Any]:
    cameras = native.parse_cameras(cameras_text)
    models = [native.build_camera_model(camera, cutoff) for camera in cameras]
    camera_matrix, size = collective.native_readout_matrix(models)
    residual, node, residual_labels, node_labels, metadata = (
        build_residual_and_node_maps(size)
    )
    residual_mass = np.asarray(metadata["residual_mass"], dtype=np.float64)
    inverse_mass_sqrt = np.diag(1.0 / np.sqrt(residual_mass))
    residual_isometry = residual @ inverse_mass_sqrt
    node_isometry = node @ inverse_mass_sqrt
    identification = node_isometry @ residual_isometry.T
    node_synthesis = np.linalg.pinv(node, rcond=1.0e-12)
    reconstructed_state = node_synthesis @ identification @ residual

    state = collective.complex_state(time_value, size)
    direct = camera_matrix @ state
    through_return = camera_matrix @ reconstructed_state @ state
    residual_log = np.diag(np.log(residual_labels.astype(np.float64)))
    node_log = np.diag(np.log(node_labels.astype(np.float64)))
    return {
        "source_cameras": list(cameras),
        "native_cutoff": cutoff,
        "ambient_dimension": size,
        "time": time_value,
        "readout_operator_preservation_error": float(
            np.linalg.norm(
                camera_matrix @ reconstructed_state - camera_matrix, ord=2
            )
        ),
        "native_characteristic_preservation_error": float(
            np.linalg.norm(through_return - direct)
        ),
        "log_generator_intertwining_error": float(
            np.linalg.norm(
                node_log @ identification - identification @ residual_log,
                ord=2,
            )
        ),
        "interpretation": (
            "The residual-to-node identification followed by native node "
            "synthesis is the identity on the integer state. Therefore every "
            "native camera resultant and its entire logarithmic orbit are "
            "preserved, not only the sampled time."
        ),
    }


def run_lab(args: argparse.Namespace) -> dict[str, Any]:
    sizes = parse_sizes(args.sizes)
    return {
        "schema": "org.native-carry.residual-native-return-identification/v1",
        "status": "GLOBAL_COHERENT_IDENTIFICATION_EXACT_LOCAL_IDENTIFICATION_FALSE",
        "native_operator_authority": (
            "native_carry_primitive_real_operator_all_bases_fixed.py"
        ),
        "identification": {
            "residual": (
                "R_mu(b,n)=sqrt(omega_b(n)(1-1/b)) f(n)"
            ),
            "depth_one_mass": (
                "theta(n)=sum_(c:k_c(n)=1) omega_c(n), theta(n)>=1/3"
            ),
            "native_node_output": (
                "O_node(c,n)=sqrt(rho(n)omega_c(n)/theta(n)) "
                "q_c Gamma_out(c,n/c), with q_c Gamma_out=x_n"
            ),
            "common_gram": "R_mu*R_mu=O_node*O_node=diag(rho)",
            "partial_isometry": "U_node=O_hat R_hat*",
            "exact_relation": "U_node R_mu=O_node",
            "unitary_extension": (
                "After adjoining orthogonal gauge channels so the two port "
                "spaces have equal dimension, U_node extends to a unitary."
            ),
            "time_independence": True,
            "log_intertwining": "L_node U_node=U_node L_residual",
        },
        "boundary_chart": {
            "resolved_tower": "n=bm with b not dividing m",
            "native_node_pair": "(Gamma_in,q_b Gamma_out)=(x_m,x_bm)",
            "raw_trace": "(x_m,q_b^(-1)x_bm-x_m)",
            "raw_chart_change": "C_b=[[1,0],[-1,q_b^(-1)]]",
            "unitarity": (
                "not Euclidean in raw coordinates; exactly unitary after "
                "whitening by the metric induced by q_b^k(a+k c)"
            ),
        },
        "interpretation": {
            "negative_local_result": (
                "mu_R is not the affine return of each tower separately; "
                "tower ranks obstruct that statement."
            ),
            "positive_global_result": (
                "After arithmetic gluing by the integer label n, mu_R is "
                "canonically equivalent to the coherent native node-return "
                "outputs. Those node values reconstruct every resolved raw "
                "Green trace and its affine return."
            ),
            "singleton_ports": (
                "At finite cutoff, unresolved outputs use the already-defined "
                "external integer nodes. In the infinite limit every fixed "
                "target is included by the same fiberwise rule."
            ),
        },
        "native_characteristic_audit": native_characteristic_audit(
            args.cameras, args.cutoff, args.time
        ),
        "size_audits": [one_size_audit(size) for size in sizes],
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sizes", default="8,16,32,64,128")
    parser.add_argument("--cameras", default="2,3,4,5,6,7")
    parser.add_argument("--cutoff", type=int, default=32)
    parser.add_argument("--time", type=float, default=14.134725141734695)
    parser.add_argument("--output", type=Path)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    try:
        if args.cutoff < 1:
            raise ValueError("cutoff must be positive")
        if not math.isfinite(args.time):
            raise ValueError("time must be finite")
        report = run_lab(args)
    except ValueError as exc:
        parser.error(str(exc))
    payload = json.dumps(report, indent=2, sort_keys=True)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload + "\n", encoding="utf-8")
    print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
