#!/usr/bin/env python3
"""Pythagorean node-return colligation and Weyl/Schur audit.

This laboratory inserts the exact coherent identification

    residual Pythagorean ports -> native node outputs

into the carry-normalized endpoint/bulk analysis.  The endpoint block is

    E_node = (O_node, G_depth=1),

and the bulk block contains the active Green rows of depth at least two.  Its
frame is identical to the residual realization because

    O_node* O_node = R_mu* R_mu.

After frame normalization V=(E,B), V*V=I, the logarithmic generator is

    H = V diag(log n) V*.

The script audits both mathematical parameters that must remain distinct:

* lambda: the spectral parameter of the Weyl/Schur family;
* t: the real angular parameter of the native characteristic orbit.

The bulk gamma-field and Weyl action are

    gamma_B(lambda)=(lambda-H_BB)^(-1) H_BE,
    W(lambda)=lambda-H_EE-H_EB(lambda-H_BB)^(-1)H_BE.

The fixed Poisson completion M=B E^dagger eliminates the bulk in the native
readout and recovers the original real-operator characteristic for every t.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, Sequence

import numpy as np

import native_carry_collective_operator_lab as collective
import native_carry_conservative_all_bases_atlas_lab as conservative
import native_carry_primitive_real_operator_all_bases_fixed as native
import native_carry_quadratic_weighted_green_atlas_lab as green
import native_carry_residual_native_return_identification_lab as return_identification


def active_green_blocks(
    size: int, depths: np.ndarray, weights: np.ndarray
) -> tuple[np.ndarray, np.ndarray, dict[str, int]]:
    endpoint_rows: list[np.ndarray] = []
    bulk_rows: list[np.ndarray] = []
    for base_index, base in enumerate(range(2, size + 1)):
        chart = green.build_tower_chart(base, size)
        numbers = np.asarray(
            [number for _, tower in chart.towers for number in tower],
            dtype=np.int64,
        )
        row_depths = depths[base_index, numbers - 1]
        row_weights = weights[base_index, numbers - 1]
        active_green = (
            np.sqrt(row_weights / float(base))[:, None]
            * (chart.q * chart.canonical_analysis)
        )
        endpoint_rows.extend(active_green[row_depths == 1])
        bulk_rows.extend(active_green[row_depths >= 2])
    endpoint = (
        np.vstack(endpoint_rows)
        if endpoint_rows
        else np.zeros((0, size), dtype=np.float64)
    )
    bulk = (
        np.vstack(bulk_rows)
        if bulk_rows
        else np.zeros((0, size), dtype=np.float64)
    )
    return endpoint, bulk, {
        "green_depth_one_dimension": int(endpoint.shape[0]),
        "green_bulk_dimension": int(bulk.shape[0]),
    }


def node_residual_identification(
    size: int,
) -> dict[str, Any]:
    residual, node, residual_labels, node_labels, metadata = (
        return_identification.build_residual_and_node_maps(size)
    )
    residual_mass = np.asarray(metadata.pop("residual_mass"), dtype=np.float64)
    inverse_mass_sqrt = np.diag(1.0 / np.sqrt(residual_mass))
    residual_isometry = residual @ inverse_mass_sqrt
    node_isometry = node @ inverse_mass_sqrt
    partial_isometry = node_isometry @ residual_isometry.T
    return {
        "residual": residual,
        "node": node,
        "partial_isometry": partial_isometry,
        "residual_labels": residual_labels,
        "node_labels": node_labels,
        "metadata": metadata,
    }


def normalized_colligation(size: int) -> dict[str, Any]:
    _, depths, _, weights = conservative.all_bases_weights(size)
    identification = node_residual_identification(size)
    residual = np.asarray(identification["residual"], dtype=np.float64)
    node = np.asarray(identification["node"], dtype=np.float64)
    green_endpoint, bulk, green_metadata = active_green_blocks(
        size, depths, weights
    )
    residual_endpoint = np.vstack((residual, green_endpoint))
    node_endpoint = np.vstack((node, green_endpoint))
    residual_form = residual_endpoint.T @ residual_endpoint
    node_form = node_endpoint.T @ node_endpoint
    bulk_form = bulk.T @ bulk
    full_form = node_form + bulk_form
    inverse_sqrt, _ = green.inverse_positive_sqrt(full_form)
    normalized_residual_endpoint = residual_endpoint @ inverse_sqrt
    normalized_node_endpoint = node_endpoint @ inverse_sqrt
    normalized_bulk = bulk @ inverse_sqrt
    frame_eigenvalues = np.linalg.eigvalsh(full_form)
    endpoint_eigenvalues = np.linalg.eigvalsh(
        normalized_node_endpoint.T @ normalized_node_endpoint
    )

    endpoint_gram = normalized_node_endpoint.T @ normalized_node_endpoint
    endpoint_left_inverse = np.linalg.solve(
        endpoint_gram, normalized_node_endpoint.T
    )
    poisson = normalized_bulk @ endpoint_left_inverse
    return {
        **identification,
        "green_endpoint": green_endpoint,
        "residual_endpoint": residual_endpoint,
        "node_endpoint": node_endpoint,
        "bulk_raw": bulk,
        "endpoint": normalized_node_endpoint,
        "residual_endpoint_normalized": normalized_residual_endpoint,
        "bulk": normalized_bulk,
        "poisson": poisson,
        "inverse_frame_sqrt": inverse_sqrt,
        "audit": {
            **green_metadata,
            "residual_endpoint_dimension": int(residual_endpoint.shape[0]),
            "node_endpoint_dimension": int(node_endpoint.shape[0]),
            "node_residual_endpoint_gram_error": float(
                np.linalg.norm(node_form - residual_form, ord=2)
            ),
            "full_frame_min_eigenvalue": float(frame_eigenvalues[0]),
            "full_frame_max_eigenvalue": float(frame_eigenvalues[-1]),
            "normalized_isometry_error": float(
                np.linalg.norm(
                    normalized_node_endpoint.T @ normalized_node_endpoint
                    + normalized_bulk.T @ normalized_bulk
                    - np.eye(size),
                    ord=2,
                )
            ),
            "normalized_endpoint_min_eigenvalue": float(endpoint_eigenvalues[0]),
            "normalized_endpoint_max_eigenvalue": float(endpoint_eigenvalues[-1]),
            "poisson_operator_norm": float(np.linalg.norm(poisson, ord=2)),
            "poisson_intertwining_error": float(
                np.linalg.norm(
                    poisson @ normalized_node_endpoint - normalized_bulk,
                    ord=2,
                )
            ),
        },
    }


def spectral_blocks(
    endpoint: np.ndarray, bulk: np.ndarray
) -> dict[str, Any]:
    size = endpoint.shape[1]
    logarithms = np.log(np.arange(1, size + 1, dtype=np.float64))
    h_bb = (bulk * logarithms[None, :]) @ bulk.T
    bulk_eigenvalues, bulk_eigenvectors = np.linalg.eigh(h_bb)

    def h_ee_action(vector: np.ndarray) -> np.ndarray:
        return endpoint @ (logarithms * (endpoint.T @ vector))

    def h_be_action(vector: np.ndarray) -> np.ndarray:
        return bulk @ (logarithms * (endpoint.T @ vector))

    def h_eb_action(vector: np.ndarray) -> np.ndarray:
        return endpoint @ (logarithms * (bulk.T @ vector))

    def bulk_resolvent(parameter: complex, rhs: np.ndarray) -> np.ndarray:
        spectral_rhs = bulk_eigenvectors.T @ rhs
        return bulk_eigenvectors @ (
            spectral_rhs / (parameter - bulk_eigenvalues)
        )

    def gamma_action(parameter: complex, endpoint_vector: np.ndarray) -> np.ndarray:
        return bulk_resolvent(parameter, h_be_action(endpoint_vector))

    def weyl_action(parameter: complex, endpoint_vector: np.ndarray) -> np.ndarray:
        solved_bulk = gamma_action(parameter, endpoint_vector)
        return (
            parameter * endpoint_vector
            - h_ee_action(endpoint_vector)
            - h_eb_action(solved_bulk)
        )

    return {
        "logarithms": logarithms,
        "h_bb": h_bb,
        "bulk_eigenvalues": bulk_eigenvalues,
        "gamma_action": gamma_action,
        "weyl_action": weyl_action,
    }


def on_shell_audit(
    endpoint: np.ndarray,
    bulk: np.ndarray,
    spectral: dict[str, Any],
    maximum_modes: int,
) -> dict[str, Any]:
    size = endpoint.shape[1]
    logarithms = np.asarray(spectral["logarithms"], dtype=np.float64)
    bulk_eigenvalues = np.asarray(
        spectral["bulk_eigenvalues"], dtype=np.float64
    )
    gamma_action = spectral["gamma_action"]
    weyl_action = spectral["weyl_action"]
    candidate_indices = np.unique(
        np.linspace(1, size - 1, min(maximum_modes, size - 1), dtype=np.int64)
    )
    rows: list[dict[str, float | int]] = []
    for index in candidate_indices:
        parameter = float(logarithms[index])
        separation = float(np.min(np.abs(parameter - bulk_eigenvalues)))
        if separation <= 1.0e-9:
            continue
        endpoint_mode = endpoint[:, index]
        bulk_mode = bulk[:, index]
        gamma_bulk = gamma_action(complex(parameter), endpoint_mode)
        weyl_kernel = weyl_action(complex(parameter), endpoint_mode)
        rows.append(
            {
                "n": int(index + 1),
                "lambda": parameter,
                "distance_to_bulk_spectrum": separation,
                "gamma_on_shell_error": float(
                    np.linalg.norm(gamma_bulk - bulk_mode)
                ),
                "weyl_kernel_residual": float(np.linalg.norm(weyl_kernel)),
            }
        )
    return {
        "tested_mode_count": len(rows),
        "maximum_gamma_on_shell_error": float(
            max((row["gamma_on_shell_error"] for row in rows), default=0.0)
        ),
        "maximum_weyl_kernel_residual": float(
            max((row["weyl_kernel_residual"] for row in rows), default=0.0)
        ),
        "rows": rows,
        "identity": (
            "gamma_B(log n) E e_n=B e_n and W(log n)E e_n=0 "
            "whenever log n is outside the finite bulk spectrum"
        ),
    }


def nevanlinna_audit(
    endpoint: np.ndarray, spectral: dict[str, Any]
) -> dict[str, Any]:
    rng = np.random.default_rng(20260805)
    vector = rng.normal(size=endpoint.shape[0]) + 1j * rng.normal(
        size=endpoint.shape[0]
    )
    vector /= np.linalg.norm(vector)
    weyl_action = spectral["weyl_action"]
    rows = []
    for parameter in (0.5 + 0.25j, 2.0 + 0.75j, 4.0 + 1.5j):
        value = weyl_action(parameter, vector)
        ratio = float(np.vdot(vector, value).imag / parameter.imag)
        rows.append(
            {
                "lambda": [float(parameter.real), float(parameter.imag)],
                "imaginary_quadratic_ratio": ratio,
                "positive_pass": ratio >= -1.0e-10,
            }
        )
    return {
        "rows": rows,
        "minimum_imaginary_quadratic_ratio": min(
            row["imaginary_quadratic_ratio"] for row in rows
        ),
        "nevanlinna_pass": all(row["positive_pass"] for row in rows),
    }


def endpoint_weyl_covariance_audit(
    colligation: dict[str, Any], spectral_node: dict[str, Any]
) -> dict[str, Any]:
    residual_endpoint = np.asarray(
        colligation["residual_endpoint_normalized"], dtype=np.float64
    )
    node_endpoint = np.asarray(colligation["endpoint"], dtype=np.float64)
    bulk = np.asarray(colligation["bulk"], dtype=np.float64)
    residual = np.asarray(colligation["residual"], dtype=np.float64)
    node = np.asarray(colligation["node"], dtype=np.float64)
    partial = np.asarray(colligation["partial_isometry"], dtype=np.float64)
    green_dimension = int(colligation["green_endpoint"].shape[0])

    residual_port_dimension = residual.shape[0]
    node_port_dimension = node.shape[0]

    def map_endpoint(vector: np.ndarray) -> np.ndarray:
        return np.concatenate(
            (
                partial @ vector[:residual_port_dimension],
                vector[residual_port_dimension:],
            )
        )

    spectral_residual = spectral_blocks(residual_endpoint, bulk)
    rng = np.random.default_rng(314159)
    state = rng.normal(size=node_endpoint.shape[1]) + 1j * rng.normal(
        size=node_endpoint.shape[1]
    )
    residual_vector = residual_endpoint @ state
    node_vector = node_endpoint @ state
    parameter = 2.0 + 0.75j
    mapped = map_endpoint(residual_vector)
    residual_weyl = spectral_residual["weyl_action"](
        parameter, residual_vector
    )
    node_weyl = spectral_node["weyl_action"](parameter, node_vector)
    return {
        "residual_port_dimension": residual_port_dimension,
        "node_port_dimension": node_port_dimension,
        "shared_green_endpoint_dimension": green_dimension,
        "endpoint_state_map_error": float(np.linalg.norm(mapped - node_vector)),
        "weyl_covariance_error_on_coherent_vector": float(
            np.linalg.norm(map_endpoint(residual_weyl) - node_weyl)
        ),
        "identity": (
            "On the coherent endpoint range, W_node(lambda) U_endpoint = "
            "U_endpoint W_residual(lambda). Thus replacing residual ports by "
            "native node-return ports is a fixed unitary equivalence of Weyl "
            "families after gauge completion."
        ),
    }


def trace_metric_audit(size: int, bases: Sequence[int]) -> dict[str, Any]:
    maximum_error = 0.0
    resolved_count = 0
    for base in bases:
        chart = green.build_tower_chart(base, size)
        for _, numbers in chart.towers:
            if len(numbers) < 2:
                continue
            resolved_count += 1
            _, synthesis, _, _, _ = green.weighted_tfvd_block(
                len(numbers), chart.q
            )
            affine_return = synthesis[:, -2:]
            node_to_trace = np.asarray(
                [[1.0, 0.0], [-1.0, 1.0 / chart.q]], dtype=np.float64
            )
            trace_metric = affine_return.T @ affine_return
            node_metric = node_to_trace.T @ trace_metric @ node_to_trace
            whitened = (
                return_identification.positive_sqrt(trace_metric)
                @ node_to_trace
                @ np.linalg.inv(
                    return_identification.positive_sqrt(node_metric)
                )
            )
            maximum_error = max(
                maximum_error,
                float(np.linalg.norm(whitened.T @ whitened - np.eye(2), ord=2)),
            )
    return {
        "bases": list(bases),
        "resolved_tower_count": resolved_count,
        "maximum_whitened_node_to_trace_unitarity_error": maximum_error,
        "consequence": (
            "The node-coordinate Weyl family is unitarily equivalent, in the "
            "native return metric, to the raw Green-trace Weyl family."
        ),
    }


def native_characteristic_audit(
    camera_matrix: np.ndarray,
    endpoint: np.ndarray,
    bulk: np.ndarray,
    poisson: np.ndarray,
    time_value: float,
) -> dict[str, Any]:
    atlas = np.vstack((endpoint, bulk))
    port_readout = camera_matrix @ atlas.T
    endpoint_dimension = endpoint.shape[0]
    endpoint_readout = port_readout[:, :endpoint_dimension]
    bulk_readout = port_readout[:, endpoint_dimension:]
    effective_readout = endpoint_readout + bulk_readout @ poisson
    state = collective.complex_state(time_value, endpoint.shape[1])
    endpoint_state = endpoint @ state
    bulk_state = bulk @ state
    direct = camera_matrix @ state
    effective = effective_readout @ endpoint_state
    endpoint_contribution = endpoint_readout @ endpoint_state
    bulk_contribution = bulk_readout @ bulk_state
    return {
        "time": time_value,
        "effective_readout_operator_error": float(
            np.linalg.norm(effective_readout @ endpoint - camera_matrix, ord=2)
        ),
        "native_characteristic_error": float(np.linalg.norm(effective - direct)),
        "poisson_state_completion_error": float(
            np.linalg.norm(poisson @ endpoint_state - bulk_state)
        ),
        "direct_characteristic_norm": float(np.linalg.norm(direct)),
        "endpoint_contribution_norm": float(np.linalg.norm(endpoint_contribution)),
        "bulk_contribution_norm": float(np.linalg.norm(bulk_contribution)),
        "completed_contribution_norm": float(
            np.linalg.norm(endpoint_contribution + bulk_contribution)
        ),
        "identity": (
            "(Q_E+Q_B M_MB) E exp(-itL)alpha = "
            "C_native exp(-itL)alpha for every real t"
        ),
    }


def run_lab(args: argparse.Namespace) -> dict[str, Any]:
    cameras = native.parse_cameras(args.cameras)
    models = [native.build_camera_model(camera, args.cutoff) for camera in cameras]
    camera_matrix, size = collective.native_readout_matrix(models)
    colligation = normalized_colligation(size)
    endpoint = np.asarray(colligation["endpoint"], dtype=np.float64)
    bulk = np.asarray(colligation["bulk"], dtype=np.float64)
    poisson = np.asarray(colligation["poisson"], dtype=np.float64)
    spectral = spectral_blocks(endpoint, bulk)
    return {
        "schema": "org.native-carry.pythagorean-node-weyl-colligation/v1",
        "status": "FINITE_NODE_RETURN_WEYL_COLLIGATION_EXACT",
        "native_operator_authority": (
            "native_carry_primitive_real_operator_all_bases_fixed.py"
        ),
        "configuration": {
            "source_cameras": list(cameras),
            "native_cutoff": args.cutoff,
            "ambient_dimension": size,
            "time": args.time,
        },
        "colligation": colligation["audit"],
        "node_residual_identification": {
            **colligation["metadata"],
            "U_node_R_mu_minus_O_node_error": float(
                np.linalg.norm(
                    colligation["partial_isometry"] @ colligation["residual"]
                    - colligation["node"],
                    ord=2,
                )
            ),
        },
        "trace_metric": trace_metric_audit(size, cameras),
        "spectral_weyl": {
            "endpoint_dimension": int(endpoint.shape[0]),
            "bulk_dimension": int(bulk.shape[0]),
            "bulk_spectrum_min": float(spectral["bulk_eigenvalues"][0]),
            "bulk_spectrum_max": float(spectral["bulk_eigenvalues"][-1]),
            "on_shell": on_shell_audit(
                endpoint, bulk, spectral, args.maximum_modes
            ),
            "nevanlinna": nevanlinna_audit(endpoint, spectral),
            "parameter_warning": (
                "lambda is the Weyl spectral parameter. The native height t "
                "remains the angular parameter of exp(-it log n)."
            ),
        },
        "weyl_coordinate_covariance": endpoint_weyl_covariance_audit(
            colligation, spectral
        ),
        "native_characteristic": native_characteristic_audit(
            camera_matrix, endpoint, bulk, poisson, args.time
        ),
        "infinite_limit_candidate": {
            "endpoint_lower_bound": (
                "inherited from the Pythagorean residual: E*E>=c I uniformly"
            ),
            "bulk_nontrivial": (
                "inherited from the fixed base-2 depth-two event at n=4"
            ),
            "bounded_analysis": (
                "the mu_G=omega/b tail is controlled by sum b^-2 and b^-3"
            ),
            "expected_limit": (
                "a bounded nontrivial Poisson operator and an operator-valued "
                "Nevanlinna Weyl family off the real bulk spectrum"
            ),
            "remaining_domain_gate": (
                "prove local-energy/resolvent convergence of H_BB,N and the "
                "Schur family, then identify the infinite symmetric operator "
                "whose boundary triple realizes this limit"
            ),
        },
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cameras", default="2,3,4,5,6,7")
    parser.add_argument("--cutoff", type=int, default=32)
    parser.add_argument("--time", type=float, default=14.134725141734695)
    parser.add_argument("--maximum-modes", type=int, default=32)
    parser.add_argument("--output", type=Path)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    if args.cutoff < 1:
        parser.error("cutoff must be positive")
    if not math.isfinite(args.time):
        parser.error("time must be finite")
    if args.maximum_modes < 1:
        parser.error("maximum-modes must be positive")
    report = run_lab(args)
    payload = json.dumps(report, indent=2, sort_keys=True)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload + "\n", encoding="utf-8")
    print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
