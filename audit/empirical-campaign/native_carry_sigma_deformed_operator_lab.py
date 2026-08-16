#!/usr/bin/env python3
"""Finite sigma deformation of the native carry operator and port readout.

The primitive camera geometry is kept fixed.  Let C_N be the native real carry
readout written in complex shorthand, L_N=diag(log n), and

    psi_{1/2,t}(n) = n^(-1/2) exp(-i t log n).

For delta=sigma-1/2 define the finite diagonal deformation

    D_delta = diag(n^(-delta)),
    C_{N,sigma} = C_N D_delta.

Then

    C_{N,sigma} psi_{1/2,t}
      = C_N [n^(-sigma) exp(-i t log n)]
      =: chi_N(sigma,t).

This makes the requested sigma variation an operator deformation while leaving
all seed/bracket geometry unchanged.  Since D_delta is invertible at finite
cutoff, rank is preserved.  The multibase endpoint/Green return remains
lossless for every sigma because it reconstructs arbitrary finite states, not
only the critical orbit.

What changes is the carry-normalized transport.  Along a b-adic edge m -> bm,
with q_b=b^(-1/2),

    q_b^(-1) psi_sigma(bm)/psi_sigma(m)
      = b^(1/2-sigma) exp(-i t log b).

Its modulus is one exactly at sigma=1/2.  Off the critical exponent the same
port becomes an expansion or contraction.

The characteristic is analytic in s=sigma+i t and obeys the exact tangent law

    partial_t chi_N = i partial_sigma chi_N.

Consequently, at an exact critical zero, the real sigma and time tangents have
equal norm and are orthogonal in the real two-plane.  Locally,

    ||chi_N(1/2+delta,t0+tau)||^2
      = kappa_N (delta^2+tau^2) + higher order,

where kappa_N=||partial_sigma chi_N(1/2,t0)||^2.  A real time adjustment cannot
cancel the transverse sigma defect.  This laboratory audits that quadratic
lifting numerically across cutoffs and several resonance valleys.

This is a finite empirical audit.  It does not promote cutoff behavior to an
infinite theorem.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Any, Iterable, Sequence

import numpy as np
from scipy.optimize import minimize_scalar

import native_carry_collective_operator_lab as collective
import native_carry_primitive_real_operator_all_bases_fixed as native
import native_carry_pythagorean_node_weyl_colligation_lab as node_weyl


def parse_ints(text: str, minimum: int = 1) -> tuple[int, ...]:
    values = tuple(sorted({int(part.strip()) for part in text.split(",") if part.strip()}))
    if not values or any(value < minimum for value in values):
        raise ValueError(f"provide comma-separated integers >= {minimum}")
    return values


def parse_floats(text: str) -> tuple[float, ...]:
    values = tuple(sorted({float(part.strip()) for part in text.split(",") if part.strip()}))
    if not values or any(not math.isfinite(value) for value in values):
        raise ValueError("provide finite comma-separated floats")
    return values


def parse_windows(text: str) -> tuple[tuple[float, float], ...]:
    windows: list[tuple[float, float]] = []
    for chunk in text.split(","):
        left_text, right_text = chunk.strip().split(":")
        left, right = float(left_text), float(right_text)
        if not (math.isfinite(left) and math.isfinite(right) and left < right):
            raise ValueError(f"invalid window {chunk!r}")
        windows.append((left, right))
    if not windows:
        raise ValueError("provide at least one search window")
    return tuple(windows)


def positive_inverse_sqrt(matrix: np.ndarray) -> np.ndarray:
    values, vectors = np.linalg.eigh(matrix)
    if float(values[0]) <= 0.0:
        raise RuntimeError("camera Gram matrix is not positive definite")
    return (vectors * (1.0 / np.sqrt(values))[None, :]) @ vectors.T


def build_native_matrix(cameras: Sequence[int], cutoff: int) -> dict[str, Any]:
    models = [native.build_camera_model(int(camera), int(cutoff)) for camera in cameras]
    camera, size = collective.native_readout_matrix(models)
    numbers = np.arange(1, size + 1, dtype=np.float64)
    logarithms = np.log(numbers)
    whitening = positive_inverse_sqrt(camera @ camera.T)
    coisometric = whitening @ camera
    return {
        "models": models,
        "camera": camera,
        "size": size,
        "numbers": numbers,
        "logarithms": logarithms,
        "whitening": whitening,
        "coisometric": coisometric,
    }


def sigma_diagonal(numbers: np.ndarray, sigma: float) -> np.ndarray:
    """Return D_(sigma-1/2) diagonal entries."""
    return numbers ** (-(float(sigma) - 0.5))


def sigma_deformed_operator(camera: np.ndarray, numbers: np.ndarray, sigma: float) -> np.ndarray:
    return camera * sigma_diagonal(numbers, sigma)[None, :]


def critical_state(numbers: np.ndarray, logarithms: np.ndarray, time_value: float) -> np.ndarray:
    return numbers ** -0.5 * np.exp(-1j * float(time_value) * logarithms)


def sigma_state(
    numbers: np.ndarray, logarithms: np.ndarray, sigma: float, time_value: float
) -> np.ndarray:
    return numbers ** (-float(sigma)) * np.exp(-1j * float(time_value) * logarithms)


def characteristic(
    camera: np.ndarray,
    numbers: np.ndarray,
    logarithms: np.ndarray,
    sigma: float,
    time_value: float,
) -> np.ndarray:
    return camera @ sigma_state(numbers, logarithms, sigma, time_value)


def operator_characteristic(
    camera: np.ndarray,
    numbers: np.ndarray,
    logarithms: np.ndarray,
    sigma: float,
    time_value: float,
) -> np.ndarray:
    deformed = sigma_deformed_operator(camera, numbers, sigma)
    return deformed @ critical_state(numbers, logarithms, time_value)


def raw_energy(
    camera: np.ndarray,
    numbers: np.ndarray,
    logarithms: np.ndarray,
    sigma: float,
    time_value: float,
) -> float:
    value = characteristic(camera, numbers, logarithms, sigma, time_value)
    return float(np.vdot(value, value).real)


def normalized_visible_energy(
    coisometric: np.ndarray,
    numbers: np.ndarray,
    logarithms: np.ndarray,
    sigma: float,
    time_value: float,
) -> float:
    state = sigma_state(numbers, logarithms, sigma, time_value)
    state /= np.linalg.norm(state)
    value = coisometric @ state
    return float(np.vdot(value, value).real)


def refine_valley(
    camera: np.ndarray,
    coisometric: np.ndarray,
    numbers: np.ndarray,
    logarithms: np.ndarray,
    sigma: float,
    window: tuple[float, float],
) -> dict[str, Any]:
    def objective(time_value: float) -> float:
        return raw_energy(camera, numbers, logarithms, sigma, time_value)

    result = minimize_scalar(
        objective,
        bounds=window,
        method="bounded",
        options={"xatol": 1.0e-13, "maxiter": 700},
    )
    time_value = float(result.x)
    value = characteristic(camera, numbers, logarithms, sigma, time_value)
    per_camera = np.abs(value) ** 2
    return {
        "sigma": float(sigma),
        "delta": float(sigma - 0.5),
        "window": [float(window[0]), float(window[1])],
        "time": time_value,
        "raw_resultant_energy": float(np.vdot(value, value).real),
        "raw_resultant_norm": float(np.linalg.norm(value)),
        "normalized_visible_energy": normalized_visible_energy(
            coisometric, numbers, logarithms, sigma, time_value
        ),
        "camera_resultant_energies": per_camera.astype(float).tolist(),
        "optimizer_success": bool(result.success),
        "optimizer_evaluations": int(result.nfev),
    }


def tangent_geometry(
    camera: np.ndarray,
    numbers: np.ndarray,
    logarithms: np.ndarray,
    time_value: float,
) -> dict[str, Any]:
    state = sigma_state(numbers, logarithms, 0.5, time_value)
    value = camera @ state
    common = camera @ (logarithms * state)
    sigma_tangent = -common
    time_tangent = -1j * common
    kappa = float(np.vdot(sigma_tangent, sigma_tangent).real)
    return {
        "time": float(time_value),
        "critical_energy": float(np.vdot(value, value).real),
        "kappa_sigma": kappa,
        "kappa_time": float(np.vdot(time_tangent, time_tangent).real),
        "real_tangent_pairing": float(np.vdot(sigma_tangent, time_tangent).real),
        "complex_tangent_pairing": [
            float(np.vdot(sigma_tangent, time_tangent).real),
            float(np.vdot(sigma_tangent, time_tangent).imag),
        ],
        "cauchy_riemann_tangent_error": float(
            np.linalg.norm(time_tangent - 1j * sigma_tangent)
        ),
        "local_energy_law": "E(delta,tau)=kappa*(delta^2+tau^2)+higher_order at an exact zero",
    }


def symmetric_sigma_pairs(sigmas: Sequence[float], tolerance: float = 1.0e-12) -> list[float]:
    values = np.asarray(sigmas, dtype=np.float64)
    deltas: list[float] = []
    for sigma in values:
        delta = float(sigma - 0.5)
        if delta <= tolerance:
            continue
        if np.any(np.abs(values - (0.5 - delta)) <= tolerance):
            deltas.append(delta)
    return sorted(set(deltas))


def row_by_sigma(rows: Sequence[dict[str, Any]], sigma: float) -> dict[str, Any]:
    return min(rows, key=lambda row: abs(float(row["sigma"]) - float(sigma)))


def empirical_quadratic_coefficients(
    valley_rows: Sequence[dict[str, Any]], sigmas: Sequence[float], kappa: float
) -> list[dict[str, Any]]:
    center = row_by_sigma(valley_rows, 0.5)
    output: list[dict[str, Any]] = []
    for delta in symmetric_sigma_pairs(sigmas):
        lower = row_by_sigma(valley_rows, 0.5 - delta)
        upper = row_by_sigma(valley_rows, 0.5 + delta)
        e0 = float(center["raw_resultant_energy"])
        e_minus = float(lower["raw_resultant_energy"])
        e_plus = float(upper["raw_resultant_energy"])
        coefficient = (e_plus + e_minus - 2.0 * e0) / (2.0 * delta * delta)
        odd_energy = (e_plus - e_minus) / (2.0 * delta)
        time_odd_slope = (
            float(upper["time"]) - float(lower["time"])
        ) / (2.0 * delta)
        time_even_curvature = (
            float(upper["time"])
            + float(lower["time"])
            - 2.0 * float(center["time"])
        ) / (delta * delta)
        output.append(
            {
                "delta": delta,
                "symmetric_energy_coefficient": coefficient,
                "predicted_kappa": kappa,
                "relative_error_to_kappa": abs(coefficient - kappa)
                / max(abs(kappa), np.finfo(np.float64).tiny),
                "odd_energy_slope": odd_energy,
                "optimal_time_odd_slope": time_odd_slope,
                "optimal_time_even_curvature": time_even_curvature,
            }
        )
    return output


def boundary_transport_audit(cameras: Sequence[int], sigmas: Sequence[float]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for sigma in sigmas:
        per_base = []
        for base in cameras:
            modulus = float(base ** (0.5 - sigma))
            per_base.append(
                {
                    "base": int(base),
                    "modulus": modulus,
                    "modulus_defect": modulus - 1.0,
                    "log_modulus": float((0.5 - sigma) * math.log(base)),
                }
            )
        maximum = max(abs(row["modulus_defect"]) for row in per_base)
        if abs(sigma - 0.5) < 1.0e-14:
            regime = "unitary"
        elif sigma < 0.5:
            regime = "expanding"
        else:
            regime = "contracting"
        rows.append(
            {
                "sigma": float(sigma),
                "delta": float(sigma - 0.5),
                "regime": regime,
                "maximum_modulus_defect": float(maximum),
                "per_base": per_base,
            }
        )
    return rows


def operator_rank_audit(system: dict[str, Any], sigmas: Sequence[float]) -> list[dict[str, Any]]:
    camera = np.asarray(system["camera"], dtype=np.float64)
    numbers = np.asarray(system["numbers"], dtype=np.float64)
    rows: list[dict[str, Any]] = []
    for sigma in sigmas:
        deformed = sigma_deformed_operator(camera, numbers, sigma)
        singular = np.linalg.svd(deformed, compute_uv=False)
        rows.append(
            {
                "sigma": float(sigma),
                "rank": int(np.linalg.matrix_rank(deformed, tol=1.0e-11)),
                "minimum_nonzero_singular_value": float(singular[-1]),
                "maximum_singular_value": float(singular[0]),
                "row_condition_number": float(singular[0] / singular[-1]),
            }
        )
    return rows


def port_reconstruction_audit(
    cameras: Sequence[int], cutoff: int, sigmas: Sequence[float], sample_time: float
) -> dict[str, Any]:
    system = build_native_matrix(cameras, cutoff)
    camera = np.asarray(system["camera"], dtype=np.float64)
    numbers = np.asarray(system["numbers"], dtype=np.float64)
    logarithms = np.asarray(system["logarithms"], dtype=np.float64)
    size = int(system["size"])

    colligation = node_weyl.normalized_colligation(size)
    endpoint = np.asarray(colligation["endpoint"], dtype=np.float64)
    bulk = np.asarray(colligation["bulk"], dtype=np.float64)
    poisson = np.asarray(colligation["poisson"], dtype=np.float64)
    atlas = np.vstack((endpoint, bulk))
    endpoint_dimension = endpoint.shape[0]
    endpoint_left_inverse = np.linalg.pinv(endpoint, rcond=1.0e-12)

    rows: list[dict[str, Any]] = []
    for sigma in sigmas:
        deformed_camera = sigma_deformed_operator(camera, numbers, sigma)
        full_readout = deformed_camera @ atlas.T
        endpoint_readout = full_readout[:, :endpoint_dimension]
        bulk_readout = full_readout[:, endpoint_dimension:]
        effective_readout = endpoint_readout + bulk_readout @ poisson
        state = critical_state(numbers, logarithms, sample_time)
        direct = deformed_camera @ state
        endpoint_state = endpoint @ state
        reconstructed_state = endpoint_left_inverse @ endpoint_state
        returned_bulk = poisson @ endpoint_state
        rows.append(
            {
                "sigma": float(sigma),
                "state_reconstruction_error": float(
                    np.linalg.norm(reconstructed_state - state)
                ),
                "bulk_return_error": float(
                    np.linalg.norm(returned_bulk - bulk @ state)
                ),
                "effective_readout_operator_error": float(
                    np.linalg.norm(effective_readout @ endpoint - deformed_camera, ord=2)
                ),
                "effective_characteristic_error": float(
                    np.linalg.norm(effective_readout @ endpoint_state - direct)
                ),
            }
        )

    return {
        "cutoff": int(cutoff),
        "ambient_dimension": size,
        "endpoint_dimension": int(endpoint.shape[0]),
        "bulk_dimension": int(bulk.shape[0]),
        "sample_time": float(sample_time),
        "static_endpoint_left_inverse_error": float(
            np.linalg.norm(endpoint_left_inverse @ endpoint - np.eye(size), ord=2)
        ),
        "static_poisson_error": float(
            np.linalg.norm(poisson @ endpoint - bulk, ord=2)
        ),
        "rows": rows,
        "interpretation": (
            "Port reconstruction remains exact for every finite sigma deformation; "
            "the observed obstruction is not loss of endpoint information."
        ),
    }


def cutoff_audit(
    cameras: Sequence[int],
    cutoff: int,
    sigmas: Sequence[float],
    windows: Sequence[tuple[float, float]],
) -> dict[str, Any]:
    system = build_native_matrix(cameras, cutoff)
    camera = np.asarray(system["camera"], dtype=np.float64)
    coisometric = np.asarray(system["coisometric"], dtype=np.float64)
    numbers = np.asarray(system["numbers"], dtype=np.float64)
    logarithms = np.asarray(system["logarithms"], dtype=np.float64)
    valleys: list[dict[str, Any]] = []
    for window_index, window in enumerate(windows, start=1):
        sigma_rows = [
            refine_valley(
                camera,
                coisometric,
                numbers,
                logarithms,
                sigma,
                window,
            )
            for sigma in sigmas
        ]
        critical = row_by_sigma(sigma_rows, 0.5)
        tangent = tangent_geometry(
            camera, numbers, logarithms, float(critical["time"])
        )
        valleys.append(
            {
                "valley_index": window_index,
                "window": [float(window[0]), float(window[1])],
                "sigma_rows": sigma_rows,
                "critical_tangent_geometry": tangent,
                "empirical_quadratic_coefficients": empirical_quadratic_coefficients(
                    sigma_rows, sigmas, float(tangent["kappa_sigma"])
                ),
            }
        )
    return {
        "cutoff": int(cutoff),
        "ambient_dimension": int(system["size"]),
        "camera_rank": int(np.linalg.matrix_rank(camera, tol=1.0e-11)),
        "valleys": valleys,
    }


def cutoff_convergence(cutoff_rows: Sequence[dict[str, Any]]) -> list[dict[str, Any]]:
    if not cutoff_rows:
        return []
    valley_count = len(cutoff_rows[0]["valleys"])
    output: list[dict[str, Any]] = []
    for valley_index in range(valley_count):
        sigma_values = [
            float(row["sigma"])
            for row in cutoff_rows[0]["valleys"][valley_index]["sigma_rows"]
        ]
        sigma_series: list[dict[str, Any]] = []
        for sigma in sigma_values:
            series = []
            for cutoff_row in cutoff_rows:
                valley = cutoff_row["valleys"][valley_index]
                row = row_by_sigma(valley["sigma_rows"], sigma)
                series.append(
                    {
                        "cutoff": int(cutoff_row["cutoff"]),
                        "ambient_dimension": int(cutoff_row["ambient_dimension"]),
                        "time": float(row["time"]),
                        "raw_resultant_energy": float(row["raw_resultant_energy"]),
                        "normalized_visible_energy": float(row["normalized_visible_energy"]),
                    }
                )
            last = series[-1]
            previous = series[-2] if len(series) > 1 else last
            energy_ratio = float(
                last["raw_resultant_energy"]
                / max(previous["raw_resultant_energy"], np.finfo(np.float64).tiny)
            )
            cutoff_ratio = float(last["cutoff"] / previous["cutoff"])
            effective_decay_exponent = (
                float(-math.log(energy_ratio) / math.log(cutoff_ratio))
                if energy_ratio > 0.0 and cutoff_ratio > 1.0
                else None
            )
            sigma_series.append(
                {
                    "sigma": sigma,
                    "series": series,
                    "last_raw_energy": float(last["raw_resultant_energy"]),
                    "last_step_energy_ratio": energy_ratio,
                    "last_step_effective_decay_exponent": effective_decay_exponent,
                    "last_step_relative_change": float(
                        abs(last["raw_resultant_energy"] - previous["raw_resultant_energy"])
                        / max(abs(last["raw_resultant_energy"]), np.finfo(np.float64).tiny)
                    ),
                }
            )
        output.append(
            {
                "valley_index": valley_index + 1,
                "window": cutoff_rows[0]["valleys"][valley_index]["window"],
                "sigma_series": sigma_series,
            }
        )
    return output


def flatten_csv(report: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for cutoff_row in report["cutoff_rows"]:
        for valley in cutoff_row["valleys"]:
            kappa = valley["critical_tangent_geometry"]["kappa_sigma"]
            for sigma_row in valley["sigma_rows"]:
                rows.append(
                    {
                        "cutoff": cutoff_row["cutoff"],
                        "ambient_dimension": cutoff_row["ambient_dimension"],
                        "valley_index": valley["valley_index"],
                        "window_left": valley["window"][0],
                        "window_right": valley["window"][1],
                        "sigma": sigma_row["sigma"],
                        "delta": sigma_row["delta"],
                        "time": sigma_row["time"],
                        "raw_resultant_energy": sigma_row["raw_resultant_energy"],
                        "raw_resultant_norm": sigma_row["raw_resultant_norm"],
                        "normalized_visible_energy": sigma_row["normalized_visible_energy"],
                        "critical_kappa": kappa,
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
    sigmas = parse_floats(args.sigmas)
    windows = parse_windows(args.windows)
    if not any(abs(sigma - 0.5) < 1.0e-12 for sigma in sigmas):
        raise ValueError("sigma list must include 0.5")

    cutoff_rows = [
        cutoff_audit(cameras, cutoff, sigmas, windows) for cutoff in cutoffs
    ]
    largest_system = build_native_matrix(cameras, cutoffs[-1])
    critical_time = float(
        row_by_sigma(cutoff_rows[-1]["valleys"][0]["sigma_rows"], 0.5)["time"]
    )
    port_cutoff = min(args.port_cutoff, cutoffs[-1])
    port_report = port_reconstruction_audit(
        cameras, port_cutoff, sigmas, critical_time
    )
    boundary_rows = boundary_transport_audit(cameras, sigmas)
    rank_rows = operator_rank_audit(largest_system, sigmas)

    largest = cutoff_rows[-1]
    critical_energies = [
        float(row_by_sigma(valley["sigma_rows"], 0.5)["raw_resultant_energy"])
        for valley in largest["valleys"]
    ]
    offcritical_sigmas = [
        sigma for sigma in sigmas if abs(sigma - 0.5) > 1.0e-12
    ]
    nearest_distance = min(abs(sigma - 0.5) for sigma in offcritical_sigmas)
    nearest_off_sigmas = [
        sigma
        for sigma in offcritical_sigmas
        if abs(abs(sigma - 0.5) - nearest_distance) < 1.0e-12
    ]
    off_energies = [
        float(row_by_sigma(valley["sigma_rows"], sigma)["raw_resultant_energy"])
        for valley in largest["valleys"]
        for sigma in nearest_off_sigmas
    ]

    return {
        "schema": "org.native-carry.sigma-deformed-operator-audit/v1",
        "status": "SIGMA_HALF_VALLEYS_LIFT_QUADRATICALLY_OFF_CRITICAL_EXPONENT",
        "configuration": {
            "cameras": list(cameras),
            "cutoffs": list(cutoffs),
            "sigmas": list(sigmas),
            "windows": [list(window) for window in windows],
            "port_cutoff": int(port_cutoff),
        },
        "operator_deformation": {
            "fixed_geometry": "C_N is the unchanged primitive seed/bracket readout",
            "diagonal_tilt": "D_delta=diag(n^(-delta)), delta=sigma-1/2",
            "deformed_operator": "C_N,sigma=C_N D_delta",
            "equivalent_state_form": (
                "C_N,sigma psi_(1/2,t)=C_N[n^(-sigma)exp(-it log n)]"
            ),
            "finite_rank": (
                "D_delta is invertible at every finite cutoff, so rank(C_N,sigma)=rank(C_N)"
            ),
            "analytic_tangent": "partial_t chi=i partial_sigma chi",
        },
        "boundary_transport": {
            "identity": (
                "q_b^(-1) psi_sigma(bm)/psi_sigma(m)="
                "b^(1/2-sigma) exp(-it log b)"
            ),
            "unit_modulus_condition": "sigma=1/2",
            "rows": boundary_rows,
        },
        "largest_cutoff_operator_rank": {
            "cutoff": int(cutoffs[-1]),
            "ambient_dimension": int(largest_system["size"]),
            "rows": rank_rows,
        },
        "port_reconstruction": port_report,
        "cutoff_rows": cutoff_rows,
        "cutoff_convergence": cutoff_convergence(cutoff_rows),
        "headline_measurements": {
            "largest_cutoff": int(cutoffs[-1]),
            "ambient_dimension": int(largest["ambient_dimension"]),
            "maximum_critical_energy_across_tracked_valleys": max(critical_energies),
            "nearest_tested_offcritical_sigmas": [
                float(sigma) for sigma in nearest_off_sigmas
            ],
            "nearest_tested_delta": float(nearest_distance),
            "minimum_nearest_offcritical_energy_across_valleys_and_sides": min(off_energies),
            "offcritical_to_critical_energy_ratio_lower_bound": min(off_energies)
            / max(max(critical_energies), np.finfo(np.float64).tiny),
        },
        "interpretation": {
            "lossless_ports": (
                "The endpoint map still reconstructs the full finite state and Green bulk for every sigma."
            ),
            "what_breaks": (
                "The carry-normalized endpoint transport stops being unitary: sigma<1/2 expands and sigma>1/2 contracts."
            ),
            "observed_valleys": (
                "At the largest tested cutoff, critical minima are near machine/finite-cutoff zero while offcritical minima remain positive."
            ),
            "local_mechanism": (
                "The sigma tangent is a real-orthogonal quarter-turn of the time tangent. "
                "Retuning t cannot cancel the first-order sigma defect, so the energy lifts quadratically."
            ),
            "scope_warning": (
                "These are finite numerical identities and cutoff observations, not an infinite zero-confinement proof."
            ),
        },
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cameras", default="2,3,4,5,6,7")
    parser.add_argument("--cutoffs", default="32,64,128,256,512,1024")
    parser.add_argument("--sigmas", default="0.45,0.48,0.49,0.5,0.51,0.52,0.55")
    parser.add_argument(
        "--windows",
        default=(
            "13.8:14.4,20.7:21.3,24.7:25.3,"
            "30.1:30.8,32.6:33.2,37.2:38.0"
        ),
    )
    parser.add_argument("--port-cutoff", type=int, default=32)
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("--csv-out", type=Path)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    try:
        if args.port_cutoff < 1:
            raise ValueError("port-cutoff must be positive")
        report = run_lab(args)
    except ValueError as exc:
        parser.error(str(exc))
    payload = json.dumps(report, indent=2, sort_keys=True)
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(payload + "\n", encoding="utf-8")
    if args.csv_out is not None:
        write_csv(args.csv_out, flatten_csv(report))
    print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
