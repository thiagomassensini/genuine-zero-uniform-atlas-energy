#!/usr/bin/env python3
"""Validate the locked, explicitly non-kernel empirical evidence record."""

from __future__ import annotations

import ast
from collections import Counter
import hashlib
import json
import re
import tarfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EVIDENCE_PATH = ROOT / "audit/empirical-evidence.json"
SHA256 = re.compile(r"^[0-9a-f]{64}$")


def fail(message: str) -> None:
    raise SystemExit(f"empirical evidence check failed: {message}")


evidence = json.loads(EVIDENCE_PATH.read_text())

if evidence.get("schema") != (
    "org.genuine-zero-uniform-atlas-energy.empirical-evidence/v1"
):
    fail("unknown schema")
if evidence.get("status") != "NUMERICAL_FLOAT64_EVIDENCE_NOT_KERNEL_CHECKED":
    fail("the numerical campaign must remain explicitly outside the kernel")

source = evidence.get("operator_source", {})
if source.get("repository") != (
    "https://github.com/thiagomassensini/finite-native-carry-operator"
):
    fail("operator repository differs from the audited source")
if source.get("commit") != "00e9d6beb17226545abf5ddf90bbfede6c7146b0":
    fail("operator commit differs from the audited source")
if source.get("file") != (
    "laboratory/native_carry_primitive_real_operator_all_bases.py"
):
    fail("operator file differs from the audited source")
if not SHA256.fullmatch(source.get("sha256", "")):
    fail("operator source SHA-256 is malformed")

geometry = evidence.get("camera_geometry", {})
if geometry.get("labels") != [2, 3, 4, 5, 6, 7]:
    fail("camera labels differ from the formal six-camera type")
if geometry.get("periods") != [4, 3, 4, 5, 6, 7]:
    fail("camera periods differ from the formal geometry table")
if geometry.get("second_radius_moments") != [1, 1, 5, 5, 14, 14]:
    fail("radius moments differ from the formal geometry table")
if geometry.get("even_antipodal_channels") != {"4": 2, "6": 3}:
    fail("even antipodal channels differ from the formal geometry table")

campaign = evidence.get("campaign", {})
expected_runtime = {
    "python": "3.12.12",
    "numpy": "2.3.5",
    "scipy": "1.17.0",
}
if campaign.get("runtime") != expected_runtime:
    fail("campaign runtime differs from the recorded environment")

expected_source_hashes = {
    "audit/empirical-campaign/native_carry_transverse_coercivity_certificate_lab.py":
        "76f857c5557e19f2f5bbdd97ff4cd0915ee675633dfd8e24b589fe78f3c70d09",
    "audit/empirical-campaign/native_carry_sigma_deformed_operator_lab.py":
        "896c89486273cd8a42f0b51baba3550e7aac725c9b6fd62fb393501eb8f50d12",
    "audit/empirical-campaign/native_carry_pythagorean_node_weyl_colligation_lab.py":
        "754c9e8f8fd8e285b7d916d122ef240fd517092c3f21e6fc871694d98ec18f35",
    "audit/empirical-campaign/native_carry_collective_operator_lab.py":
        "006180ccfd317daebd1fd8003666d758c9f456a951dd096e88f61769fed2743b",
    "audit/empirical-campaign/native_carry_primitive_real_operator_all_bases_fixed.py":
        "c68d4bb274f36eb4dc5572afe64394787876f64bc8f2e50573654f2ab712ecee",
    "audit/empirical-campaign/native_carry_conservative_all_bases_atlas_lab.py":
        "895d26701831c179f41a1f3b81512973eb2592fc847fd4bf4935e4d7cb2ef738",
    "audit/empirical-campaign/native_carry_quadratic_weighted_green_atlas_lab.py":
        "feeb57037b592584c9520d1e3563eb0fc0270a7f033fcb0762e8e4c5a2d1157c",
    "audit/empirical-campaign/native_carry_residual_native_return_identification_lab.py":
        "d2bf9ea9e189e27bb7683df4295a7864641c39262b241122ce24aacc1711eded",
    "audit/empirical-campaign/aggregate_coercivity_56_results.py":
        "de8269d0ebb31a22ae3df7a7781eb28df6b3994f4f65abb6fb778626bfb83aac",
}
source_entries = campaign.get("source_files", [])
source_hashes = {
    entry.get("path"): entry.get("sha256")
    for entry in source_entries
    if isinstance(entry, dict)
}
if len(source_hashes) != len(source_entries):
    fail("campaign source manifest has duplicate or malformed paths")
if source_hashes != expected_source_hashes:
    fail("campaign source manifest differs from the audited import closure")

source_modules = {Path(path).stem for path in source_hashes}
for relative_path, expected_digest in source_hashes.items():
    source_path = ROOT / relative_path
    if not source_path.is_file():
        fail(f"campaign source is missing: {relative_path}")
    source_bytes = source_path.read_bytes()
    if hashlib.sha256(source_bytes).hexdigest() != expected_digest:
        fail(f"campaign source hash changed: {relative_path}")
    try:
        syntax = ast.parse(source_bytes, filename=relative_path)
    except SyntaxError as error:
        fail(f"campaign source does not parse: {relative_path}: {error}")
    local_imports: set[str] = set()
    for node in ast.walk(syntax):
        if isinstance(node, ast.Import):
            local_imports.update(
                alias.name for alias in node.names
                if alias.name.startswith("native_carry_")
            )
        elif (
            isinstance(node, ast.ImportFrom)
            and node.module is not None
            and node.module.startswith("native_carry_")
        ):
            local_imports.add(node.module)
    missing_imports = local_imports.difference(source_modules)
    if missing_imports:
        fail(
            f"campaign source closure is incomplete for {relative_path}: "
            + ", ".join(sorted(missing_imports))
        )

requirements = ROOT / "audit/empirical-campaign/requirements.txt"
if requirements.read_text() != "numpy==2.3.5\nscipy==1.17.0\n":
    fail("campaign requirements lock changed")
operator_copy = (
    ROOT
    / "audit/empirical-campaign/"
      "native_carry_primitive_real_operator_all_bases_fixed.py"
)
if hashlib.sha256(operator_copy.read_bytes()).hexdigest() != source.get("sha256"):
    fail("included operator copy differs from the pinned upstream source")

bundle_rel = campaign.get("bundle")
if bundle_rel != "audit/coercivity_56_guard1024_results.tar.gz":
    fail("campaign bundle path differs from the audited repository path")
bundle_path = ROOT / bundle_rel
if not bundle_path.is_file():
    fail("campaign bundle is missing from the repository")
bundle_digest = hashlib.sha256(bundle_path.read_bytes()).hexdigest()
expected_bundle_digest = (
    "6aabb89cb3e460ae3142a6e82341d3597b9afe3d632151d76c6de186824053ae"
)
if campaign.get("bundle_sha256") != expected_bundle_digest:
    fail("campaign bundle manifest digest differs from the audited digest")
if bundle_digest != expected_bundle_digest:
    fail("campaign bundle contents differ from the locked SHA-256")

cutoffs = [8192, 12288, 16384, 24576, 32768, 49152, 65536]
coefficients = [0.25, 0.5, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
expected_status_counts = {
    "CERTIFIED_NONNEGATIVE_ON_COMPACT": 18,
    "COUNTEREXAMPLE_FOUND": 2,
    "RESOURCE_LIMIT_UNRESOLVED": 36,
}
if campaign.get("cutoffs") != cutoffs:
    fail("campaign cutoff grid changed")
if campaign.get("candidate_coefficients") != coefficients:
    fail("campaign coefficient grid changed")
if campaign.get("status_counts") != expected_status_counts:
    fail("campaign manifest status counts changed")
if campaign.get("compact") != {
    "sigma": [0.49, 0.51],
    "time": [10.0, 40.0],
}:
    fail("campaign compact rectangle changed")

job_count = campaign.get("job_count")
if job_count != len(cutoffs) * len(coefficients):
    fail("campaign grid size differs from job_count")
if job_count != sum(expected_status_counts.values()):
    fail("campaign status counts do not sum to job_count")


def coefficient_token(coefficient: float) -> str:
    if coefficient == 0.25:
        return "0p25"
    if coefficient == 0.5:
        return "0p5"
    return str(int(coefficient))


archive_root = "coercivity_56_guard1024"
job_stems = [
    f"M{cutoff}_c{coefficient_token(coefficient)}"
    for cutoff in cutoffs
    for coefficient in coefficients
]
expected_archive_names = {
    archive_root,
    f"{archive_root}/environment.txt",
    f"{archive_root}/jobs.tsv",
}
for stem in job_stems:
    expected_archive_names.update(
        f"{archive_root}/{stem}.{extension}"
        for extension in ("cmd", "json", "csv", "log", "status")
    )

archive_statuses: Counter[str] = Counter()
archive_four_certified: list[int] = []
with tarfile.open(bundle_path, mode="r:gz") as archive:
    members = archive.getmembers()
    member_names = [member.name for member in members]
    if len(member_names) != len(set(member_names)):
        fail("campaign bundle contains duplicate member names")
    if set(member_names) != expected_archive_names:
        missing = expected_archive_names.difference(member_names)
        extra = set(member_names).difference(expected_archive_names)
        fail(
            "campaign bundle member set changed; missing="
            f"{sorted(missing)} extra={sorted(extra)}"
        )
    if any(not (member.isfile() or member.isdir()) for member in members):
        fail("campaign bundle contains a link or special file")

    def archive_bytes(relative_name: str) -> bytes:
        extracted = archive.extractfile(f"{archive_root}/{relative_name}")
        if extracted is None:
            fail(f"campaign bundle member is not a regular file: {relative_name}")
        return extracted.read()

    expected_jobs = [
        f"{cutoff}\t{coefficient:g}"
        for cutoff in cutoffs
        for coefficient in coefficients
    ]
    jobs = archive_bytes("jobs.tsv").decode().splitlines()
    if jobs != expected_jobs:
        fail("campaign jobs.tsv differs from the exact grid")

    environment = archive_bytes("environment.txt").decode()
    for expected_line in (
        "Python 3.12.12",
        "numpy 2.3.5",
        "scipy 1.17.0",
        "76f857c5557e19f2f5bbdd97ff4cd0915ee675633dfd8e24b589fe78f3c70d09  "
        "native_carry_transverse_coercivity_certificate_lab.py",
        "c68d4bb274f36eb4dc5572afe64394787876f64bc8f2e50573654f2ab712ecee  "
        "native_carry_primitive_real_operator_all_bases_fixed.py",
    ):
        if expected_line not in environment:
            fail(f"campaign environment record lost: {expected_line}")

    expected_branch = {
        "guard_multiplier": 1024.0,
        "maximum_cells": 1_000_000,
        "minimum_sigma_radius": 5e-10,
        "minimum_time_radius": 8e-10,
        "sigma_bins": 8,
        "time_bins": 120,
    }
    for cutoff in cutoffs:
        for coefficient in coefficients:
            stem = f"M{cutoff}_c{coefficient_token(coefficient)}"
            json_bytes = archive_bytes(f"{stem}.json")
            if archive_bytes(f"{stem}.log") != json_bytes:
                fail(f"campaign log differs from JSON payload: {stem}")
            if not archive_bytes(f"{stem}.csv"):
                fail(f"campaign CSV is empty: {stem}")
            status_fields = archive_bytes(f"{stem}.status").decode().split()
            if not status_fields or status_fields[0] != "SUCCESS":
                fail(f"campaign process did not complete successfully: {stem}")
            command = archive_bytes(f"{stem}.cmd").decode()
            for fragment in (
                f"--cutoffs {cutoff}",
                f"--certify {cutoff}:{coefficient:g}",
                "--guard-multiplier 1024",
                f"--json-out {archive_root}/{stem}.json",
                f"--csv-out {archive_root}/{stem}.csv",
            ):
                if fragment not in command:
                    fail(f"campaign command mismatch for {stem}: {fragment}")

            report = json.loads(json_bytes)
            configuration = report.get("configuration", {})
            if configuration.get("cameras") != [2, 3, 4, 5, 6, 7]:
                fail(f"campaign JSON camera table changed: {stem}")
            if configuration.get("cutoffs") != [cutoff]:
                fail(f"campaign JSON cutoff changed: {stem}")
            if configuration.get("sigma_compact") != [0.49, 0.51]:
                fail(f"campaign JSON sigma compact changed: {stem}")
            if configuration.get("time_compact") != [10.0, 40.0]:
                fail(f"campaign JSON time compact changed: {stem}")
            if configuration.get("branch") != expected_branch:
                fail(f"campaign JSON branch configuration changed: {stem}")
            if configuration.get("requested_certificate_coefficients") != {
                str(cutoff): coefficient
            }:
                fail(f"campaign JSON requested coefficient changed: {stem}")

            rows = report.get("cutoff_rows", [])
            if len(rows) != 1 or rows[0].get("cutoff") != cutoff:
                fail(f"campaign JSON cutoff row changed: {stem}")
            certificate = rows[0].get("coercivity_certificate", {})
            if certificate.get("coefficient") != coefficient:
                fail(f"campaign JSON certificate coefficient changed: {stem}")
            status = certificate.get("status")
            if status not in expected_status_counts:
                fail(f"campaign JSON has an unknown status: {stem}: {status}")
            if certificate.get("certified") != (
                status == "CERTIFIED_NONNEGATIVE_ON_COMPACT"
            ):
                fail(f"campaign JSON certified flag contradicts status: {stem}")
            archive_statuses[status] += 1
            if coefficient == 4.0 and certificate.get("certified"):
                archive_four_certified.append(cutoff)

if dict(archive_statuses) != expected_status_counts:
    fail("campaign archive status counts differ from the manifest")
if archive_four_certified != [8192, 12288, 16384]:
    fail("campaign archive coefficient-four cutoff list changed")
if campaign.get("coefficient_four_certified_cutoffs") != archive_four_certified:
    fail("campaign manifest coefficient-four cutoff list differs from archive")

expected_semantics = (
    "These jobs were classified as CERTIFIED_NONNEGATIVE_ON_COMPACT by the "
    "campaign under its float64 guard; this is not interval certification or "
    "a Lean theorem."
)
if campaign.get("coefficient_four_status_semantics") != expected_semantics:
    fail("coefficient-four status semantics lost the non-kernel disclaimer")
guard_note = campaign.get("guard_note", "")
if "not formal interval arithmetic" not in guard_note:
    fail("campaign guard note no longer excludes interval certification")

scope = evidence.get("formal_scope", {})
does_not_prove = scope.get("does_not_prove", [])
if not does_not_prove:
    fail("formal scope boundary is missing")
required_boundaries = {
    "a global bound for the named cutoff-tail remainder or scaled-tail convergence",
    "the numerical inequality phaseFloor > 4",
    "a concrete C/M bridge from the reoptimized finite operator to the algebraic phase model",
    "a kernel-checked coefficient-four bound",
}
missing_boundaries = required_boundaries.difference(does_not_prove)
if missing_boundaries:
    fail(
        "formal scope lost required boundaries: "
        + ", ".join(sorted(missing_boundaries))
    )

print(
    "empirical evidence check passed: "
    f"{job_count} float64 jobs locked and explicitly non-kernel"
)
