"""Verify immutable source pins, release hashes, tests, and the optional pinned Lean build."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time
import unittest

ROOT = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
CHECK_MODULES = ("ACSquareP2Checks", "ACSquareP3Checks", "PaperChecks", "ReleaseChecks")


def run(args, cwd, log):
    start = time.perf_counter()
    result = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log.parent.mkdir(parents=True, exist_ok=True)
    log.write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f"Command failed: {args}; inspect {log}")
    return {"command": args, "returncode": result.returncode,
            "elapsed_seconds": time.perf_counter()-start, "log": log.name}, result.stdout


def audit_sources():
    source = json.loads((ROOT / "SOURCE_PROVENANCE.json").read_text())
    for module in source["lean_modules"]:
        name = f"lean/{module}.lean"
        if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != source["source_sha256"][name]:
            raise ValueError(f"Lean source differs from the proof commit: {name}")
    if hashlib.sha256((ROOT / "lean/AC.lean").read_bytes()).hexdigest() != "927ba318d26b06c312140117b2a4856373832ed2c043944f520ec7337bcfca1b":
        raise ValueError("Official AC.lean differs from the pin")
    # A supplementary scan, not a replacement for kernel checking.
    for path in (ROOT / "lean").glob("*.lean"):
        code = re.sub(r"/-.*?-/", "", path.read_text(), flags=re.S)
        code = re.sub(r"--[^\n]*", "", code)
        if re.search(r"\b(sorry|admit|native_decide|axiom)\b", code):
            raise ValueError(f"Forbidden proof escape or new axiom: {path.name}")
    from experiment import check_pins
    check_pins()
    manifest = ROOT / "MANIFEST.json"
    if manifest.exists():
        for name, expected in json.loads(manifest.read_text())["sha256"].items():
            if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != expected:
                raise ValueError(f"Package hash mismatch: {name}")
    return len(source["lean_modules"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true")
    parser.add_argument("--output", type=Path, default=ROOT / "run/verification.json")
    args = parser.parse_args()
    output = args.output.resolve(); logs = output.parent
    modules = audit_sources(); commands = []
    tests = unittest.defaultTestLoader.discover(str(ROOT), pattern="test_*.py").countTestCases()
    result, _ = run([sys.executable, "-m", "unittest", "-v"], ROOT, logs / "tests.log")
    commands.append(result)
    result, _ = run([sys.executable, "generate_release_lean.py", "--check"], ROOT, logs / "seed-regeneration.log")
    commands.append(result)
    reports = 0
    if args.lean:
        lean = ROOT / "lean"
        result, version = run(["lake", "env", "lean", "--version"], lean, logs / "lean-version.log")
        commands.append(result)
        if "4.29.1" not in version: raise ValueError("Unexpected Lean version")
        manifest = json.loads((lean / "lake-manifest.json").read_text())
        for package in manifest["packages"]:
            directory = lean / ".lake/packages" / package["name"]
            head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=directory, text=True).strip()
            dirty = subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"], cwd=directory, text=True)
            if head != package["rev"] or dirty:
                raise ValueError(f"Dependency pin or cleanliness failure: {package['name']}")
        result, _ = run(["lake", "build"], lean, logs / "lean-build.log")
        commands.append(result)
        for name in CHECK_MODULES:
            result, text = run(["lake", "env", "lean", "--trust=0", f"{name}.lean"], lean, logs / f"{name}-trust-zero.log")
            commands.append(result)
            found = re.findall(r"depends on axioms:\s*\[([^]]*)\]", text)
            expected = (lean / f"{name}.lean").read_text().count("#print axioms")
            no_axioms = text.count("does not depend on any axioms")
            if len(found) + no_axioms != expected:
                raise ValueError(f"Incomplete axiom report: {name}")
            for group in found:
                if not {x.strip() for x in group.split(",") if x.strip()} <= ALLOWED_AXIOMS:
                    raise ValueError(f"Unexpected logical dependency: {group}")
            reports += expected
    receipt = {"ok": True, "proof_source_modules": modules, "python_tests": tests,
               "lean_checked": args.lean, "axiom_reports": reports,
               "trust_zero_modules": list(CHECK_MODULES) if args.lean else [],
               "allowed_axioms": sorted(ALLOWED_AXIOMS), "commands": commands}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k:v for k,v in receipt.items() if k != "commands"}, indent=2))

if __name__ == "__main__": main()
