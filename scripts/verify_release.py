"""Build the pinned Lake project and save an independently rerunnable axiom audit."""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8")
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_logged(command, destination):
    with destination.open("w", encoding="utf-8", newline="\n") as log:
        process = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, encoding="utf-8", errors="replace")
        for line in process.stdout:
            log.write(line)
            log.flush()
            print(line, end="", flush=True)
        status = process.wait()
    if status:
        raise RuntimeError(f"Command failed with exit code {status}: {command}")


def main():
    OUT.mkdir(exist_ok=True)
    sources = sorted([*ROOT.glob("*.lean"), *(ROOT / "RefinedBMV").glob("*.lean")])
    for path in sources:
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b", path.read_text(encoding="utf-8")):
            raise RuntimeError(f"Forbidden placeholder or target axiom: {path.relative_to(ROOT)}")
    artifacts = [ROOT / ".lake/build/lib/lean" / p.relative_to(ROOT).with_suffix(".olean")
                 for p in sources]
    fresh = not any(path.exists() for path in artifacts)
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    run_logged(["lake", "build"], OUT / "release_build.log")
    run_logged(["lake", "env", "lean", "-j", "2", "Audit.lean"], OUT / "release_axioms.log")
    audit = (OUT / "release_axioms.log").read_text(encoding="utf-8")
    expected = len(re.findall(r"^#print axioms ", (ROOT / "Audit.lean").read_text(encoding="utf-8"), re.M))
    groups = re.findall(r"depends on axioms:\s*\[(.*?)\]", audit, re.S)
    if len(groups) != expected:
        raise RuntimeError(f"Expected {expected} audit records, got {len(groups)}")
    for group in groups:
        names = {x.strip() for x in group.split(",") if x.strip()}
        if not names <= ALLOWED:
            raise RuntimeError(f"Unexpected axiom dependencies: {sorted(names - ALLOWED)}")
    records = []
    for source, artifact in zip(sources, artifacts):
        if not artifact.is_file():
            raise RuntimeError(f"Unbuilt delivered source: {source.relative_to(ROOT)}")
        records.append({"source": source.relative_to(ROOT).as_posix(),
                        "source_sha256": sha(source), "olean_sha256": sha(artifact)})
    lock = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next(p for p in lock["packages"] if p["name"] == "mathlib")
    report = {"all_passed": True, "started_utc": started,
              "finished_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
              "mathlib_revision": mathlib["rev"],
              "fresh_project_artifacts_before_build": fresh,
              "dependency_cache_note": "Pinned mathlib dependency artifacts may be cached; this field concerns only delivered project sources.",
              "source_files": len(records), "axiom_audits": expected,
              "axiom_allowlist": sorted(ALLOWED), "modules": records}
    (OUT / "release_build_report.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"ALL PASSED: {len(records)} source files; {expected} axiom audits", flush=True)


if __name__ == "__main__":
    main()
