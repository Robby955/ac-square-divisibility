"""Build local release assets from a clean Git commit. Does not publish or tag."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess

from verify import audit_sources

ROOT = Path(__file__).resolve().parent


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def prepare(output: Path):
    if git("status", "--porcelain").strip():
        raise ValueError("Commit or preserve the working-tree changes before preparing a release")
    audit_sources()
    commit = git("rev-parse", "HEAD").decode().strip()
    prefix = "ac-square-divisibility"
    archive = git("archive", "--format=tar", f"--prefix={prefix}/", commit)
    assets = {
        "square-divisibility.pdf": git("show", f"{commit}:paper/square-divisibility.pdf"),
        f"{prefix}-{commit[:12]}.tar.gz": gzip.compress(archive, mtime=0),
        "SOURCE_COMMIT.txt": (commit + "\n").encode(),
        "RELEASE_NOTES.md": git("show", f"{commit}:RELEASE_NOTES.md"),
    }
    hashes = {name: hashlib.sha256(data).hexdigest() for name, data in assets.items()}
    assets["SHA256SUMS"] = "".join(f"{hashes[name]}  {name}\n" for name in sorted(hashes)).encode()
    output.mkdir(parents=True, exist_ok=False)
    for name, data in assets.items():
        (output / name).write_bytes(data)
    return {"source_commit": commit, "directory": str(output), "sha256": hashes,
            "published": False, "tag_created": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "run/release")
    args = parser.parse_args()
    try:
        result = prepare(args.output.resolve())
    except (ValueError, FileExistsError) as error:
        parser.error(str(error))
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
