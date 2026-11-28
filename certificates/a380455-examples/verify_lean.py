"""Recompile a certificate and its dependencies using a pinned Lean project."""
import argparse
import os
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory

MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
TARGET = "prime-polyomino-factor-maxima-14-17"
THEOREM = "PrimePolyFactor.a380455_four_maxima"


def ordered_sources(source_dir, target):
    done = set()
    visiting = set()
    order = []

    def visit(name):
        if name in done:
            return
        if name in visiting or re.fullmatch(r"[a-z0-9-]+", name) is None:
            raise ValueError(f"Invalid module dependency {name}")
        visiting.add(name)
        source = source_dir / (name + ".lean")
        for line in source.read_text(encoding="utf-8").splitlines():
            if line.startswith("import ") and line != "import Mathlib":
                match = re.fullmatch(r"import certificates\.«([a-z0-9-]+)»", line)
                if not match:
                    raise ValueError(f"Unexpected import in {source.name}: {line}")
                visit(match[1])
        visiting.remove(name)
        done.add(name)
        order.append(name)

    visit(target)
    return order


def pinned_environment(project):
    import json
    toolchain = (project / "lean-toolchain").read_text().strip()
    packages = json.loads((project / "lake-manifest.json").read_bytes())["packages"]
    revision = next((p.get("rev") for p in packages if p["name"] == "mathlib"), None)
    if toolchain != TOOLCHAIN or revision != MATHLIB:
        raise ValueError("The Lean toolchain or Mathlib revision differs from the verified build")
    lean = subprocess.check_output(["lake", "env", "which", "lean"], cwd=project, text=True).strip()
    search = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=project, text=True).strip()
    paths = [str((project / p).resolve()) for p in search.split(os.pathsep) if p]
    return lean, paths


def verify(source_dir, project, target, theorem):
    names = ordered_sources(source_dir, target)
    lean, paths = pinned_environment(project)
    with TemporaryDirectory(prefix="a380455-") as scratch:
        root = Path(scratch)
        sources = root / "certificates"
        compiled = root / "build" / "certificates"
        sources.mkdir()
        compiled.mkdir(parents=True)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(compiled.parent), *paths]), LEAN_NUM_THREADS="1")
        flags = [lean, "-j1", "-DElab.async=false"]
        for i, name in enumerate(names, 1):
            filename = name + ".lean"
            (sources / filename).write_bytes((source_dir / filename).read_bytes())
            print(f"[{i}/{len(names)}] {name}", flush=True)
            subprocess.run([*flags, "-o", str(compiled / (name + ".olean")), str(sources / filename)],
                           cwd=root, env=env, check=True)
        audit = root / "Audit.lean"
        audit.write_text(f"import certificates.«{target}»\n#print axioms {theorem}\n")
        result = subprocess.check_output([*flags, str(audit)], cwd=root, env=env, text=True)
        expected = re.escape("'" + theorem + "' depends on axioms:") + r"\s*\[([^\]]*)\]"
        match = re.search(expected, result)
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        if not match or not set(match[1].split(", ")) <= allowed:
            raise ValueError(f"Unrecognized axiom report: {result}")
        print(result.strip())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path, help="Existing Lean project with the pinned Mathlib cache")
    args = parser.parse_args()
    verify(Path(__file__).resolve().parent.parent, args.project.resolve(), TARGET, THEOREM)
