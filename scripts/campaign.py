"""Aristotle campaign driver (one-round policy).

Usage:
  python scripts/campaign.py run H0            # single node, attempt 1
  python scripts/campaign.py run D05 --attempt 2 --hints-file hints/D05.md
  python scripts/campaign.py wave D01 D02 D03  # parallel attempt-1 wave
  python scripts/campaign.py file <path.lean> --node-id XX --attempt N  # explicit file

Per-node protocol (frozen): attempt 1 raw; attempt 2 with Stacks proof-sketch hints;
attempt 3 one split into <=2 sublemmas (file crafted by hand, submitted via `file`).
Every attempt is logged to REGISTRY.jsonl (append-only).

Acceptance: Aristotle server-side Lean verification (trust directive from the mission
owner); the binding axiom/no-sorry gate is the CI comparator (AxiomCheck.lean).
"""

import argparse
import asyncio
import json
import shutil
import sys
import time
from pathlib import Path

import aristotlelib
from aristotlelib import Project

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "scripts"))
from nodes import NODES, node_file  # noqa: E402

RUNS = REPO / "aristotle_runs"
REGISTRY = REPO / "REGISTRY.jsonl"
TOOLCHAIN = "leanprover/lean4:v4.28.0"
POLL_SECONDS = 60
TIMEOUT_SECONDS = 4 * 3600

PROMPT = (
    "This is a self-contained Lean 4 file using Mathlib (Lean toolchain {tc}). "
    "Prove the theorem `{name}` by replacing its final `sorry` with a complete proof. "
    "Rules: do NOT modify any definition or theorem statement in the file; do NOT add "
    "axioms; do NOT use `sorry` or `native_decide`; you may add private helper lemmas "
    "before the target theorem. The proof must be verified by Lean against Mathlib. "
    "Return the completed .lean file."
)


def log_registry(entry: dict) -> None:
    entry["ts"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    with REGISTRY.open("a") as fh:
        fh.write(json.dumps(entry) + "\n")


def theorem_name(lean_text: str) -> str:
    for line in lean_text.splitlines():
        if line.startswith("theorem "):
            return line.split()[1]
    raise ValueError("no theorem found")


def make_submission_dir(node_id: str, attempt: int, lean_text: str) -> Path:
    d = RUNS / f"{node_id}_a{attempt}" / "submit"
    if d.exists():
        shutil.rmtree(d)
    d.mkdir(parents=True)
    (d / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    (d / f"{node_id}.lean").write_text(lean_text)
    return d


async def run_node(node_id: str, attempt: int, lean_text: str, hints: str | None) -> dict:
    name = theorem_name(lean_text)
    prompt = PROMPT.format(tc=TOOLCHAIN, name=name)
    if hints:
        prompt += (
            "\n\nMathematical context and proof sketch (from the Stacks Project, "
            "Tag 0BNI and the Beauville-Laszlo literature):\n" + hints
        )
    sub = make_submission_dir(node_id, attempt, lean_text)
    t0 = time.time()
    entry = {
        "node_id": node_id,
        "attempt": attempt,
        "config": "raw" if attempt == 1 else ("hints" if attempt == 2 else "split"),
        "theorem": name,
    }
    try:
        project = await Project.create_from_directory(prompt, sub)
        entry["project_id"] = project.project_id
        print(f"[{node_id} a{attempt}] submitted: {project.project_id}", flush=True)
        while True:
            await asyncio.sleep(POLL_SECONDS)
            await project.refresh()
            if project.status.name == "IDLE":
                break
            if time.time() - t0 > TIMEOUT_SECONDS:
                entry.update(result="failed", notes="timeout")
                break
        dest = RUNS / f"{node_id}_a{attempt}" / "result"
        dest.mkdir(parents=True, exist_ok=True)
        out = None
        if project.has_files:
            out = await project.get_files(dest)
        entry["wall_time_s"] = round(time.time() - t0)
        # classify: returned lean file for the node without sorry => proved
        proved = False
        if out is not None:
            for p in sorted(Path(dest).rglob("*.lean")):
                text = p.read_text()
                if name in text and "sorry" not in text:
                    proved = True
                    entry["result_file"] = str(p.relative_to(REPO))
                    entry["lines"] = len(text.splitlines())
                    break
        if "result" not in entry:
            entry["result"] = "proved" if proved else "failed"
        entry["axioms"] = "deferred_to_ci_comparator"
    except Exception as exc:  # noqa: BLE001
        entry.update(result="failed", wall_time_s=round(time.time() - t0),
                     notes=f"error: {type(exc).__name__}: {exc}")
    log_registry(entry)
    print(f"[{node_id} a{attempt}] {entry['result']} ({entry.get('wall_time_s', '?')}s)",
          flush=True)
    return entry


async def main() -> None:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p_run = sub.add_parser("run")
    p_run.add_argument("node")
    p_run.add_argument("--attempt", type=int, default=1)
    p_run.add_argument("--hints-file")
    p_wave = sub.add_parser("wave")
    p_wave.add_argument("nodes", nargs="+")
    p_wave.add_argument("--attempt", type=int, default=1)
    p_file = sub.add_parser("file")
    p_file.add_argument("path")
    p_file.add_argument("--node-id", required=True)
    p_file.add_argument("--attempt", type=int, required=True)
    p_file.add_argument("--hints-file")
    args = ap.parse_args()

    if args.cmd == "run":
        hints = Path(args.hints_file).read_text() if args.hints_file else None
        await run_node(args.node, args.attempt, node_file(args.node), hints)
    elif args.cmd == "wave":
        await asyncio.gather(*(
            run_node(n, args.attempt, node_file(n), None) for n in args.nodes))
    elif args.cmd == "file":
        hints = Path(args.hints_file).read_text() if args.hints_file else None
        await run_node(args.node_id, args.attempt, Path(args.path).read_text(), hints)


if __name__ == "__main__":
    asyncio.run(main())
