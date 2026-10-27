#!/usr/bin/env python3
"""Split a CSE/SSA proposal from its proof, or install its checked theorem.

Prepare, build CseCheckpointsLABEL.Program, run GenCseCheckpoints with
--existing-output, check Data/Proof*/Closed, then invoke --install.
"""
import argparse
import re
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("label", type=int)
    parser.add_argument("--install", action="store_true")
    parser.add_argument("--ssa", action="store_true", help="Prepare pass 2 SSA checkpoints instead")
    parser.add_argument("--argc", type=int, help="SSA argument count in the original pass equation")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    base = root / "submission/InitECandidate/Proofs"
    index = 2 if args.ssa else 4
    kind = "Ssa" if args.ssa else "Cse"
    if args.ssa and args.argc is None:
        parser.error("--ssa requires --argc")
    source = base / f"WordStages/Pass{args.label}_{index}.lean"
    target = base / f"{kind}Checkpoints{args.label}"
    target.mkdir(exist_ok=True)
    if args.install:
        if not (target / "Closed.lean").exists():
            raise FileNotFoundError("Generate and kernel-check Closed before installing")
        build = root / ".lake/build/lib/lean"
        for module in target.glob("*.lean"):
            artifact = build / "InitECandidate/Proofs" / target.name / (module.stem + ".olean")
            if not artifact.exists() or artifact.stat().st_mtime < module.stat().st_mtime:
                raise ValueError(f"Kernel-check current {module.name} before installing")
            for dependency in re.findall(r"^import ([A-Za-z0-9_.]+)", module.read_text(), re.M):
                imported = build.joinpath(*dependency.split(".")).with_suffix(".olean")
                if not imported.exists() or imported.stat().st_mtime > artifact.stat().st_mtime:
                    raise ValueError(f"Recheck {module.name} against current {dependency}")
        source.write_text(
            f"import InitECandidate.Proofs.{kind}Checkpoints{args.label}.Closed\n"
            "namespace InitECandidate.Proofs.WordStages\n"
            f"theorem pass{args.label}_{index}_eq : "
            + (f"Flapjack.Compiler.Backend.WordAlloc.fullSsaCcTrans {args.argc} " if args.ssa else
               "Flapjack.Compiler.Backend.WordCse.wordCommonSubexpElim ")
            + f"pass{args.label}_{index-1} = pass{args.label}_{index} := by\n"
            f"  exact InitECandidate.Proofs.{kind}Checkpoints{args.label}.checked\n"
            f"#print axioms pass{args.label}_{index}_eq\n"
            "end InitECandidate.Proofs.WordStages\n"
        )
    else:
        original = source.read_text()
        marker = f"theorem pass{args.label}_{index}_eq"
        if f"def pass{args.label}_{index} " not in original or marker not in original:
            raise ValueError("Expected original pass data and theorem; refusing to overwrite")
        data = original.split(marker, 1)[0]
        (target / "Program.lean").write_text(data + "end InitECandidate.Proofs.WordStages\n")


if __name__ == "__main__":
    main()
