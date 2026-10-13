# Verification

## What `scripts/verify.sh` checks

1. `lake build IrrationalitySequences Challenge Verification` succeeds. `Challenge.lean` is expected to report one `sorry`: it is the statement Comparator compares against, not part of the proof.
2. `Verification/Axioms.lean` prints the axioms of `Erdos264.exists_irrationality_sequence` and `Erdos264.statement`; the script requires both lists to be exactly `[propext, Classical.choice, Quot.sound]` and exits with status 2 otherwise. With a `sorry` planted in the main theorem, the script printed `sorryAx` and exited with status 2.
3. `Verification/NonVacuity.lean` compiles: the constant sequence `1` is not a strong irrationality sequence, `fast 0 = 4`, and every value of `fast` is positive.

The build passes `--trust=0` to Lean (see [lakefile.toml](../lakefile.toml)).

## Comparator

[Challenge.json](../Challenge.json) compares `Erdos264.exists_irrationality_sequence` in `Challenge` with the theorem of the same name in `IrrationalitySequences.Main`, allows only the three standard axioms, uses no shared definitions (`definition_names` is empty) and enables the nanoda kernel in addition to Lean's.

## Independent check of v1.0.0

A fresh clone of commit `7fbe31c5efcddf069b67c7a59600aa4db3548c2a` (tag `v1.0.0`), in a new directory with its own build output:

| Check | Command | Result |
| --- | --- | --- |
| Build and axioms | `lake exe cache get`, then `./scripts/verify.sh` | exit 0, `verify: PASS`; both theorems depend on `[propext, Classical.choice, Quot.sound]` |
| Kernel replay | `lake env leanchecker --fresh IrrationalitySequences` | exit 0, no diagnostics |
| Comparator | Comparator `ca04cfc7` with [Challenge.json](../Challenge.json), lean4export `05d43a2b` (Lean v4.35.0-rc4), nanoda_lib `73573340` (nanoda 0.4.22) | exit 0; the nanoda kernel and Lean's kernel both accepted `Erdos264.exists_irrationality_sequence`; "Your solution is okay!" |

After the build, the clone had no changes and `lake-manifest.json` was unchanged. Comparator ran with its development `fake-landrun.sh` in place of the Landrun sandbox, so it checked the statements and the kernels but did not isolate the build.
