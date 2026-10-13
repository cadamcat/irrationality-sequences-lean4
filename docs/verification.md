# Verification

## What `scripts/verify.sh` checks

1. `lake build IrrationalitySequences Challenge Verification` succeeds. `Challenge.lean` is expected to report one `sorry`: it is the statement Comparator compares against, not part of the proof.
2. `Verification/Axioms.lean` prints the axioms of `Erdos264.exists_irrationality_sequence` and `Erdos264.statement`; the script requires both lists to be exactly `[propext, Classical.choice, Quot.sound]` and exits with status 2 otherwise. With a `sorry` planted in the main theorem, the script printed `sorryAx` and exited with status 2.
3. `Verification/NonVacuity.lean` compiles: the constant sequence `1` is not a strong irrationality sequence, `fast 0 = 4`, and every value of `fast` is positive.

The build passes `--trust=0` to Lean (see [lakefile.toml](../lakefile.toml)).

## Comparator

[Challenge.json](../Challenge.json) compares `Erdos264.exists_irrationality_sequence` in `Challenge` with the theorem of the same name in `IrrationalitySequences.Main`, allows only the three standard axioms, uses no shared definitions (`definition_names` is empty) and enables the nanoda kernel in addition to Lean's.

## Independent check

Pending.
