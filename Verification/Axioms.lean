module

public import IrrationalitySequences

/-!
# Axiom audit

Each theorem below must depend only on `propext`, `Classical.choice` and `Quot.sound`.
`scripts/verify.sh` checks the printed lists.
-/

#print axioms Erdos264.exists_irrationality_sequence
#print axioms Erdos264.statement
