# Third-party sources

- **Mathlib** ([leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4)), Apache-2.0, fetched at the revision in [lake-manifest.json](lake-manifest.json). It is a build dependency; no Mathlib source is copied here.
- **Formal Conjectures** ([google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)), Apache-2.0. The definition `IsStrongIrrationalitySequence` adapts `Erdos264.IsIrrationalitySequence` from `FormalConjectures/ErdosProblems/264.lean`, dropping its requirement `b n ≠ 0`.
