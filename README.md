[English](README.md) | [简体中文](README_zh.md)

# Irrationality sequences in Lean 4

There is a sequence of positive integers `a` such that `∑ 1 / (a n + b n)` is irrational for every bounded integer sequence `b` with `a n + b n ≠ 0` for all `n`. This is the existence question behind [Erdős Problem #264](https://www.erdosproblems.com/264).

- **Author:** Yao Xu ([@cadamcat](https://github.com/cadamcat)); see [authors and attribution](AUTHORS.md).
- Developed with AI assistance (Claude Code and Codex); all proofs are verified by the Lean 4 kernel.

## Scope

Erdős Problem #264 also asks whether `2^n` and `n!` are irrationality sequences. Kovač and Tao proved that `2^n` is not; whether `n!` is one is open. This repository proves only the existence statement above and says nothing about `n!`.

Formal Conjectures (`Erdos264.IsIrrationalitySequence`) additionally requires `b n ≠ 0` for every `n`. The property proved here drops that requirement, so it implies Formal Conjectures' property.

## Main results

| Theorem | Statement |
| --- | --- |
| `Erdos264.exists_irrationality_sequence` | `∃ a : ℕ → ℕ, (∀ n, 0 < a n) ∧ ∀ b : ℕ → ℤ, BddAbove (Set.range b) → BddBelow (Set.range b) → 0 ∉ Set.range (fun n ↦ (a n : ℤ) + b n) → Irrational (∑' n, (1 : ℝ) / ((a n : ℤ) + b n))` |
| `Erdos264.statement` | the same, through the definitions `IsStrongIrrationalitySequence` and `Statement` in [Basic.lean](IrrationalitySequences/Basic.lean) |

The witness is `fast n = 4 · (n + 1) · ∏_{i < n} (fast i + n + 1)`. Each term exceeds the product of all earlier perturbed denominators, so for a bounded perturbation the tail after `n` lies below `4 / fast n` while every rational partial sum has denominator at most that product; a rational total would leave a gap the tail cannot fill. The proof is in [Main.lean](IrrationalitySequences/Main.lean). [Challenge.lean](Challenge.lean) states the first theorem in Mathlib vocabulary only, and [Challenge.json](Challenge.json) configures [Comparator](https://github.com/leanprover/comparator) to compare the two.

## Build and verify

Requirements: Git and [elan](https://github.com/leanprover/elan). From the repository root:

```sh
lake exe cache get
./scripts/verify.sh
```

The script builds the library, the challenge and the checks in [Verification](Verification), then requires both theorems to depend only on `propext`, `Classical.choice` and `Quot.sound`. An open proof shows up as `sorryAx` and makes it exit with status 2. [Verification/NonVacuity.lean](Verification/NonVacuity.lean) checks that the property is not satisfied trivially: the constant sequence `1` fails it. Details are in [docs/verification.md](docs/verification.md).

## Fixed dependencies

- Lean `v4.35.0-rc4`, selected by [lean-toolchain](lean-toolchain). Every file uses the module system.
- [Mathlib](https://github.com/leanprover-community/mathlib4) tag `v4.35.0-rc4`, commit `1f414401f69059aa7eead47b53ee40bd38455eeb`; the other revisions are fixed in [lake-manifest.json](lake-manifest.json).

## Mathematical references

- [Erdős Problem #264](https://www.erdosproblems.com/264), including the example `2^(2^n)`.
- V. Kovač and T. Tao, [*On several irrationality problems for Ahmes series*](https://arxiv.org/abs/2406.17593), Theorem 2.7: irrationality sequences exist with any prescribed super-exponential growth.

See [THIRD_PARTY.md](THIRD_PARTY.md) for attribution and [LICENSE](LICENSE) for the license (Apache-2.0).
