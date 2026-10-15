[English](README.md) | [简体中文](README_zh.md)

# 无理数序列的 Lean 4 形式化

存在一个正整数序列 `a`，使得对每一个有界整数序列 `b`，只要对所有 `n` 都有 `a n + b n ≠ 0`，和 `∑ 1 / (a n + b n)` 就是无理数。这是 [Erdős 问题 #264](https://www.erdosproblems.com/264) 背后的存在性问题。

- **作者：** Yao Xu（[@cadamcat](https://github.com/cadamcat)），见[作者与署名](AUTHORS.md)。
- 本项目在 AI 协助下开发；所有证明均由 Lean 4 内核验证。

## 范围

Erdős 问题 #264 还问 `2^n` 和 `n!` 是否为无理数序列。Kovač 与 Tao 证明了 `2^n` 不是；`n!` 是否是仍未解决。本仓库只证明上面的存在性命题，不涉及 `n!`。

Formal Conjectures 的定义（`Erdos264.IsIrrationalitySequence`）还要求对每个 `n` 都有 `b n ≠ 0`。这里证明的性质去掉了这一要求，因此蕴含 Formal Conjectures 的性质。

## 主要结果

| 定理 | 命题 |
| --- | --- |
| `Erdos264.exists_irrationality_sequence` | `∃ a : ℕ → ℕ, (∀ n, 0 < a n) ∧ ∀ b : ℕ → ℤ, BddAbove (Set.range b) → BddBelow (Set.range b) → 0 ∉ Set.range (fun n ↦ (a n : ℤ) + b n) → Irrational (∑' n, (1 : ℝ) / ((a n : ℤ) + b n))` |
| `Erdos264.statement` | 同一命题，通过 [Basic.lean](IrrationalitySequences/Basic.lean) 中的定义 `IsStrongIrrationalitySequence` 和 `Statement` 表述 |

所用序列是 `fast n = 4 · (n + 1) · ∏_{i < n} (fast i + n + 1)`。每一项都大于此前所有扰动后分母的乘积：在有界扰动下，第 `n` 项之后的尾和小于 `4 / fast n`，而每个部分和作为有理数的分母不超过该乘积；若总和为有理数，它与部分和之间的间隙是尾和填不满的。证明见 [Main.lean](IrrationalitySequences/Main.lean)。[Challenge.lean](Challenge.lean) 只用 Mathlib 的词汇陈述第一个定理，[Challenge.json](Challenge.json) 配置 [Comparator](https://github.com/leanprover/comparator) 对二者进行比对。

## 构建与验证

需要 Git 和 [elan](https://github.com/leanprover/elan)。在仓库根目录运行：

```sh
lake exe cache get
./scripts/verify.sh
```

脚本构建库、challenge 文件和 [Verification](Verification) 中的检查，并要求两个定理只依赖 `propext`、`Classical.choice` 和 `Quot.sound`。未完成的证明会显示为 `sorryAx`，脚本以状态 2 退出。[Verification/NonVacuity.lean](Verification/NonVacuity.lean) 检查该性质并非平凡成立：常数序列 `1` 不满足它。详见 [docs/verification.md](docs/verification.md)。

## 固定依赖

- Lean `v4.35.0-rc4`，由 [lean-toolchain](lean-toolchain) 指定；所有文件都使用 module 系统。
- [Mathlib](https://github.com/leanprover-community/mathlib4) 标签 `v4.35.0-rc4`，提交 `1f414401f69059aa7eead47b53ee40bd38455eeb`；其余依赖的版本固定在 [lake-manifest.json](lake-manifest.json) 中。

## 数学参考

- [Erdős 问题 #264](https://www.erdosproblems.com/264)，其中给出了例子 `2^(2^n)`。
- V. Kovač 与 T. Tao，[*On several irrationality problems for Ahmes series*](https://arxiv.org/abs/2406.17593)，定理 2.7：对任意给定的超指数增长，都存在无理数序列。

署名见 [THIRD_PARTY.md](THIRD_PARTY.md)，许可证见 [LICENSE](LICENSE)（Apache-2.0）。
