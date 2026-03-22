# Lean 4 + Mathlib Exercises [![Actions Status](../../workflows/Lean%20Action%20CI/badge.svg)](../../actions)

Formalized proofs in Lean 4 using Mathlib, spanning algebra, topology, and custom tactic development. Each file is a self-contained exercise aimed at practicing proof engineering with a large math library.

## Contents

| File | Topic |
|------|-------|
| [**Polynomials.lean**](LeanExcercises/Polynomials.lean) | If a cubic `x³ − x² − ax − b = 0` has three positive roots, then `x³ − x² + bx + a = 0` has one real root and two complex conjugates. Uses Vieta's formulas, AM-GM, and Galois-theoretic conjugation invariance of real polynomial roots (`aeval_conj`). |
| [**Galois.lean**](LeanExcercises/Galois.lean) | The Galois group of `x⁵ + x + 3` over `ℚ` is `S₅`, via irreducibility over `𝔽₇` and cycle-type analysis modulo 2. |
| [**GroupPresentation.lean**](LeanExcercises/GroupPresentation.lean) | The semidirect product `(ℤ/2 × ℤ/2) ⋊ ℤ` (swap action) has the presentation `⟨a, t ∣ a² = 1, [a, t²] = 1, [a, t⁻¹at] = 1⟩`. |
| [**ParacompactByExhaustion.lean**](LeanExcercises/ParacompactByExhaustion.lean) | The union of a compact exhaustion (each `Kᵢ ⊆ int(Kᵢ₊₁)`) is paracompact, via σ-compactness and weak local compactness. |
| [**Reals.lean**](LeanExcercises/Reals.lean) | AM-GM inequality `8abc ≤ (a+b)(b+c)(c+a)` for nonneg reals, from three pairwise weighted AM-GM applications. |
| [**Tactic.lean**](LeanExcercises/Tactic.lean) | Custom Lean 4 tactics, including `apply_iff` which automatically applies the correct direction (`mp`/`mpr`) of an iff lemma. |

## Building

Requires a Lean 4 toolchain (version pinned in [`lean-toolchain`](lean-toolchain)) and Mathlib.

```sh
lake build
```

## Development environment

The repo includes a **Dev Container** ([`.devcontainer/devcontainer.json`](.devcontainer/devcontainer.json)) based on Ubuntu 22.04 with the [lean4](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) and [lean4-code-actions](https://marketplace.visualstudio.com/items?itemName=denis-gorbachev.lean4-code-actions) VS Code extensions pre-installed. Open the repo in VS Code and choose **Reopen in Container** (or use GitHub Codespaces) to get a ready-to-go Lean 4 + Mathlib setup.

### Copilot instructions

[`.github/instructions/lean-debugging.instructions.md`](.github/instructions/lean-debugging.instructions.md) is auto-loaded for all `*.lean` files. It contains Lean 4-specific guidance for GitHub Copilot:

- **Tactic debugging** — `trace_state` workflow, `rw` syntactic-match pitfalls, indentation scope issues.
- **Mathlib API patterns** — bridge lemmas between `eval`/`eval₂`/`aeval`, multiset notation normalization, naming conventions.
- **Proof refactoring** — when to extract named lemmas, abstraction boundary checks, canonical patterns (e.g., `roots.map σ = roots` for field automorphisms).
