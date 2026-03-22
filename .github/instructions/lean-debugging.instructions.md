---
applyTo: "**/*.lean"
description: "Lean 4 tactic debugging, proof methodology, Mathlib API patterns, and refactoring guidance"
---

# Lean 4 Tactic Debugging & Proof Methodology

## Inspect state BEFORE attempting the next tactic

Use `trace_state` proactively in these situations — don't guess the goal form:
- Before any `rw` chain — to see the exact syntactic form
- After `fin_cases` / `cases` / `induction` — to see generated goal shapes
- After `ext` — especially on `MonoidHom` involving `Multiplicative`/`Additive` wrappers
- After `simp` — to see what simplified form remains
- When an error says "did not find pattern" or "unsolved goals" showing the original goal

## trace_state workflow

Insert `trace_state` at the inspection point, compile, and grep the output:
```lean
rw [step1]
trace_state  -- prints full context + goal
rw [step2]
```
```bash
lake env lean File.lean 2>&1 | grep -B2 -A20 "trace_state"
```

For sequential `rw` inspection, split `rw [a, b, c]` into separate rewrites with `trace_state` between each — this is the only reliable way to see intermediate states.

## Known pitfalls

### Syntactic vs semantic equality in rw
`(-↑n) - 1` and `(-↑n) + (-1)` are semantically equal but syntactically different. `rw [zpow_add]` pattern-matches on `+`, won't match `-`. Apply `sub_eq_add_neg` first to normalize.

### ext through Multiplicative wrappers
`ext` on `MonoidHom` for types like `Multiplicative (ZMod 2 × ZMod 2)` produces goals with `Additive.toMul`, `MonoidHom.toAdditive''` wrappers and may fail to synthesize `Group (ZMod 2 × ZMod 2)` (bare, unwrapped). **Use `MonoidHom.ext` + `intro` + `show` instead.**

### Indentation determines tactic scope
`| succ n ih => intro x` followed by `have ...` on the next line: Lean parses `intro x` as the complete case body; `have` becomes a new command. **Put `=>` on its own line for multiline bodies.** Symptom: "unsolved goals" showing the pre-tactic goal (= no tactics executed).

### fin_cases simplification
After `fin_cases x <;> simp`, goals have already-simplified forms (e.g., `pb` not `pt⁻¹ * pa * pt`). Don't write `change` patterns based on the pre-simp form. Inspect state first.

### zpow_add unification
Direct `rw [zpow_add]` can fail because Lean can't determine the split point. Use explicit binding: `have h := zpow_add x a b; rw [h]`.

## Key Mathlib API notes

- `Int.ofAdd_mul` (not `ofAdd_mul`) — in namespace `Int`, from `Mathlib.Algebra.Group.Int.TypeTags`
- `MulEquiv.coe_toMonoidHom` exists; `MulEquiv.toMonoidHom_coe` does NOT
- `MulAut` group inverse `⁻¹` IS `MulEquiv.symm`
- `PresentedGroup.toGroup.of : toGroup h (of x) = f x` (simp)
- `PresentedGroup.ext`: two MonoidHoms from a presented group agree iff they agree on generators
- `SemidirectProduct.hom_ext`: two homs equal if they agree on `inl` and `inr`
- `SemidirectProduct.range_inl_eq_ker_rightHom`: exactness for semidirect products
- `DFunLike.congr_fun h x`: go from `f = g` (MonoidHom equality) to `f x = g x`

## More pitfalls

### def vs abbrev transparency
`def ι := fromKlein` makes `ι` and `fromKlein` NOT interchangeable in `exact`/`rfl`/`Exists.intro`. Lean's elaborator won't unfold `def` in expected-type positions. **Use `abbrev` for definitional aliases**, or insert `show`/`change` to manually coerce the goal.

### set_option placement
`set_option maxHeartbeats N in` must come BEFORE any docstring (`/-- ... -/`). The docstring must be immediately before the declaration it documents. Wrong order causes parse errors.

### Group synthesis on unwrapped Multiplicative
Using `rfl` or lemmas like `SemidirectProduct.rightHom_inl` on terms involving `Multiplicative (ZMod 2 × ZMod 2)` can trigger synthesis of `Group (ZMod 2 × ZMod 2)` (bare product, no wrapper). **Workaround**: use `simp [SemidirectProduct.rightHom]` or unfold the definition manually instead of `rfl`.

### Stale Lean workers
Always `pkill -f "lean --worker"` before recompiling via `lake env lean`. Stale workers cache old file state and can report outdated errors, wasting entire compile-debug cycles.

### Heredoc file writing
Writing Lean files via shell heredoc (`cat > file << 'EOF'`) can silently truncate or duplicate content. **Use Python `open().write()` instead** for reliable multi-line file creation from the terminal.

---

## Definitional vs syntactic equality in tactics

### `rw`/`simp` require syntactic matches, not definitional
Two terms can be definitionally equal (`rfl` proves `a = b`) yet `rw [lemma_about_b]` fails to match `a` in the goal. This is the single most common source of wasted compile cycles.

**Common instances:**
- `ofRealHom` vs `algebraMap ℝ ℂ` — definitionally equal, but lemmas like `eval_map_algebraMap` only match the `algebraMap` form.
- `Insert.insert a s` vs `a ::ₘ s` — Multiset `{a, b, c}` notation desugars to `Insert.insert`, but `Multiset.map_cons` matches `::ₘ`.
- `def`-introduced names vs their bodies — `def ι := f` makes `ι` and `f` syntactically different; `rw` won't substitute one for the other.

**Fix patterns:**
- Normalize with a `rw [show a = b from rfl]` before the lemma that needs the other form.
- Use `simp only [Multiset.insert_eq_cons]` to normalize multiset notation to `::ₘ` form.
- Use `abbrev` instead of `def` for definitional aliases that should be transparent.
- Use `change` or `show` to rewrite the goal to the syntactic form the next tactic expects.

### Multiset notation specifically
`{a, b, c} : Multiset α` desugars to nested `Insert.insert` calls. Many `Multiset.*` lemmas are stated for `::ₘ` (cons). To bridge:
```lean
simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
```
This must come BEFORE `rw [Multiset.map_cons, ...]` can work. Alternatively, use `simp only` to do all the rewriting in one step.

---

## Mathlib API discovery practices

### Never guess lemma names
Naming conventions are helpful but unreliable. `map_ne_zero_of_injective` doesn't exist; the actual name is `Polynomial.map_ne_zero` (which uses `[Nontrivial S]`, not injectivity). Always `grep` the Mathlib source before using a name:
```bash
grep -rn "theorem.*map_ne_zero\|lemma.*map_ne_zero" .lake/packages/mathlib/Mathlib/ --include="*.lean" | head -10
```

### Check the exact signature, not just the name
`Multiset.map_le_map_iff` has type `s.map f ≤ t.map f ↔ s ≤ t` — both sides are mapped. It does NOT help with `s.map f ≤ t` (one side unmapped). Read the type before committing to a proof strategy.

### Bridge lemmas between `eval`/`eval₂`/`aeval` worlds
- `eval_map`: `(p.map f).eval x = p.eval₂ f x` — goes from map+eval to eval₂
- `aeval_def`: `aeval x p = eval₂ (algebraMap R A) x p` — relates aeval to eval₂
- `eval_map_algebraMap`: `(map (algebraMap R B) P).eval b = aeval b P` — direct bridge from map+eval to aeval

When a lemma uses `aeval` (e.g., `aeval_conj`) but your goal has `eval` after `eval_map`, you need `eval_map_algebraMap` or must normalize `eval₂ f x` into `aeval x` form. This requires that `f = algebraMap R A` syntactically.

---

## Proof refactoring methodology

### Factor inline proofs into named lemmas when:
- The inline block is ≥3 lines AND has a clean standalone mathematical statement
- The result could be reused at a different degree/dimension (e.g., `roots.map conj = roots` applies to any real polynomial, not just cubics)
- The proof mixes two concerns (e.g., algebraic setup + combinatorial case analysis)

### Check abstraction boundaries before refactoring
When replacing lemma A (which consumes input X) with approach B (which provides weaker input Y):
1. Verify Y is actually sufficient to derive A's conclusion
2. If not, check whether the gap requires a nontrivial theorem (e.g., IVT for odd-degree polynomials)
3. If the gap theorem isn't in Mathlib, keep A — the stronger input avoids needing it

**Pattern:** `Multiset.map conj roots = roots` (multiset equality, strong) vs `∀ z ∈ roots, conj z ∈ roots` (pointwise membership, weak). The former lets you use `cons_eq_cons` to destructure the multiset. The latter requires counting arguments or external theorems to extract structure from an odd-sized set.

### Canonical pattern: `roots.map σ = roots` for a field automorphism σ
To prove a ring automorphism `σ` preserves the root multiset of a polynomial `p` mapped via embedding `f`:
1. `map_roots_le_of_injective p σ.injective` gives `roots.map σ ≤ (p.map σ).roots`
2. `.trans (by rw [map_map, show σ.comp f = f from RingHom.ext (by simp)])` reduces to `≤ roots`
3. `Multiset.eq_of_le_of_card_le ... (by simp)` closes with card equality

This is the standard Galois-theoretic roots argument. The pointwise version (`aeval_conj` etc.) provides an equivalent _semantic_ argument but the multiset-level proof above is shorter in Lean.

---

## Multiset reasoning patterns

### `Multiset.cons_eq_cons` for structural case analysis
When you have `a ::ₘ as = b ::ₘ bs`, this gives:
```
a = b ∧ as = bs ∨ a ≠ b ∧ ∃ cs, as = b ::ₘ cs ∧ bs = a ::ₘ cs
```
This is the workhorse for reasoning about explicit small multisets.

### Permuting multiset elements
To prove `{a, b, c} = {b, a, c}` or similar:
```lean
simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]; abel
```
This normalizes the multiset to an additive expression and lets `abel` handle commutativity.

### Membership in small multisets
`simp` fully reduces `x ∈ ({a, b, c} : Multiset α)` to `x = a ∨ x = b ∨ x = c` (via `mem_cons` + `mem_singleton` + `not_mem_zero`). Then `rcases` or `obtain` destructures the disjunction.
