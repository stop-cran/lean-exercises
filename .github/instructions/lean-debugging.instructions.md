---
applyTo: "**/*.lean"
description: "Lean 4 tactic debugging patterns: trace_state usage, rw chain inspection, ext/fin_cases pitfalls, indentation scope issues, Multiplicative wrapper issues, zpow_add unification"
---

# Lean 4 Tactic Debugging

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
