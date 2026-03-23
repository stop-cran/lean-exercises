---
applyTo: "**/*.lean,lean-toolchain,lakefile.toml,lake-manifest.json"
description: "Lean 4 / Mathlib version upgrade: toolchain migration, API breakage patterns, and fix strategies"
---

# Lean 4 & Mathlib Version Upgrade Guide

## Upgrade workflow

### 1. Update toolchain
```bash
echo "leanprover/lean4:v<NEW_VERSION>" > lean-toolchain
```

### 2. Update dependencies
```bash
# Remove any pinned revisions in lakefile.toml unless intentional
lake update
```

### 3. Try the Mathlib cache first
```bash
lake exe cache get
```
If the cache fails (stale or unavailable), Mathlib will build from source (~2 hours for ~3300 modules). This is expected for bleeding-edge toolchains.

### 4. Build and fix errors
```bash
# Kill stale workers before each compile attempt
pkill -f "lean --worker" 2>/dev/null; sleep 2
lake env lean <FILE>.lean 2>&1 | grep "^<FILE>.*error" | head -20
```

### 5. Full project verification
```bash
lake build <TARGET> 2>&1 | grep "error\|warning" | grep -v "declaration uses.*sorry"
```

---

## Common API breakage patterns

### ZMod.val returns Fin.val coercion (v4.29+)

**Symptom**: After `fin_cases`, goals contain `↑(k + l : Fin n)` where `↑` is `Fin.val`. `simp`, `norm_num`, and `norm_cast` all fail to reduce `↑(0 : Fin 2)` to `0 : ℕ`.

**Root cause**: `ZMod.val` for `ZMod (n+1)` is now `((↑) : Fin (n+1) → ℕ)`. Unfolding it with `simp [ZMod.val]` leaves `Fin.val` coercions that the simplifier cannot reduce to ℕ literals.

**Fix strategies** (in order of preference):

1. **Avoid unfolding `ZMod.val`** — use `ZMod.val_zero`, `ZMod.val_one`, `ZMod.val_add` directly:
   ```lean
   -- Instead of: simp [ZMod.val]; norm_num
   -- Use:
   simp [ZMod.val_zero]                          -- for (0 : ZMod n).val = 0
   haveI : Fact (1 < 2) := ⟨by omega⟩
   simp [ZMod.val_zero, ZMod.val_one]            -- for val of 0 and 1
   ```

2. **Algebraic rewriting with `ZMod.val_add`** — avoid `fin_cases` entirely:
   ```lean
   -- g^2 = 1 implies g^(n%2) = g^n
   have key : ∀ n, g ^ (n % 2) = g ^ n := fun n => by
     conv_rhs => rw [← Nat.div_add_mod n 2]
     simp [pow_add, pow_mul, hg]
   rw [ZMod.val_add, key, pow_add]
   ```

3. **Explicit `rfl` witnesses** (when `ZMod.val` is already unfolded):
   ```lean
   simp only [..., ZMod.val,
     show ((0 : Fin 2) : ℕ) = 0 from rfl,
     show ((1 : Fin 2) : ℕ) = 1 from rfl,
     pow_zero, pow_one, mul_one]
   ```
   ⚠️ These `show ... from rfl` lemmas may fail if simp already rewrote the Fin.val subterms. Place them early in the simp list.

### Polynomial.Splits API change

**Symptom**: `Polynomial.Splits` expects one argument instead of two. `p.Splits f` no longer type-checks.

**Old API**: `p.Splits (f : R →+* S)` — a polynomial splits via a ring hom.
**New API**: `Splits p` or `p.Splits` where `p` is the mapped polynomial.

**Fix**:
```lean
-- Old:
instance : Fact (f.Splits (algebraMap ℚ f.SplittingField)) := ...
-- New:
instance : Fact ((f.map (algebraMap ℚ f.SplittingField)).Splits) :=
  ⟨SplittingField.splits f⟩
```

### FiniteDimensional.finrank → Module.finrank

**Symptom**: `Unknown constant 'FiniteDimensional.finrank'`.

**Fix**: Replace `FiniteDimensional.finrank` with `Module.finrank`. If instance synthesis fails for `Module R M`, add an explicit instance:
```lean
instance : Module ℚ f.SplittingField := Algebra.toModule
```

### IsSolvableByRad → solvableByRad membership

**Symptom**: `IsSolvableByRad` is deprecated. `solvableByRad.isSolvable'` argument type mismatch.

**Old API**: `IsSolvableByRad F α` — type class on an element.
**New API**: `α ∈ solvableByRad F E` — membership in an `IntermediateField`.

**Fix**:
```lean
-- Old:
theorem not_solvable {α : E} (hα : aeval α f = 0) : ¬IsSolvableByRad ℚ α := by
  intro hrad
  exact ... (solvableByRad.isSolvable' hrad f_irreducible hα)

-- New:
theorem not_solvable {α : E} (hα : aeval α f = 0) : α ∉ solvableByRad ℚ E := by
  intro hrad
  exact ... (isSolvable_gal_of_irreducible hrad f_irreducible hα)
```

### Simp lemma removals / renames

After upgrading, many `simp only [...]` calls may have unused arguments. The linter will report them. Fix by removing the flagged lemmas from the simp list. Common removals:
- `SemidirectProduct.left_inl`, `right_inl`, `left_inr`, `right_inr`
- `toAdd_ofAdd`, `toAdd_one`
- `MulAut.inv_apply`
- `zpow_ofNat`
- `PresentedGroup.toGroup.of` (in some contexts)

---

## Debugging upgrade failures

### Reading deprecation hints
Lean prints deprecation warnings with the replacement name:
```
warning: `solvableByRad.isSolvable'` has been deprecated: Use `isSolvable_gal_of_irreducible` instead
```
Always check the replacement's signature — argument order and types may have changed.

### Instance synthesis failures
When `failed to synthesize instance` occurs after an upgrade:
1. Check if the constant was renamed or moved to a different namespace
2. Try adding explicit instances: `Algebra.toModule`, `inferInstance`
3. Check if the type class hierarchy changed (e.g., `FiniteDimensional` → `Module.Finite`)

### Stale build artifacts
If Mathlib reports missing `.ir` files or mysterious elaboration failures:
```bash
# Rebuild Mathlib from scratch (slow but reliable)
lake exe cache get          # try cache first
lake build Mathlib          # fall back to source build
```

### Version compatibility
- Check Mathlib's `lean-toolchain` matches your project's toolchain
- After `lake update`, verify `lake-manifest.json` has compatible versions
- Batteries build failures (e.g., "invalid binder annotation") usually indicate a Lean version bug — try a newer Lean version

---

## Pre-upgrade checklist

- [ ] Commit current working state
- [ ] Note the current toolchain version and Mathlib commit
- [ ] Update `lean-toolchain`
- [ ] Remove Mathlib `rev` pin in `lakefile.toml` (unless pinning intentionally)
- [ ] Run `lake update`
- [ ] Run `lake exe cache get`
- [ ] Build each file individually: `lake env lean <FILE>.lean 2>&1`
- [ ] Fix errors file by file
- [ ] Run full `lake build` to verify
- [ ] Check for new warnings (unused simp args, deprecations)
