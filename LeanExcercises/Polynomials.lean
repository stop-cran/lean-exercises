import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.MeanInequalities

/-!
  # Cubic root structure under coefficient swap

  For real numbers `a` and `b`, if the equation `x³ - x² - a·x - b = 0` has three positive
  roots, then the equation `x³ - x² + b·x + a = 0` has one positive real root and two
  complex-conjugate roots.

  The proof uses Vieta's formulas and AM-GM bounds to show that the "all real roots" case
  for the swapped equation leads to a contradiction.
-/

open Complex ComplexConjugate Polynomial

/-- If the roots of a mapped polynomial equal a mapped multiset, then the roots of the
    original polynomial equal the original multiset. -/
theorem roots_eq_of_map_roots_eq_map {R : Type*} {S : Type v} [Field R] [CommRing S] [IsDomain S] (p : R[X])
  (s : Multiset R) (f : R →+* S) (h : (p.map f).roots = s.map f) : p.roots = s := by
  induction s using Multiset.induction generalizing p
  · have := map_roots_le_of_injective p f.injective
    simp only [Multiset.map_zero] at h
    exact Multiset.map_injective f.injective (Multiset.le_zero.mp (h ▸ this))
  · have : p ≠ 0 := by intro hp; simp [hp] at h
    have hp : p.IsRoot ?_ := by
      apply_rules [IsRoot.of_map _ f.injective, (mem_roots _).mp] <;> aesop
    apply mul_divByMonic_eq_iff_isRoot.mpr at hp
    rw [←hp, Polynomial.map_mul, roots_mul (by aesop)] at h
    rw [←hp, roots_mul] <;> aesop

/-- A conjugation-symmetric multiset of three complex numbers either consists of three reals
    or has the form `{x, z, conj z}` for some real `x` and non-real `z`. -/
lemma multiset_three_conj_cases {z1 z2 z3 : ℂ}
  (h : ({z1, z2, z3} : Multiset ℂ) = {conj z1, conj z2, conj z3}):
  ↑z1.re = z1 ∧ ↑z2.re = z2 ∧ ↑z3.re = z3 ∨
  ∃ x : ℝ, ∃ z : ℂ, z ≠ conj z ∧ ({z1, z2, z3} : Multiset ℂ) = {↑x, z, conj z} := by
  by_cases H1 : conj z1 = z1
  · simp [H1] at h
    by_cases H2 : conj z2 = z2
    · simp [H2] at h
      rw [conj_eq_iff_re.mp, conj_eq_iff_re.mp, conj_eq_iff_re.mp] <;> tauto
    · rcases Multiset.cons_eq_cons.mp h with _ | ⟨_, _, eq, _⟩; tauto
      apply (Multiset.singleton_eq_cons_iff _).mp at eq
      right
      exists z1.re, z2
      rw [conj_eq_iff_re.mp] <;>
        first | exact ⟨fun h => H2 h.symm, by obtain ⟨rfl, _⟩ := eq; rfl⟩ | exact H1
  · have Hz1 : z1 ∈ ({conj z1, conj z2, conj z3} : Multiset ℂ) := by rw [←h]; simp
    simp at Hz1
    right
    rcases Hz1 with _ | eq | eq; tauto
    · rw [(by simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]; abel :
            ({z1, z2, z3} : Multiset ℂ) = {z2, z1, z3}), eq] at h
      simp at h
      exists z3.re, z1
      rw [conj_eq_iff_re.mp (by tauto),
          (by simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]; abel :
            ({z1, z2, z3} : Multiset ℂ) = {z3, z1, z2})]
      simp
      exact ⟨fun h => H1 h.symm, by simp [eq]⟩
    · rw [(by simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]; abel :
            ({z1, z2, z3} : Multiset ℂ) = {z3, z2, z1}), eq] at h
      simp at h
      exists z2.re, z1
      rw [conj_eq_iff_re.mp (by tauto),
          (by simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]; abel :
            ({z1, z2, z3} : Multiset ℂ) = {z2, z1, z3})]
      simp
      exact ⟨fun h => H1 h.symm, by simp [eq]⟩

/-- Weighted AM-GM for two nonneg reals, scaled by a third:
    `√x₃ · √(x₁x₂x₃) ≤ x₃(x₁ + x₂)/2`. -/
lemma am_gm_2 (x1 x2 x3 : ℝ) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3):
  x3 ^ (1/2 : ℝ) * (x1 * x2 * x3) ^ (1/2 : ℝ) ≤ x3 * (x1 + x2) * (1/2 : ℝ) := by
  have := @Real.geom_mean_le_arith_mean2_weighted (1/2 : ℝ) (1/2 : ℝ) x1 x2 ?_ ?_ ?_ ?_ ?_
  rw [(by ring : x1 * x2 * x3 = x3 * (x1 * x2)), Real.mul_rpow, ←mul_assoc, ←pow_two,
      ←Real.rpow_mul_natCast, Real.mul_rpow]
  norm_num
  all_goals first | positivity | nlinarith

/-- AM-GM for three nonneg reals with equal weights:
    `3 · (x₁x₂x₃)^(1/3) ≤ x₁ + x₂ + x₃`. -/
lemma am_gm_3 (x1 x2 x3 : ℝ) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3):
  3 * (x1 * x2 * x3) ^ (1/3 : ℝ) ≤ x1 + x2 + x3 := by
  have h := @Real.geom_mean_le_arith_mean3_weighted (1/3 : ℝ) (1/3 : ℝ) (1/3 : ℝ) x1 x2 x3
  repeat specialize h (by linarith)
  rw [←Real.mul_rpow, ←Real.mul_rpow] at h
  linarith
  all_goals positivity

/-- Conjugation fixes the multiset of roots of a real polynomial.
    Each root's conjugate is a root (by `aeval_conj`), so `roots.map conj ≤ roots`;
    card equality gives `=`. -/
lemma roots_map_conj (p : ℝ[X]) :
    (map ofRealHom p).roots.map conj = (map ofRealHom p).roots :=
  Multiset.eq_of_le_of_card_le
    ((map_roots_le_of_injective _ (starRingEnd ℂ).injective).trans
      (by rw [map_map, show (starRingEnd ℂ).comp ofRealHom = ofRealHom from
        RingHom.ext (by simp)]))
    (by simp)

/-- Each cubic equation either has all three roots real or one real root and two conjugates. -/
lemma cubic_roots_cases (p : Cubic ℝ) (ha : p.a ≠ 0) : (∃ x1 x2 x3 : ℝ, p.roots = {x1, x2, x3}) ∨
  ∃ x : ℝ, ∃ z : ℂ, z ≠ conj z ∧ (Cubic.map ofRealHom p).roots = {↑x, z, conj z} := by
  -- Any cubic equation has three roots over ℂ, because this field is algebraically closed.
  obtain ⟨z1, z2, z3, hz⟩ : ∃ z1 z2 z3 : ℂ, (p.map ofRealHom).roots = {z1, z2, z3} := by
    apply_rules [Multiset.card_eq_three.mp, (Cubic.splits_iff_card_roots _).mp,
      IsAlgClosed.splits_codomain]
  rw [Cubic.map_roots] at *
  -- Derive conjugation symmetry of roots using roots_map_conj (from aeval_conj)
  have hz' := hz
  have hconj := roots_map_conj p.toPoly
  rw [hz] at hconj
  simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.insert_eq_cons] at hconj
  -- Use the conjugation symmetry to deduce the structure of the roots
  rcases multiset_three_conj_cases hconj.symm
  left
  exists z1.re, z2.re, z3.re
  apply roots_eq_of_map_roots_eq_map _ _ ofRealHom
  · obtain ⟨h1, h2, h3⟩ := ‹_ ∧ _ ∧ _›; simp only [Multiset.insert_eq_cons,
      ← Multiset.singleton_add] at *; simp_all
  · right; obtain ⟨x, z, hne, heq⟩ := ‹∃ _ _, _›; exact ⟨x, z, hne, hz'.trans heq⟩

/-- If three reals have positive product, positive pairwise-product sum, and sum to 1,
    then the first is positive. Used symmetrically in `all_roots_positive`. -/
lemma first_root_positive (x1 x2 x3 : ℝ) : 0 < x1 * x2 * x3 → 0 < x1 * x2 + x1 * x3 + x2 * x3 →
  x1 + x2 + x3 = 1 → 0 < x1 := by
  intros
  rcases lt_trichotomy x1 0 with _ | _ | _ <;> try {subst_vars; linarith}
  rcases lt_trichotomy x2 0 with _ | _ | _ <;> try nlinarith
  rcases lt_trichotomy x3 0 with _ | _ | _ <;> try nlinarith
  have : 0 < -x1 := by linarith
  linarith [(by positivity : 0 < -x1 * x2 * x3)]

/-- All three roots are positive when the product and sum of pairwise products are positive
    and the roots sum to 1. -/
lemma all_roots_positive (x1 x2 x3 : ℝ) : 0 < x1 * x2 * x3 →
    0 < x1 * x2 + x1 * x3 + x2 * x3 → x1 + x2 + x3 = 1 →
    0 < x1 ∧ 0 < x2 ∧ 0 < x3 := by
  intro h1 h2 h3
  exact ⟨first_root_positive x1 x2 x3 h1 h2 h3,
    first_root_positive x2 x3 x1 (by nlinarith) (by nlinarith) (by linarith),
    first_root_positive x3 x1 x2 (by nlinarith) (by nlinarith) (by linarith)⟩

/-- If three roots of a monic cubic `x³ - x² + …` are positive, the elementary symmetric
    polynomials satisfy `0 < e₃ ≤ 1/27` and `e₂/3 ≥ e₃^(2/3)`. -/
lemma vieta_bounds (a b x1 x2 x3 : ℝ) : x1 > 0 → x2 > 0 → x3 > 0 →
  a = x1 * x2 * x3 → b = x1 * x2 + x1 * x3 + x2 * x3 → x1 + x2 + x3 = 1 →
  0 < a ∧ a ≤ 1/27 ∧ b/3 ≥ a ^ (2/3 : ℝ) := by
  intros
  subst_vars
  split_ands; positivity
  · convert_to _ ≤ (1/3 : ℝ) ^ (3 : ℝ); norm_num
    apply (Real.rpow_inv_le_iff_of_pos ?_ ?_ ?_).mp
    norm_num
    have := am_gm_3 x1 x2 x3 ?_ ?_ ?_
    linarith
    all_goals positivity
  · apply (le_div_iff₀' (by linarith)).mpr
    trans
    · have h := am_gm_3 (x1 ^ (1/2 : ℝ)) (x2 ^ (1/2 : ℝ)) (x3 ^ (1/2 : ℝ)) ?_ ?_ ?_
      rewrite [←Real.mul_rpow, ←Real.mul_rpow, ←Real.rpow_mul] at h
      have h' := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ (x1 * x2 * x3) ^ (1/2 : ℝ))
      rewrite [mul_assoc, ←Real.rpow_add'] at h'
      norm_num at h'
      exact h'
      all_goals positivity
    · have := am_gm_2 x1 x2 x3 ?_ ?_ ?_
      have := am_gm_2 x2 x3 x1 ?_ ?_ ?_
      have := am_gm_2 x3 x1 x2 ?_ ?_ ?_
      rw [(by ring : x2 * x3 * x1 = x1 * x2 * x3), (by ring : x3 * x1 * x2 = x1 * x2 * x3)] at *
      all_goals linarith

/-- Vieta's formulas for a monic depressed cubic `x³ - x² + ax + b` with three real roots:
    the roots sum to 1, their pairwise product sum equals `a`, and their product equals `-b`. -/
lemma cubic_vieta {a b x1 x2 x3 : ℝ} : Cubic.roots ⟨1, -1, a, b⟩ = {x1, x2, x3} →
  x1 + x2 + x3 = 1 ∧ a = x1 * x2 + x1 * x3 + x2 * x3 ∧ -b = x1 * x2 * x3 := by
  intro (h : (Cubic.map (RingHom.id _) ⟨1, -1, a, b⟩).roots = _)
  have := Cubic.b_eq_three_roots ?_ h
  have := Cubic.c_eq_three_roots ?_ h
  have := Cubic.d_eq_three_roots ?_ h
  all_goals simp_all
  linarith

/-- The AM-GM bounds from `vieta_bounds` are asymmetric: they cannot hold simultaneously
    for both `(a, b)` and `(b, a)`. This is the key contradiction used to rule out the
    all-real-roots case in `cubic_swapped_roots`.

    Strategy: from `a/3 ≥ b^(2/3)` invert to get `(a/3)^(3/2) ≥ b`, then show
    `a^(2/3) · 3 > (a/3)^(3/2)` by splitting off an `a^(5/6)` factor and using `a ≤ 1/27`,
    contradicting `b/3 ≥ a^(2/3)`. -/
lemma vieta_bounds_asymm (a b : ℝ) : 0 < b → b ≤ 1 / 27 → a / 3 ≥ b ^ (2/3 : ℝ) →
                                   0 < a → a ≤ 1 / 27 → b / 3 ≥ a ^ (2/3 : ℝ) → False := by
  intros _ _ ha _ _ _
  -- Invert the bound: a/3 ≥ b^(2/3) ⟹ (a/3)^(3/2) ≥ b
  apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by positivity)).mpr at ha
  -- It suffices to show a^(2/3) · 3 > (a/3)^(3/2)
  absurd (by norm_num at ha; linarith : a ^ (2/3 : ℝ) * 3 ≤ (a / 3) ^ (3/2 : ℝ))
  simp
  -- Rewrite (a/3)^(3/2) = a^(2/3) · a^(5/6) / 3^(3/2) and reduce to showing a^(5/6) < 3^(3/2)
  rw [Real.div_rpow, (by norm_num : 3/2 = 2/3 + (5/6 : ℝ)), Real.rpow_add, mul_div_assoc]
  gcongr
  -- Use a ≤ 1/27 to bound a^(5/6) via a^(5/6) = (a^(1 + 2/3 + 5/6))^... < 3^(3/2)
  apply (div_lt_iff₀ ?_).mpr
  rw [←Real.rpow_one_add', (by norm_num : 1 + (2/3 + 5/6) = 3 * (5/6 : ℝ)), Real.rpow_mul]
  gcongr
  linarith
  all_goals positivity

/-- If `x³ - x² - a·x - b = 0` has three positive roots, then `x³ - x² + b·x + a = 0`
    has one positive real root and two complex-conjugate roots. -/
theorem cubic_swapped_roots (x1 x2 x3 : ℝ) :
    Cubic.roots ⟨1, -1, -a, -b⟩ = {x1, x2, x3} → x1 > 0 → x2 > 0 → x3 > 0 →
    ∃ (y : ℝ) (z : ℂ), y > 0 ∧ z ≠ conj z ∧
      @Cubic.roots ℂ _ _ ⟨1, -1, b, a⟩ = {↑y, z, conj z} := by
  intros hx _ _ _
  -- Apply Vieta's formulas to the original equation.
  apply cubic_vieta at hx
  -- Consider two possible root structures for the swapped equation.
  rcases cubic_roots_cases ⟨1, -1, b, a⟩ (by simp) with ⟨y1, y2, y3, hy⟩ | ⟨y, z, _, hy⟩
  -- Case 1: all three roots are real (we show this is impossible).
  · apply cubic_vieta at hy
    -- Obtain AM-GM bounds for the original equation's coefficients.
    have := vieta_bounds b (-a) x1 x2 x3 ?_ ?_ ?_ ?_ ?_ ?_
    -- Deduce that all roots of the swapped equation must be positive.
    have : a < 0 := by nlinarith
    have ⟨_, _, _⟩ := all_roots_positive y1 y2 y3 ?_ ?_ ?_
    -- Obtain AM-GM bounds for the swapped equation's coefficients.
    have := vieta_bounds (-a) b y1 y2 y3 ?_ ?_ ?_ ?_ ?_ ?_
    -- The two sets of bounds are mutually contradictory.
    exfalso
    apply vieta_bounds_asymm (-a) b
    all_goals linarith
  -- Case 2: one real root and two complex-conjugate roots (the desired conclusion).
  · have : y > 0 := by
      apply Cubic.d_eq_three_roots (by simp) at hy
      apply_fun Complex.re at hy
      simp at hy
      nlinarith [normSq_apply z]
    simp [Cubic.map] at hy
    exists y, z
