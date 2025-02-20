import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.MeanInequalities

/-!
  # For given real number `a` and `b` prove that if an equation `x³ - x² - a*x - b = 0` has
  # 3 positive roots, than an equation `x³ - x² + b*x + a = 0` has one positive root and
  # two complex-conjugate roots.
-/

open Complex ComplexConjugate Polynomial

macro (name := multiset_abel) "multiset_abel" : tactic =>
  `(tactic| {repeat rw [Multiset.insert_eq_cons, ←Multiset.singleton_add]; abel_nf})

/-- Roots of mapped polynomial are symmetric to another map, which is idempotent the first one. -/
theorem roots_map_idp {R : Type*} {S : Type v} [Semiring R] [Field S] {p : R[X]} {f : R →+* S}
  {i : S →+* S} (h : i.comp f = f) : (p.map f).roots.map i = (p.map f).roots :=
  Multiset.eq_of_le_of_card_le ((map_roots_le_of_injective _ i.injective).trans
    (by rw [map_map, h])) (by simp)

/-- If roots of a mapped polynomial equals a mapped set, then roots of the original polynomial
    equal to the original set. -/
theorem map_roots_of_map {R : Type*} {S : Type v} [Field R] [CommRing S] [IsDomain S] (p : R[X])
  (s : Multiset R) (f : R →+* S) (h : (p.map f).roots = s.map f) : p.roots = s := by
  induction s using Multiset.induction generalizing p
  · have := map_roots_le_of_injective p f.injective
    aesop
  · have : p ≠ 0 := by aesop
    have hp : p.IsRoot ?_ := by
      apply_rules [IsRoot.of_map _ f.injective, (mem_roots _).mp] <;> aesop
    apply mul_divByMonic_eq_iff_isRoot.mpr at hp
    rw [←hp, Polynomial.map_mul, roots_mul (by aesop)] at h
    rw [←hp, roots_mul] <;> aesop

/-- A multiset of three complex numbers symmetric to conjugation either contains three reals or
    one real and two conjugates. -/
lemma multiset_3_conj_symm {z1 z2 z3 : ℂ}
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
      rw [conj_eq_iff_re.mp] <;> aesop
  · have Hz1 : z1 ∈ ({conj z1, conj z2, conj z3} : Multiset ℂ) := by rw [←h]; simp
    simp at Hz1
    right
    rcases Hz1 with _ | eq | eq; tauto
    · rw [(by multiset_abel : ({z1, z2, z3} : Multiset ℂ) = {z2, z1, z3}), eq] at h
      simp at h
      exists z3.re, z1
      rw [conj_eq_iff_re.mp (by tauto),
          (by multiset_abel : ({z1, z2, z3} : Multiset ℂ) = {z3, z1, z2})]
      simp
      aesop
    · rw [(by multiset_abel : ({z1, z2, z3} : Multiset ℂ) = {z3, z2, z1}), eq] at h
      simp at h
      exists z2.re, z1
      rw [conj_eq_iff_re.mp (by tauto),
          (by multiset_abel : ({z1, z2, z3} : Multiset ℂ) = {z2, z1, z3})]
      simp
      aesop

/-- Specialized version of AM-GM inequality for two variables. -/
lemma am_gm_2 (x1 x2 x3 : ℝ) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3):
  x3 ^ (1/2 : ℝ) * (x1 * x2 * x3) ^ (1/2 : ℝ) ≤ x3 * (x1 + x2) * (1/2 : ℝ) := by
  have := @Real.geom_mean_le_arith_mean2_weighted (1/2 : ℝ) (1/2 : ℝ) x1 x2 ?_ ?_ ?_ ?_ ?_
  rw [(by ring : x1 * x2 * x3 = x3 * (x1 * x2)), Real.mul_rpow, ←mul_assoc, ←pow_two,
      ←Real.rpow_mul_natCast, Real.mul_rpow]
  norm_num
  all_goals first | positivity | nlinarith

/-- Specialized version of AM-GM inequality for three variables. -/
lemma am_gm_3 (x1 x2 x3 : ℝ) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3):
  3 * (x1 * x2 * x3) ^ (1/3 : ℝ) ≤ x1 + x2 + x3 := by
  have h := @Real.geom_mean_le_arith_mean3_weighted (1/3 : ℝ) (1/3 : ℝ) (1/3 : ℝ) x1 x2 x3
  repeat specialize h (by linarith)
  rw [←Real.mul_rpow, ←Real.mul_rpow] at h
  linarith
  all_goals positivity

/-- Each cubic equation either has all three roots real or one real root and two conjugates. -/
lemma cubic_roots_cases (p : Cubic ℝ) (ha : p.a ≠ 0) : (∃ x1 x2 x3 : ℝ, p.roots = {x1, x2, x3}) ∨
  ∃ x : ℝ, ∃ z : ℂ, z ≠ conj z ∧ (Cubic.map ofRealHom p).roots = {↑x, z, conj z} := by
  -- Any cubic equation has three roots over ℂ, because this field is algebraically closed.
  obtain ⟨z1, z2, z3, hz⟩ : ∃ z1 z2 z3 : ℂ, (p.map ofRealHom).roots = {z1, z2, z3} := by
    apply_rules [Multiset.card_eq_three.mp, (Cubic.splits_iff_card_roots _).mp,
      IsAlgClosed.splits_codomain]
  rw [Cubic.map_roots] at *
  have hz' := hz
  apply_fun Multiset.map conj at hz
  rw [roots_map_idp (by ext; simp), hz'] at hz -- Prove that the roots are symmetric to conjugation
  -- Use the conjugation symmetry to deduce the structure of the roots
  rcases multiset_3_conj_symm hz
  left
  exists z1.re, z2.re, z3.re
  apply map_roots_of_map _ _ ofRealHom
  all_goals aesop

/-- First root for arbitrary coefficients provided by Vieta's formulas is positive, if the
    coefficients are positive. -/
lemma first_root_positive (x1 x2 x3 : ℝ) : 0 < x1 * x2 * x3 → 0 < x1 * x2 + x1 * x3 + x2 * x3 →
  x1 + x2 + x3 = 1 → 0 < x1 := by
  intros
  rcases lt_trichotomy x1 0 with _ | _ | _ <;> try {subst_vars; linarith}
  rcases lt_trichotomy x2 0 with _ | _ | _ <;> try nlinarith
  rcases lt_trichotomy x3 0 with _ | _ | _ <;> try nlinarith
  have : 0 < -x1 := by linarith
  linarith [(by positivity : 0 < -x1 * x2 * x3)]

/-- Bounds for arbitrary coefficients provided by Vieta's formulas. -/
lemma coeff_bounds (a b x1 x2 x3 : ℝ) : x1 > 0 → x2 > 0 → x3 > 0 →
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

/-- Vieta's formulas specialized for the given type of equation. --/
lemma cubic_ab_vieta {a b x1 x2 x3 : ℝ} : Cubic.roots ⟨1, -1, a, b⟩ = {x1, x2, x3} →
  x1 + x2 + x3 = 1 ∧ a = x1 * x2 + x1 * x3 + x2 * x3 ∧ -b = x1 * x2 * x3 := by
  intro (h : (Cubic.map (RingHom.id _) ⟨1, -1, a, b⟩).roots = _)
  have := Cubic.b_eq_three_roots ?_ h
  have := Cubic.c_eq_three_roots ?_ h
  have := Cubic.d_eq_three_roots ?_ h
  all_goals simp_all
  linarith

/-- The coefficient bounds are not compatible with the same bounds for swapped coefficients. -/
lemma coeff_bounds_asymm (a b : ℝ) : 0 < b → b ≤ 1 / 27 → a / 3 ≥ b ^ (2/3 : ℝ) →
                                   0 < a → a ≤ 1 / 27 → b / 3 ≥ a ^ (2/3 : ℝ) → False := by
  intros _ _ ha _ _ _
  apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by positivity)).mpr at ha
  absurd (by norm_num at ha; linarith : a ^ (2/3 : ℝ) * 3 ≤ (a / 3) ^ (3/2 : ℝ))
  simp
  rw [Real.div_rpow, (by norm_num : 3/2 = 2/3 + (5/6 : ℝ)), Real.rpow_add, mul_div_assoc]
  gcongr
  apply (div_lt_iff₀ ?_).mpr
  rw [←Real.rpow_one_add', (by norm_num : 1 + (2/3 + 5/6) = 3 * (5/6 : ℝ)), Real.rpow_mul]
  gcongr
  linarith
  all_goals positivity

example (x1 x2 x3 : ℝ) : Cubic.roots ⟨1, -1, -a, -b⟩ = {x1, x2, x3} → x1 > 0 → x2 > 0 → x3 > 0 →
  ∃ (y : ℝ) (z : ℂ), y > 0 ∧ z ≠ conj z ∧ @Cubic.roots ℂ _ _ ⟨1, -1, b, a⟩ = {↑y, z, conj z} := by
  intros hx _ _ _
  -- Apply Vieta's formulas to the original equation.
  apply cubic_ab_vieta at hx
  -- Consider two possible cases of the root structure for the equation with negated coefficients.
  rcases cubic_roots_cases ⟨1, -1, b, a⟩ (by simp) with ⟨y1, y2, y3, hy⟩ | ⟨y, z, _, hy⟩
  -- A case where all three roots are real (actually impossible).
  · -- Apply Vieta's formulas to the equation with negated coefficients.
    apply cubic_ab_vieta at hy
    -- Obtain coefficient bounds for the original equation.
    have := coeff_bounds b (-a) x1 x2 x3 ?_ ?_ ?_ ?_ ?_ ?_
    -- All roots must be positive.
    have : a < 0 := by nlinarith
    have := first_root_positive y1 y2 y3 ?_ ?_ ?_
    have := first_root_positive y2 y3 y1 ?_ ?_ ?_
    have := first_root_positive y3 y1 y2 ?_ ?_ ?_
    -- Obtain coefficient bounds for the equation with negated coefficients.
    have := coeff_bounds (-a) b y1 y2 y3 ?_ ?_ ?_ ?_ ?_ ?_
    exfalso -- The above bounds are mutually incompatible.
    apply coeff_bounds_asymm (-a) b
    all_goals linarith
  -- A case where one root is real and two are conjugates.
  · have : y > 0 := by
      apply Cubic.d_eq_three_roots (by simp) at hy
      apply_fun Complex.re at hy
      simp at hy
      nlinarith [normSq_apply z]
    simp [Cubic.map] at hy
    exists y, z
