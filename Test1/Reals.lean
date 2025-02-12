import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities

open Real

lemma rpow_two_inv (x : ℝ) (h : 0 ≤ x) : x = x ^ (1/2 : ℝ) * x ^ (1/2 : ℝ) := by
  rw [←pow_two,  ←Real.rpow_mul_natCast h]
  norm_num

example (a b c : ℝ) : 0 ≤ a → 0 ≤ b → 0 ≤ c → 8 * a * b * c ≤ (a + b) * (b + c) * (c + a) := by
  intros
  -- Consider AM-GM inequality for three variables pairwise.
  have hab := @geom_mean_le_arith_mean2_weighted (1/2 : ℝ) (1/2 : ℝ) a b ?_ ?_ ?_ ?_ ?_
  have hbc := @geom_mean_le_arith_mean2_weighted (1/2 : ℝ) (1/2 : ℝ) b c ?_ ?_ ?_ ?_ ?_
  have hca := @geom_mean_le_arith_mean2_weighted (1/2 : ℝ) (1/2 : ℝ) c a ?_ ?_ ?_ ?_ ?_
  -- Multiply the inequalities.
  have h := mul_le_mul_of_nonneg hab (mul_le_mul_of_nonneg hbc hca ?_ ?_) ?_ ?_
  -- The remaining nontrivial simplification.
  nth_rw 1 [rpow_two_inv a, rpow_two_inv b, rpow_two_inv c]
  all_goals first | positivity | linarith
