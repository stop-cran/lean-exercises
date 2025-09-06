import Lean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Lean Elab Tactic

/-- TODO: windback forallE if not iff inside. apply-at. Choose mp/mpr by type. -/
def applyIffT (initial: Term) (e: Term) (type: Expr): TacticM Unit := do
  match type with
  | Expr.forallE binderName _ body_type BinderInfo.default => do
    trace[apply_iff] m!"abstracting argument {binderName} at {type}"
    applyIffT initial (← `(term| ($e ?_))) body_type
  | Expr.forallE _ _ body_type _ => applyIffT initial e body_type
  | Expr.app (Expr.app (Expr.const `Iff []) _) _ =>
    try
      evalApplyLikeTactic (·.apply) (← `(term| Iff.mp ($e)))
    catch _ => evalApplyLikeTactic (·.apply) (← `(term| Iff.mpr ($e)))
  | _ => evalApplyLikeTactic (·.apply) initial

/--macro (name := rwSeq) "rw " c:(config)? s:rwRuleSeq l:(location)? : tactic =>
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) =>
    -- We show the `rfl` state on `]`
    `(tactic| (rewrite $(c)? [$rs,*] $(l)?; with_annotate_state $rbrak (try (with_reducible rfl))))
  | _ => Macro.throwUnsupported
  -- throwErrorAt i m!"Identifier {i} not found"--/

syntax (name := apply_iff) "apply_iff " (ppSpace term) : tactic

@[tactic apply_iff]
elab_rules: tactic | `(tactic| apply_iff $e:term) => do
  let s ← saveState
  let type ← Meta.inferType (← elabTermForApply e)
  s.restore
  applyIffT e e type

macro (name := apply_iff') "apply_iff' " e:(term) : tactic =>
  `(tactic| first | apply (Iff.mp $e) | apply (Iff.mpr $e) | apply $e)


example (a b : Prop) (H: (fun _ => a) 0 ↔ (fun _ => b) 1) (H1: (fun _ => a) 2): (fun _ => b) 3 := by
  simp at *    -- to check the context
  apply_iff H  -- back
  apply_iff H  -- and forth
  apply_iff H.mp
  apply_iff H1 -- apply as is

example (a b : Prop) (H: Nat → Nat → Nat → (a ↔ b)) (H1: a): b := by
  apply_iff H 0
  . assumption
  . exact 1
  . exact 2

example (a: ℝ): a/3 < 3 → a < 3 * 3 := by
  intro H
  apply_iff' div_lt_iff₀ (by positivity) -- A weird error message in the end of this line.
  assumption

example (a: ℝ): a/3 < 2 + 1 → a < 3 * 3 := by
  intro H
  apply_iff div_lt_iff₀ <;> linarith
