/-
  Presentation of the group (Z/2 × Z/2) ⋊ Z

  We prove that the semidirect product (Z/2 × Z/2) ⋊_swap Z
  (where Z acts by swapping the two Z/2 factors) has presentation
    ⟨a, t | a² = 1, [a, t²] = 1, [a, t⁻¹at] = 1⟩.
-/
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.Group
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.GroupTheory.Commutator.Basic

noncomputable section

-- ════════════════════════════════════════════════════════════
-- § 1. The Semidirect Product
-- ════════════════════════════════════════════════════════════

abbrev Z2xZ2 := Multiplicative (ZMod 2 × ZMod 2)

def swapAut : MulAut Z2xZ2 :=
  AddEquiv.toMultiplicative (AddEquiv.prodComm (M := ZMod 2) (N := ZMod 2))

def swapAction : Multiplicative ℤ →* MulAut Z2xZ2 where
  toFun n := swapAut ^ n.toAdd
  map_one' := zpow_zero swapAut
  map_mul' a b := zpow_add swapAut a.toAdd b.toAdd

abbrev Z2xZ2_sdp_Z := Z2xZ2 ⋊[swapAction] Multiplicative ℤ

@[simp] lemma swapAut_apply (x y : ZMod 2) :
    swapAut (Multiplicative.ofAdd (x, y)) = Multiplicative.ofAdd (y, x) := by
  simp [swapAut, AddEquiv.toMultiplicative, AddEquiv.prodComm]

lemma swapAut_sq : swapAut ^ 2 = 1 := by
  rw [sq]; ext ⟨x1, x2⟩ : 1
  show swapAut (swapAut (Multiplicative.ofAdd (x1, x2))) = Multiplicative.ofAdd (x1, x2)
  simp

-- ════════════════════════════════════════════════════════════
-- § 2. The Presented Group
-- ════════════════════════════════════════════════════════════

inductive Gen | a | t
open Gen

abbrev fa : FreeGroup Gen := .of a
abbrev ft : FreeGroup Gen := .of t
abbrev fb : FreeGroup Gen := MulAut.conj ft⁻¹ fa

def rels : Set (FreeGroup Gen) :=
  { ⁅fa, ft ^ 2⁆, ⁅fa, fb⁆, fa ^ 2 }

abbrev PG := PresentedGroup rels
abbrev pa : PG := PresentedGroup.of a
abbrev pt : PG := PresentedGroup.of t

-- ════════════════════════════════════════════════════════════
-- § 3. Forward Map: PG → SDP
-- ════════════════════════════════════════════════════════════

def genMap : Gen → Z2xZ2_sdp_Z
  | a => SemidirectProduct.inl (Multiplicative.ofAdd ((1:ZMod 2),(0:ZMod 2)))
  | t => SemidirectProduct.inr (Multiplicative.ofAdd (1:ℤ))

lemma genMap_rels : ∀ r ∈ rels, FreeGroup.lift genMap r = 1 := by
  intro r hr
  simp only [rels, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl <;> {
    apply SemidirectProduct.ext <;>
    simp only [commutatorElement_def, map_mul, map_inv, map_pow,
               FreeGroup.lift_apply_of,
               SemidirectProduct.mul_left, SemidirectProduct.inv_left,
               SemidirectProduct.one_left, SemidirectProduct.mul_right,
               SemidirectProduct.inv_right, SemidirectProduct.one_right,
               genMap, swapAction, MonoidHom.coe_mk, OneHom.coe_mk,
               MulAut.mul_apply] <;>
    rfl
  }

def toSDP : PG →* Z2xZ2_sdp_Z :=
  PresentedGroup.toGroup genMap_rels

-- ════════════════════════════════════════════════════════════
-- § 4. Relations in PG
-- ════════════════════════════════════════════════════════════

abbrev pb : PG := MulAut.conj pt⁻¹ pa

lemma pg_a_sq : pa ^ 2 = 1 :=
  PresentedGroup.one_of_mem (show fa ^ 2 ∈ rels by simp [rels])

lemma pg_comm_a_t2 : pa * pt ^ 2 = pt ^ 2 * pa :=
  commutatorElement_eq_one_iff_mul_comm.mp
    (PresentedGroup.one_of_mem (show ⁅fa, ft ^ 2⁆ ∈ rels by simp [rels]))

lemma pg_comm_a_b : pa * pb = pb * pa :=
  commutatorElement_eq_one_iff_mul_comm.mp
    (PresentedGroup.one_of_mem (show ⁅fa, fb⁆ ∈ rels by simp [rels]))

lemma pg_b_sq : pb ^ 2 = 1 := by
  show (pt⁻¹ * pa * (pt⁻¹)⁻¹) ^ 2 = 1
  rw [conj_pow, pg_a_sq]; group

lemma pg_conj_pt_pa : MulAut.conj pt pa = pb := by
  show pt * pa * pt⁻¹ = pt⁻¹ * pa * (pt⁻¹)⁻¹
  have h := pg_comm_a_t2
  have : pt * pa = pt⁻¹ * pa * (pt * pt) := by
    calc pt * pa
        = pt⁻¹ * (pt ^ 2 * pa) := by group
      _ = pt⁻¹ * (pa * pt ^ 2) := by rw [h]
      _ = pt⁻¹ * pa * (pt * pt) := by rw [sq]; group
  calc pt * pa * pt⁻¹
      = pt⁻¹ * pa * (pt * pt) * pt⁻¹ := by rw [this]
    _ = pt⁻¹ * pa * (pt⁻¹)⁻¹ := by group

lemma pg_tbt : MulAut.conj pt pb = pa := by
  show pt * (pt⁻¹ * pa * (pt⁻¹)⁻¹) * pt⁻¹ = pa; group

lemma pg_conj_ptinv_pb : MulAut.conj pt⁻¹ pb = pa := by
  have h := pg_conj_pt_pa.symm    -- pb = MulAut.conj pt pa
  rw [h, show MulAut.conj pt⁻¹ (MulAut.conj pt pa) = (MulAut.conj pt⁻¹ * MulAut.conj pt) pa
    from rfl, ← map_mul, inv_mul_cancel]
  rfl

-- ════════════════════════════════════════════════════════════
-- § 5. Inverse Map: SDP → PG
-- ════════════════════════════════════════════════════════════

private lemma zmod2_pow_add (g : PG) (hg : g ^ 2 = 1) (x y : ZMod 2) :
    g ^ (x + y).val = g ^ x.val * g ^ y.val := by
  have key : ∀ n, g ^ (n % 2) = g ^ n := fun n => by
    conv_rhs => rw [← Nat.div_add_mod n 2]
    simp [pow_add, pow_mul, hg]
  rw [ZMod.val_add, key, pow_add]

def fromKlein : Z2xZ2 →* PG where
  toFun n := pa ^ (Multiplicative.toAdd n).1.val * pb ^ (Multiplicative.toAdd n).2.val
  map_one' := by
    show pa ^ (0 : ZMod 2).val * pb ^ (0 : ZMod 2).val = 1
    simp [ZMod.val_zero]
  map_mul' x y := by
    show pa ^ ((Multiplicative.toAdd x).1 + (Multiplicative.toAdd y).1).val *
         pb ^ ((Multiplicative.toAdd x).2 + (Multiplicative.toAdd y).2).val =
         pa ^ (Multiplicative.toAdd x).1.val * pb ^ (Multiplicative.toAdd x).2.val *
         (pa ^ (Multiplicative.toAdd y).1.val * pb ^ (Multiplicative.toAdd y).2.val)
    rw [zmod2_pow_add pa pg_a_sq, zmod2_pow_add pb pg_b_sq]
    set x1 := (Multiplicative.toAdd x).1.val
    set x2 := (Multiplicative.toAdd x).2.val
    set y1 := (Multiplicative.toAdd y).1.val
    set y2 := (Multiplicative.toAdd y).2.val
    calc pa ^ x1 * pa ^ y1 * (pb ^ x2 * pb ^ y2)
        = pa ^ x1 * (pa ^ y1 * pb ^ x2) * pb ^ y2 := by group
      _ = pa ^ x1 * (pb ^ x2 * pa ^ y1) * pb ^ y2 := by
          rw [show pa ^ y1 * pb ^ x2 = pb ^ x2 * pa ^ y1 from
            ((commute_iff_eq pa pb).mpr pg_comm_a_b).pow_pow y1 x2 |>.eq]
      _ = pa ^ x1 * pb ^ x2 * (pa ^ y1 * pb ^ y2) := by group

def fromZ : Multiplicative ℤ →* PG := zpowersHom PG pt

@[simp] lemma fromZ_apply (n : Multiplicative ℤ) : fromZ n = pt ^ n.toAdd := rfl

-- Helper: a general conj_swap tactic for checking on 4 elements
private lemma conj_swap_hom_eq (u : PG)
    (hu_a : MulAut.conj u pa = pb) (hu_b : MulAut.conj u pb = pa) :
    fromKlein.comp swapAut.toMonoidHom =
    (MulAut.conj u).toMonoidHom.comp fromKlein := by
  apply MonoidHom.ext; intro ⟨x1, x2⟩
  show fromKlein (swapAut (Multiplicative.ofAdd (x1, x2))) =
    u * fromKlein (Multiplicative.ofAdd (x1, x2)) * u⁻¹
  simp only [swapAut_apply, fromKlein, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  fin_cases x1 <;> fin_cases x2 <;>
    simp only [ZMod.val, pow_zero, pow_one, one_mul, mul_one]
  · group
  · rw [MulAut.conj_apply] at hu_b; exact hu_b.symm
  · rw [MulAut.conj_apply] at hu_a; exact hu_a.symm
  · calc pa * pb
        = MulAut.conj u pb * MulAut.conj u pa := by rw [hu_b, hu_a]
      _ = u * (pb * pa) * u⁻¹ := by simp only [MulAut.conj_apply]; group
      _ = u * (pa * pb) * u⁻¹ := by rw [pg_comm_a_b]

lemma conj_pt_fromKlein (x : Z2xZ2) :
    fromKlein (swapAut x) = pt * fromKlein x * pt⁻¹ := by
  have key := conj_swap_hom_eq pt pg_conj_pt_pa pg_tbt
  exact DFunLike.congr_fun key x

lemma conj_ptinv_fromKlein (x : Z2xZ2) :
    fromKlein (swapAut x) = pt⁻¹ * fromKlein x * pt := by
  have ha : MulAut.conj pt⁻¹ pa = pb := by
    simp [MulAut.conj_apply, inv_inv]
  exact DFunLike.congr_fun (conj_swap_hom_eq pt⁻¹ ha pg_conj_ptinv_pb) x

lemma swapAut_inv : swapAut⁻¹ = swapAut := by
  rw [← mul_left_cancel_iff (a := swapAut), mul_inv_cancel, ← sq, swapAut_sq]

-- Compatibility condition for SemidirectProduct.lift.
lemma lift_compat : ∀ g : Multiplicative ℤ,
    fromKlein.comp ((swapAction g).toMonoidHom) =
    (MulAut.conj (fromZ g)).toMonoidHom.comp fromKlein := by
  intro g
  -- Prove pointwise first
  -- Prove: ∀ x, fromKlein ((swapAut ^ g.toAdd) x) = pt^g.toAdd * fromKlein x * (pt^g.toAdd)⁻¹
  -- Induction on g.toAdd, quantifying over x
  suffices pointwise : ∀ (n : ℤ) (x : Z2xZ2),
      fromKlein ((swapAut ^ n) x) = pt ^ n * fromKlein x * (pt ^ n)⁻¹ by
    apply MonoidHom.ext; intro x
    have h := pointwise g.toAdd x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
               fromZ_apply, swapAction, MonoidHom.coe_mk, OneHom.coe_mk] at h ⊢
    exact h
  intro n
  induction n using Int.induction_on with
  | zero => intro x; simp [zpow_zero, MulAut.one_apply]
  | succ n ih =>
    intro x
    have step1 : swapAut ^ ((↑n : ℤ) + 1) = swapAut ^ (↑n : ℤ) * swapAut ^ (1 : ℤ) := zpow_add swapAut ↑n 1
    rw [step1, MulAut.mul_apply, zpow_one, ih, conj_pt_fromKlein]
    rw [show pt ^ ((↑n : ℤ) + 1) = pt ^ (↑n : ℤ) * pt ^ (1 : ℤ) from zpow_add pt ↑n 1, zpow_one]
    group
  | pred n ih =>
    intro x
    have swapAut_symm : swapAut.symm = swapAut := swapAut_inv
    have step1 : swapAut ^ ((-↑n : ℤ) - (1 : ℤ)) = swapAut ^ (-↑n : ℤ) * swapAut ^ ((-1 : ℤ)) := by
      rw [sub_eq_add_neg]; exact zpow_add swapAut (-↑n) (-1)
    rw [step1, zpow_neg_one, MulAut.mul_apply, MulAut.inv_apply,
        swapAut_symm, ih, conj_ptinv_fromKlein]
    have step2 : pt ^ ((-↑n : ℤ) - (1 : ℤ)) = pt ^ (-↑n : ℤ) * pt ^ ((-1 : ℤ)) := by
      rw [sub_eq_add_neg]; exact zpow_add pt (-↑n) (-1)
    rw [step2, zpow_neg_one]
    group

def fromSDP : Z2xZ2_sdp_Z →* PG :=
  SemidirectProduct.lift fromKlein fromZ lift_compat

-- ════════════════════════════════════════════════════════════
-- § 6. The Isomorphism
-- ════════════════════════════════════════════════════════════

lemma toSDP_comp_fromKlein : toSDP.comp fromKlein = SemidirectProduct.inl := by
  apply MonoidHom.ext; intro ⟨x1, x2⟩
  show toSDP (fromKlein (Multiplicative.ofAdd (x1, x2))) =
    SemidirectProduct.inl (Multiplicative.ofAdd (x1, x2))
  simp only [fromKlein, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  fin_cases x1 <;> fin_cases x2 <;>
    simp only [ZMod.val, pow_zero, pow_one, one_mul, mul_one, map_mul, map_inv,
                map_one, toSDP, pb, swapAction] <;>
    rfl

lemma right_inv : ∀ x : Z2xZ2_sdp_Z, toSDP (fromSDP x) = x := by
  suffices h : toSDP.comp fromSDP = MonoidHom.id _ by
    intro x; exact DFunLike.congr_fun h x
  apply SemidirectProduct.hom_ext
  · -- On inl: toSDP ∘ fromKlein = inl
    apply MonoidHom.ext; intro x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    show toSDP (fromSDP (SemidirectProduct.inl x)) = SemidirectProduct.inl x
    simp only [fromSDP, SemidirectProduct.lift_inl]
    exact DFunLike.congr_fun toSDP_comp_fromKlein x
  · -- On inr: toSDP ∘ fromZ = inr
    apply MonoidHom.ext; intro g
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    show toSDP (fromSDP (SemidirectProduct.inr g)) = SemidirectProduct.inr g
    simp only [fromSDP, SemidirectProduct.lift_inr, fromZ_apply, map_zpow,
               toSDP, PresentedGroup.toGroup.of, genMap]
    -- Goal: inr(ofAdd 1) ^ g.toAdd = inr g
    rw [← MonoidHom.map_zpow SemidirectProduct.inr (Multiplicative.ofAdd (1:ℤ)) g.toAdd]
    congr 1
    -- Goal: ofAdd 1 ^ g.toAdd = g in Multiplicative ℤ
    rw [← Int.ofAdd_mul, one_mul, ofAdd_toAdd]

lemma left_inv : ∀ x : PG, fromSDP (toSDP x) = x := by
  have key : (fromSDP.comp toSDP) = MonoidHom.id _ := by
    apply PresentedGroup.ext; intro x
    cases x with
    | a =>
      show fromSDP (toSDP pa) = pa
      haveI : Fact (1 < 2) := ⟨by omega⟩
      simp only [toSDP, PresentedGroup.toGroup.of, genMap,
                  fromSDP, SemidirectProduct.lift_inl, fromKlein,
                  MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
                  ZMod.val_zero, ZMod.val_one, pow_one, pow_zero, mul_one]
    | t =>
      show fromSDP (toSDP pt) = pt
      simp only [toSDP, PresentedGroup.toGroup.of, genMap,
                  fromSDP, SemidirectProduct.lift_inr, fromZ_apply,
                  toAdd_ofAdd, zpow_one]
  intro x
  exact DFunLike.congr_fun key x

def pgIso : PG ≃* Z2xZ2_sdp_Z :=
  MulEquiv.ofBijective toSDP ⟨
    Function.HasLeftInverse.injective ⟨fromSDP, left_inv⟩,
    Function.HasRightInverse.surjective ⟨fromSDP, right_inv⟩⟩

-- ════════════════════════════════════════════════════════════
-- § 7. Short Exact Sequence: 1 → Z/2×Z/2 → PG → Z → 1
-- ════════════════════════════════════════════════════════════

/-- The injection Z/2 × Z/2 → PG, sending (x₁,x₂) ↦ pa^x₁ * pb^x₂. -/
abbrev ι : Z2xZ2 →* PG := fromKlein

/-- The projection PG → Z, sending pa ↦ 0, pt ↦ 1. -/
abbrev π : PG →* Multiplicative ℤ := SemidirectProduct.rightHom.comp toSDP

-- Helper: toSDP ∘ ι = inl
private lemma toSDP_comp_ι : toSDP.comp ι = SemidirectProduct.inl :=
  toSDP_comp_fromKlein

-- The composition π ∘ ι is trivial (ι lands in the kernel of π).
lemma π_comp_ι : π.comp ι = 1 := by
  apply MonoidHom.ext; intro x
  show (SemidirectProduct.rightHom.comp toSDP).comp fromKlein x = 1
  have h : (toSDP.comp fromKlein) x = SemidirectProduct.inl x := by
    exact DFunLike.congr_fun toSDP_comp_ι x
  show SemidirectProduct.rightHom (toSDP (fromKlein x)) = 1
  rw [show toSDP (fromKlein x) = SemidirectProduct.inl x from h]
  simp [SemidirectProduct.rightHom]

lemma ι_injective : Function.Injective ι := by
  intro x y hxy
  have hx : toSDP (ι x) = SemidirectProduct.inl x := DFunLike.congr_fun toSDP_comp_ι x
  have hy : toSDP (ι y) = SemidirectProduct.inl y := DFunLike.congr_fun toSDP_comp_ι y
  have h : toSDP (ι x) = toSDP (ι y) := congr_arg toSDP hxy
  rw [hx, hy] at h
  exact SemidirectProduct.inl_injective h

lemma π_surjective : Function.Surjective π := by
  intro g
  refine ⟨pt ^ g.toAdd, ?_⟩
  show SemidirectProduct.rightHom (toSDP (pt ^ g.toAdd)) = g
  simp only [map_zpow, toSDP, PresentedGroup.toGroup.of, genMap,
             SemidirectProduct.rightHom_inr]
  rw [← Int.ofAdd_mul, one_mul, ofAdd_toAdd]

lemma range_ι_eq_ker_π : MonoidHom.range ι = MonoidHom.ker π := by
  ext x
  constructor
  · -- range ι ≤ ker π: if x = ι n, then π x = 1
    rintro ⟨n, rfl⟩
    simp only [MonoidHom.mem_ker]
    show (π.comp ι) n = 1
    rw [π_comp_ι]; rfl
  · -- ker π ≤ range ι: if π x = 1, then x ∈ range ι
    intro hx
    simp only [MonoidHom.mem_ker] at hx
    -- hx : rightHom (toSDP x) = 1, i.e., (toSDP x).right = 1
    change SemidirectProduct.rightHom (toSDP x) = 1 at hx
    have hright : (toSDP x).right = 1 := hx
    -- Reconstruct: toSDP x = inl (toSDP x).left
    have hsdp : toSDP x = SemidirectProduct.inl (toSDP x).left := by
      rw [← SemidirectProduct.inl_left_mul_inr_right (toSDP x)]
      simp [hright]
    -- Apply fromSDP to get x back
    have hleft := left_inv x
    rw [show fromSDP (toSDP x) = fromKlein (toSDP x).left from by
      rw [hsdp]; simp [fromSDP, SemidirectProduct.lift_inl]] at hleft
    refine ⟨(toSDP x).left, ?_⟩
    show ι (toSDP x).left = x
    show fromKlein (toSDP x).left = x
    exact hleft

/-- The short exact sequence 1 → Z/2×Z/2 → PG → Z → 1. -/
theorem short_exact_sequence :
    Function.Injective ι ∧ Function.Surjective π ∧ MonoidHom.range ι = MonoidHom.ker π :=
  ⟨ι_injective, π_surjective, range_ι_eq_ker_π⟩

-- ════════════════════════════════════════════════════════════
-- § 8. LHS Spectral Sequence: E₂ page for 1 → V₄ → PG → ℤ → 1
-- ════════════════════════════════════════════════════════════

/-!
### Lyndon–Hochschild–Serre spectral sequence

For the short exact sequence `1 → V₄ → PG → ℤ → 1` (§ 7),
the cohomological LHS spectral sequence reads

  `E₂^{p,q} = Hᵖ(ℤ; Hᵍ(V₄; ℤ))  ⟹  H^{p+q}(PG; ℤ)`

Since `ℤ` has cohomological dimension 1, `E₂^{p,q} = 0` for `p ≥ 2`.
The spectral sequence is concentrated in columns `p = 0, 1`,
so all differentials `d_r : E_r^{p,q} → E_r^{p+r, q−r+1}` (for `r ≥ 2`)
land in `p ≥ 2`. Hence **E₂ = E_∞**.

The two nonzero columns are:
  - `E₂^{0,q} = (Hᵍ(V₄; ℤ))^ℤ` — invariants under the swap action
  - `E₂^{1,q} = Hᵍ(V₄; ℤ)_ℤ`   — coinvariants (cokernel of `t − 1`)

The conjugation action of the generator `t ∈ ℤ` on `V₄` is the swap
`σ : (x₁, x₂) ↦ (x₂, x₁)`, as formalized by `swapAut` (§ 1).

#### Integral cohomology of `V₄ = ℤ/2 × ℤ/2` (Künneth theorem)

Using `H^{2k}(ℤ/2; ℤ) = ℤ/2` (k ≥ 1), `H^{odd}(ℤ/2; ℤ) = 0`:

  | q |  Hᵍ(V₄; ℤ) | σ*-action                       |
  |---|-------------|---------------------------------|
  | 0 | ℤ           | trivial                         |
  | 1 | 0           | —                               |
  | 2 | (ℤ/2)²      | swap: (e₁, e₂) ↦ (e₂, e₁)      |
  | 3 | ℤ/2         | trivial (the Tor class β(xy))   |
  | 4 | (ℤ/2)³      | reversal: (a,b,c) ↦ (c,b,a)    |

For `H²`: generators are `e₁ = α ⊗ 1`, `e₂ = 1 ⊗ α` where
`α` generates `H²(ℤ/2; ℤ) = ℤ/2`. Swap exchanges factors.

For `H³`: the unique Künneth Tor class `τ = β(xy)` (Bockstein of
`xy ∈ H²(V₄; 𝔽₂)`) is swap-invariant since `σ*(xy) = yx = xy` in `𝔽₂`.

For `H⁴`: basis `{α²⊗1, α⊗α, 1⊗α²}` with swap `(a,b,c) ↦ (c,b,a)`.

#### E₂ page

  | q\p |    0    |    1    | ≥ 2 |
  |-----|---------|---------|-----|
  |  0  |    ℤ    |    ℤ    |  0  |
  |  1  |    0    |    0    |  0  |
  |  2  |  ℤ/2   |  ℤ/2   |  0  |
  |  3  |  ℤ/2   |  ℤ/2   |  0  |
  |  4  | (ℤ/2)² | (ℤ/2)² |  0  |

#### Convergence (E₂ = E_∞)

`H^n(PG; ℤ)` sits in `0 → E_∞^{1,n−1} → Hⁿ → E_∞^{0,n} → 0`:

  - `H⁰ ≅ ℤ`
  - `H¹ ≅ ℤ`
  - `H² ≅ ℤ/2`
  - `H³ ∈ {ℤ/4, (ℤ/2)²}`   (extension of ℤ/2 by ℤ/2)
  - `H⁴ ∈ {(ℤ/2)³, ℤ/4 × ℤ/2}` (extension of (ℤ/2)² by ℤ/2)
-/

-- ┌──────────────────────────────────────────────────────────
-- │ E₂^{*,0}: H⁰(V₄; ℤ) = ℤ, trivial action
-- └──────────────────────────────────────────────────────────
-- E₂^{0,0} = ℤ^ℤ = ℤ
-- E₂^{1,0} = ℤ/(t−1)ℤ = ℤ/0 = ℤ
-- (trivial action → both invariants and coinvariants are ℤ)

-- ┌──────────────────────────────────────────────────────────
-- │ E₂^{*,1}: H¹(V₄; ℤ) = 0
-- └──────────────────────────────────────────────────────────
-- E₂^{0,1} = 0,  E₂^{1,1} = 0

-- ┌──────────────────────────────────────────────────────────
-- │ E₂^{*,2}: H²(V₄; ℤ) ≅ (ℤ/2)², swap action
-- └──────────────────────────────────────────────────────────

/-- The swap on `(ℤ/2)²` fixes exactly the diagonal elements. -/
lemma lhs_swap_fixed (p : ZMod 2 × ZMod 2) :
    Prod.swap p = p ↔ p.1 = p.2 := by
  rcases p with ⟨x, y⟩
  simp only [Prod.swap, Prod.mk.injEq]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨h.symm, h⟩⟩

/-- `E₂^{0,2}`: 2 swap-fixed points in `(ℤ/2)²`, so the invariant
    submodule has order 2, i.e. `E₂^{0,2} ≅ ℤ/2`. -/
lemma lhs_E2_02_card :
    (Finset.univ.filter
      (fun p : ZMod 2 × ZMod 2 => Prod.swap p = p)).card = 2 := by
  decide

/-- `E₂^{1,2}`: the image of `swap − id` on `(ℤ/2)²` has 2 elements
    (the diagonal), so the coinvariant quotient has order `4/2 = 2`,
    i.e. `E₂^{1,2} ≅ ℤ/2`. -/
lemma lhs_E2_12_image_card :
    (Finset.univ.image
      (fun p : ZMod 2 × ZMod 2 => (p.2 - p.1, p.1 - p.2))).card = 2 := by
  decide

-- ┌──────────────────────────────────────────────────────────
-- │ E₂^{*,3}: H³(V₄; ℤ) ≅ ℤ/2, trivial action
-- └──────────────────────────────────────────────────────────
-- The generator τ = β(xy) ∈ Tor₁(H²,H²) is swap-invariant because
-- σ*(xy) = yx = xy in 𝔽₂-coefficients, and β commutes with σ*.
-- Trivial action on ℤ/2 → invariants = ℤ/2, coinvariants = ℤ/2:
-- E₂^{0,3} ≅ ℤ/2,  E₂^{1,3} ≅ ℤ/2

-- ┌──────────────────────────────────────────────────────────
-- │ E₂^{*,4}: H⁴(V₄; ℤ) ≅ (ℤ/2)³, reversal action
-- └──────────────────────────────────────────────────────────

/-- The reversal action `(a,b,c) ↦ (c,b,a)` on `(ℤ/2)³`, representing
    `σ*` on the Künneth basis `{α²⊗1, α⊗α, 1⊗α²}` of `H⁴(V₄; ℤ)`. -/
def lhs_reversal (p : ZMod 2 × ZMod 2 × ZMod 2) :
    ZMod 2 × ZMod 2 × ZMod 2 :=
  (p.2.2, p.2.1, p.1)

/-- The reversal is an involution. -/
lemma lhs_reversal_involutive : Function.Involutive lhs_reversal := by
  intro ⟨x, y, z⟩; rfl

/-- The reversal fixes elements `(a,b,a)`, giving 4 fixed points:
    `E₂^{0,4} ≅ (ℤ/2)²`. -/
lemma lhs_E2_04_card :
    (Finset.univ.filter
      (fun p : ZMod 2 × ZMod 2 × ZMod 2 => lhs_reversal p = p)).card = 4 := by
  decide

/-- The image of `reversal − id` on `(ℤ/2)³` has 2 elements `{(0,0,0),(1,0,1)}`,
    so the coinvariant quotient has order `8/2 = 4`:
    `E₂^{1,4} ≅ (ℤ/2)²`. -/
lemma lhs_E2_14_image_card :
    (Finset.univ.image
      (fun p : ZMod 2 × ZMod 2 × ZMod 2 =>
        (p.2.2 - p.1, p.2.1 - p.2.1, p.1 - p.2.2))).card = 2 := by
  decide

-- ┌──────────────────────────────────────────────────────────
-- │ E₂^{p,q} = 0 for p ≥ 2
-- └──────────────────────────────────────────────────────────
-- Since cd(ℤ) = 1, all higher cohomology of ℤ vanishes.
-- This means E₂ = E_∞ and the spectral sequence collapses:
--
--   0 → E_∞^{1,n−1} → Hⁿ(PG;ℤ) → E_∞^{0,n} → 0
--
-- For n ≤ 2 the extension is forced; for n ≥ 3 it requires
-- additional information (e.g., the d₂-differential on the
-- chain level, or explicit cup-product computations).

end
