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

noncomputable section

-- ════════════════════════════════════════════════════════════
-- § 1. The Semidirect Product
-- ════════════════════════════════════════════════════════════

abbrev Z2xZ2 := Multiplicative (ZMod 2 × ZMod 2)

def actionOfAut (α : MulAut Z2xZ2) : Multiplicative ℤ →* MulAut Z2xZ2 where
  toFun n := α ^ n.toAdd
  map_one' := zpow_zero α
  map_mul' a b := zpow_add α a.toAdd b.toAdd

def swapAut : MulAut Z2xZ2 :=
  AddEquiv.toMultiplicative (AddEquiv.prodComm (M := ZMod 2) (N := ZMod 2))

abbrev Z2xZ2_sdp_Z := Z2xZ2 ⋊[actionOfAut swapAut] Multiplicative ℤ

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

def rels : Set (FreeGroup Gen) :=
  { fa * ft^2 * fa⁻¹ * (ft^2)⁻¹,
    fa * (ft⁻¹ * fa * ft) * fa⁻¹ * (ft⁻¹ * fa * ft)⁻¹,
    fa^2 }

abbrev PG := PresentedGroup rels
abbrev pa : PG := PresentedGroup.of a
abbrev pt : PG := PresentedGroup.of t

-- ════════════════════════════════════════════════════════════
-- § 3. Forward Map: PG → SDP
-- ════════════════════════════════════════════════════════════

def genMap : Gen → Z2xZ2_sdp_Z
  | a => SemidirectProduct.inl (Multiplicative.ofAdd ((1:ZMod 2),(0:ZMod 2)))
  | t => SemidirectProduct.inr (Multiplicative.ofAdd (1:ℤ))

set_option maxHeartbeats 400000 in
lemma genMap_rels : ∀ r ∈ rels, FreeGroup.lift genMap r = 1 := by
  intro r hr
  simp only [rels, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl <;> {
    apply SemidirectProduct.ext <;>
    simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of,
               SemidirectProduct.mul_left, SemidirectProduct.inv_left,
               SemidirectProduct.one_left, SemidirectProduct.mul_right,
               SemidirectProduct.inv_right, SemidirectProduct.one_right,
               genMap, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
               SemidirectProduct.left_inr, SemidirectProduct.right_inr,
               actionOfAut, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
               toAdd_one, MulAut.mul_apply, MulAut.inv_apply, zpow_ofNat] <;>
    first | rfl
  }

def toSDP : PG →* Z2xZ2_sdp_Z :=
  PresentedGroup.toGroup genMap_rels

-- ════════════════════════════════════════════════════════════
-- § 4. Relations in PG
-- ════════════════════════════════════════════════════════════

abbrev pb : PG := pt⁻¹ * pa * pt

private lemma inv_eq_self_of_sq {G : Type*} [Group G] {g : G} (h : g ^ 2 = 1) :
    g⁻¹ = g := by
  rw [sq] at h
  calc g⁻¹ = g⁻¹ * (g * g) := by rw [h, mul_one]
    _ = g := by group

private lemma comm_of_comm_eq_one {G : Type*} [Group G] {x y : G}
    (h : x * y * x⁻¹ * y⁻¹ = 1) : x * y = y * x := by
  calc x * y
      = x * y * (x⁻¹ * y⁻¹) * (y * x) := by group
    _ = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = 1 * (y * x) := by rw [h]
    _ = y * x := one_mul _

lemma pg_a_sq : pa ^ 2 = 1 :=
  PresentedGroup.one_of_mem (show fa ^ 2 ∈ rels by simp [rels])

lemma pg_a_inv : pa⁻¹ = pa := inv_eq_self_of_sq pg_a_sq

lemma pg_comm_a_t2 : pa * pt ^ 2 = pt ^ 2 * pa :=
  comm_of_comm_eq_one (PresentedGroup.one_of_mem (show _ ∈ rels by simp [rels]))

lemma pg_comm_a_b : pa * pb = pb * pa :=
  comm_of_comm_eq_one (PresentedGroup.one_of_mem (show _ ∈ rels by simp [rels]))

lemma pg_b_sq : pb ^ 2 = 1 := by
  show (pt⁻¹ * pa * pt) ^ 2 = 1
  have : pt⁻¹ * pa * pt * (pt⁻¹ * pa * pt) = pt⁻¹ * (pa * pa) * pt := by group
  rw [sq, this, show pa * pa = pa ^ 2 from (sq pa).symm, pg_a_sq]; group

lemma pg_b_inv : pb⁻¹ = pb := inv_eq_self_of_sq pg_b_sq

lemma pg_tbt : pt * pb * pt⁻¹ = pa := by
  show pt * (pt⁻¹ * pa * pt) * pt⁻¹ = pa; group

lemma pg_conj_pt_pa : pt * pa * pt⁻¹ = pb := by
  have h := pg_comm_a_t2
  have : pt * pa = pt⁻¹ * pa * (pt * pt) := by
    calc pt * pa
        = pt⁻¹ * (pt ^ 2 * pa) := by group
      _ = pt⁻¹ * (pa * pt ^ 2) := by rw [h]
      _ = pt⁻¹ * pa * (pt * pt) := by rw [sq]; group
  calc pt * pa * pt⁻¹
      = pt⁻¹ * pa * (pt * pt) * pt⁻¹ := by rw [this]
    _ = pt⁻¹ * pa * pt := by group

-- conj by pt⁻¹ also swaps: pt⁻¹ * pb * pt = pa
lemma pg_conj_ptinv_pb : pt⁻¹ * pb * pt = pa := by
  have := pg_conj_pt_pa
  -- pt * pa * pt⁻¹ = pb, so pa = pt⁻¹ * pb * pt
  calc pt⁻¹ * pb * pt = pt⁻¹ * (pt * pa * pt⁻¹) * pt := by rw [pg_conj_pt_pa]
    _ = pa := by group

-- ════════════════════════════════════════════════════════════
-- § 5. Inverse Map: SDP → PG
-- ════════════════════════════════════════════════════════════

private lemma zmod2_pow_add (g : PG) (hg : g ^ 2 = 1) (x y : ZMod 2) :
    g ^ (x + y).val = g ^ x.val * g ^ y.val := by
  have hg2 : g * g = 1 := by rwa [sq] at hg
  fin_cases x <;> fin_cases y <;> simp_all [ZMod.val, pow_succ, pow_zero] ; norm_num

private lemma pow_comm_of_comm {G : Type*} [Group G] (a b : G) (hab : a * b = b * a) :
    ∀ m n : ℕ, a ^ m * b ^ n = b ^ n * a ^ m := by
  intro m; induction m with
  | zero => intro _; simp [pow_zero]
  | succ m ih => intro n; calc a ^ (m + 1) * b ^ n
        = a ^ m * a * b ^ n := by rw [pow_succ]
      _ = a ^ m * (a * b ^ n) := by group
      _ = a ^ m * (b ^ n * a) := by
          congr 1; induction n with
          | zero => simp
          | succ n ihn =>
            calc a * b ^ (n + 1) = a * (b ^ n * b) := by rw [pow_succ]
              _ = (a * b ^ n) * b := by group
              _ = (b ^ n * a) * b := by rw [ihn]
              _ = b ^ n * (a * b) := by group
              _ = b ^ n * (b * a) := by rw [hab]
              _ = b ^ (n + 1) * a := by rw [pow_succ]; group
      _ = (a ^ m * b ^ n) * a := by group
      _ = (b ^ n * a ^ m) * a := by rw [ih n]
      _ = b ^ n * a ^ (m + 1) := by rw [pow_succ]; group

def fromKlein : Z2xZ2 →* PG where
  toFun n := pa ^ (Multiplicative.toAdd n).1.val * pb ^ (Multiplicative.toAdd n).2.val
  map_one' := by simp [ZMod.val]
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
          rw [pow_comm_of_comm pa pb pg_comm_a_b y1 x2]
      _ = pa ^ x1 * pb ^ x2 * (pa ^ y1 * pb ^ y2) := by group

def fromZ : Multiplicative ℤ →* PG := zpowersHom PG pt

@[simp] lemma fromZ_apply (n : Multiplicative ℤ) : fromZ n = pt ^ n.toAdd := rfl

-- Helper: a general conj_swap tactic for checking on 4 elements
private lemma conj_swap_hom_eq (u : PG)
    (hu_a : u * pa * u⁻¹ = pb) (hu_b : u * pb * u⁻¹ = pa) :
    fromKlein.comp swapAut.toMonoidHom =
    (MulAut.conj u).toMonoidHom.comp fromKlein := by
  apply MonoidHom.ext; intro ⟨x1, x2⟩
  show fromKlein (swapAut (Multiplicative.ofAdd (x1, x2))) =
    u * fromKlein (Multiplicative.ofAdd (x1, x2)) * u⁻¹
  simp only [swapAut_apply, fromKlein, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  -- 4 cases: (0,0), (0,1), (1,0), (1,1)
  -- After fin_cases + simp, we need: 1 = u*1*u⁻¹, pb = u*pa*u⁻¹,
  -- pa = u*pb*u⁻¹, pa*pb = u*(pb*pa)*u⁻¹
  -- But Lean shows pb as pt⁻¹*pa*pt and u⁻¹ as u^(-1)
  fin_cases x1 <;> fin_cases x2 <;>
    simp only [ZMod.val, pow_zero, pow_one, one_mul, mul_one]
  -- Case (0,0): 1 = u * 1 * u⁻¹
  · group
  -- Case (0,1): pa = u * pb * u⁻¹  (hu_b.symm)
  · exact hu_b.symm
  -- Case (1,0): pb = u * pa * u⁻¹  (hu_a.symm)
  · exact hu_a.symm
  -- Case (1,1): pa * pb = u * (pa * pb) * u⁻¹
  · calc pa * pb
        = (u * pb * u⁻¹) * (u * pa * u⁻¹) := by rw [hu_b, hu_a]
      _ = u * (pb * pa) * u⁻¹ := by group
      _ = u * (pa * pb) * u⁻¹ := by rw [pg_comm_a_b]

lemma conj_pt_fromKlein (x : Z2xZ2) :
    fromKlein (swapAut x) = pt * fromKlein x * pt⁻¹ := by
  have key := conj_swap_hom_eq pt pg_conj_pt_pa pg_tbt
  exact congr_fun (congr_arg DFunLike.coe key) x

lemma conj_ptinv_fromKlein (x : Z2xZ2) :
    fromKlein (swapAut x) = pt⁻¹ * fromKlein x * pt := by
  -- pb = pt⁻¹ * pa * pt (def), pa = pt⁻¹ * pb * pt (pg_conj_ptinv_pb)
  have ha : pt⁻¹ * pa * (pt⁻¹)⁻¹ = pb := by rw [inv_inv]
  have hb : pt⁻¹ * pb * (pt⁻¹)⁻¹ = pa := by rw [inv_inv]; exact pg_conj_ptinv_pb
  have key := conj_swap_hom_eq pt⁻¹ ha hb
  exact congr_fun (congr_arg DFunLike.coe key) x

lemma swapAut_inv : swapAut⁻¹ = swapAut := by
  rw [← mul_left_cancel_iff (a := swapAut), mul_inv_cancel, ← sq, swapAut_sq]

-- Compatibility condition for SemidirectProduct.lift.
lemma lift_compat : ∀ g : Multiplicative ℤ,
    fromKlein.comp ((actionOfAut swapAut g).toMonoidHom) =
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
               fromZ_apply, actionOfAut, MonoidHom.coe_mk, OneHom.coe_mk] at h ⊢
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

set_option maxHeartbeats 800000 in
lemma right_inv : ∀ x : Z2xZ2_sdp_Z, toSDP (fromSDP x) = x := by
  suffices h : toSDP.comp fromSDP = MonoidHom.id _ by
    intro x; exact DFunLike.congr_fun h x
  apply SemidirectProduct.hom_ext
  · -- On inl: toSDP ∘ fromKlein = inl
    apply MonoidHom.ext; intro x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    show toSDP (fromSDP (SemidirectProduct.inl x)) = SemidirectProduct.inl x
    simp only [fromSDP, SemidirectProduct.lift_inl]
    -- Goal: toSDP (fromKlein x) = inl x
    -- fromKlein and toSDP are both MonoidHoms, so their composition is too
    -- Check that (toSDP.comp fromKlein) = inl by checking on the 4 elements
    suffices hh : toSDP.comp fromKlein = SemidirectProduct.inl by
      exact DFunLike.congr_fun hh x
    apply MonoidHom.ext; intro ⟨x1, x2⟩
    show toSDP (fromKlein (Multiplicative.ofAdd (x1, x2))) =
      SemidirectProduct.inl (Multiplicative.ofAdd (x1, x2))
    simp only [fromKlein, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
    fin_cases x1 <;> fin_cases x2 <;>
      simp only [ZMod.val, pow_zero, pow_one, one_mul, mul_one, map_mul, map_inv,
                  map_one, toSDP, PresentedGroup.toGroup.of, genMap, pb,
                  actionOfAut] <;>
      first | rfl
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
      simp only [toSDP, PresentedGroup.toGroup.of, genMap,
                  fromSDP, SemidirectProduct.lift_inl, fromKlein,
                  MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, ZMod.val]
      norm_num
    | t =>
      show fromSDP (toSDP pt) = pt
      simp only [toSDP, PresentedGroup.toGroup.of, genMap,
                  fromSDP, SemidirectProduct.lift_inr, fromZ_apply,
                  toAdd_ofAdd, zpow_one]
  intro x
  exact congr_fun (congr_arg DFunLike.coe key) x

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
private lemma toSDP_comp_ι : toSDP.comp ι = SemidirectProduct.inl := by
  show toSDP.comp fromKlein = SemidirectProduct.inl
  apply MonoidHom.ext; intro ⟨x1, x2⟩
  show toSDP (fromKlein (Multiplicative.ofAdd (x1, x2))) =
    SemidirectProduct.inl (Multiplicative.ofAdd (x1, x2))
  simp only [fromKlein, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  fin_cases x1 <;> fin_cases x2 <;>
    simp only [ZMod.val, pow_zero, pow_one, one_mul, mul_one, map_mul, map_inv,
                map_one, toSDP, PresentedGroup.toGroup.of, genMap, pb, actionOfAut] <;>
    first | rfl

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

end
