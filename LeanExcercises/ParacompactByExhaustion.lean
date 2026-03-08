import Mathlib.Topology.Compactness.Paracompact

open Set Filter Topology in
/-- An exhaustion by compact sets yields a paracompact union: if each K(i) is contained in the
interior of K(i+1) and each K(i) is compact, then the union of all K(i) is paracompact
in the subspace topology. -/
theorem paracompact_of_compact_exhaustion {X : Type*} [TopologicalSpace X] [T2Space X]
    (K : ℕ → Set X)
    (hK_compact : ∀ i, IsCompact (K i))
    (hK_subset_interior : ∀ i, K i ⊆ interior (K (i + 1))) :
    ParacompactSpace ↥(⋃ i, K i) := by
  -- Each K i lies in the subtype's range, so its preimage is compact in the subtype
  have hrange : ∀ i, K i ⊆ range (Subtype.val : ↥(⋃ i, K i) → X) := by
    intro i; simp only [Subtype.range_coe_subtype, setOf_mem_eq]; exact subset_iUnion K i
  have hcsub : ∀ i, IsCompact (Subtype.val ⁻¹' K i : Set ↥(⋃ i, K i)) := fun i =>
    IsInducing.subtypeVal.isCompact_preimage' (hK_compact i) (hrange i)
  -- σ-compact: the preimages of K i cover univ in the subtype
  haveI : SigmaCompactSpace ↥(⋃ i, K i) :=
    ⟨⟨fun i => Subtype.val ⁻¹' K i, hcsub, by
      ext ⟨x, hx⟩; simp only [mem_iUnion, mem_preimage, mem_univ, iff_true]; exact mem_iUnion.mp hx⟩⟩
  -- Weakly locally compact: x ∈ K n implies interior(K (n+1)) is a neighborhood with compact closure
  haveI : WeaklyLocallyCompactSpace ↥(⋃ i, K i) := ⟨fun ⟨x, hx⟩ => by
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact ⟨_, hcsub (n + 1), mem_of_superset
      ((isOpen_interior.preimage continuous_subtype_val).mem_nhds (hK_subset_interior n hn))
      (preimage_mono interior_subset)⟩⟩
  -- T₂ is inherited; apply Mathlib's instance: weakly locally compact + σ-compact + T₂ → paracompact
  infer_instance
