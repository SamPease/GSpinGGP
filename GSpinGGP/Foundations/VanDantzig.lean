/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import TauCeti.Topology.Algebra.Group.OpenSubgroup.Compact
import TauCeti.Topology.LocallyConstant.Compact

/-!
# van Dantzig's theorem and compact open subgroups

General facts about totally disconnected locally compact Hausdorff spaces and groups:

* `exists_isCompact_isClopen_between`: a compact open set between a compact set and an open
  neighbourhood of it;
* `exists_subgroup_biInvariant_on`: a locally constant function is, on a compact set, bi-invariant
  under some compact open subgroup;
* `exists_compactOpenSubgroup_ge`: every compact subgroup lies in a compact open subgroup.

van Dantzig's theorem itself (every neighbourhood of `1` contains a compact open subgroup) is Tau
Ceti's `NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup`, with the instance
`IsTopologicalGroup.nonarchimedeanGroup_of_weaklyLocallyCompactSpace`.
-/

open Topology Filter
open scoped Pointwise

namespace GSpinGGP

/-- In a totally disconnected locally compact Hausdorff space, between a compact set and an
open neighbourhood of it there is a compact open (hence clopen) set. -/
theorem exists_isCompact_isClopen_between {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [TotallyDisconnectedSpace X] {K U : Set X} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) : ∃ V, IsCompact V ∧ IsClopen V ∧ K ⊆ V ∧ V ⊆ U := by
  have hloc : ∀ x ∈ K, ∃ W : Set X, IsCompact W ∧ IsClopen W ∧ x ∈ W ∧ W ⊆ U := by
    intro x hx
    obtain ⟨C, hC, hxC, hCU⟩ := exists_compact_subset hU (hKU hx)
    obtain ⟨W, hW, hxW, hWC⟩ :=
      isTopologicalBasis_isClopen.mem_nhds_iff.mp (isOpen_interior.mem_nhds hxC)
    exact ⟨W, hC.of_isClosed_subset hW.1 (hWC.trans interior_subset), hW, hxW,
      hWC.trans (interior_subset.trans hCU)⟩
  choose! W hWc hWcl hxW hWU using hloc
  obtain ⟨t, htK, hcover⟩ :=
    hK.elim_nhds_subcover W (fun x hx => (hWcl x hx).isOpen.mem_nhds (hxW x hx))
  exact ⟨⋃ x ∈ t, W x, t.isCompact_biUnion fun x hx => hWc x (htK x hx),
    isClopen_biUnion_finset fun x hx => hWcl x (htK x hx), hcover,
    Set.iUnion₂_subset fun x hx => hWU x (htK x hx)⟩

section CompactOpenSubgroups

variable {G₀ : Type*} [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀]

/-- **van Dantzig**, in the form used for test functions and smooth vectors: in a locally compact,
totally disconnected Hausdorff group, every neighbourhood of `1` contains a compact open
subgroup. -/
theorem exists_compactOpenSubgroup_subset [T2Space G₀] [LocallyCompactSpace G₀]
    [TotallyDisconnectedSpace G₀] :
    ∀ U ∈ 𝓝 (1 : G₀), ∃ K : Subgroup G₀,
      IsOpen (K : Set G₀) ∧ IsCompact (K : Set G₀) ∧ (K : Set G₀) ⊆ U := fun U hU => by
  obtain ⟨K, hKc, hKU⟩ := NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup.mem_iff.1 hU
  exact ⟨K, K.isOpen, hKc, hKU⟩

/-- **Uniform local constancy**: a locally constant function on a totally disconnected locally
compact Hausdorff group is, on a compact set `C`, invariant under left and right translation by
some compact open subgroup. -/
theorem exists_subgroup_biInvariant_on [T2Space G₀] [LocallyCompactSpace G₀]
    [TotallyDisconnectedSpace G₀] {β : Type*} (f : G₀ → β) (hf : IsLocallyConstant f)
    (C : Set G₀) (hC : IsCompact C) :
    ∃ K : Subgroup G₀, IsOpen (K : Set G₀) ∧ IsCompact (K : Set G₀) ∧
      ∀ c ∈ C, ∀ k ∈ K, ∀ k' ∈ K, f (k * c * k') = f c := by
  obtain ⟨V, hVo, hV1, hV⟩ := IsLocallyConstant.exists_isOpen_forall_mem_eq
    (hf.comp_continuous (by fun_prop : Continuous fun p : G₀ × (G₀ × G₀) => p.2.1 * p.1 * p.2.2))
    hC ((1 : G₀), (1 : G₀))
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp (hVo.mem_nhds hV1)
  obtain ⟨K, hKc, hKU⟩ := NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup.mem_iff.1
    (Filter.inter_mem hu hv)
  refine ⟨K, K.isOpen, hKc, fun c hc k hk k' hk' => ?_⟩
  simpa using hV (k, k') (huv (Set.mk_mem_prod (hKU hk).1 (hKU hk').2)) c hc

/-- In a totally disconnected locally compact Hausdorff group, every compact subgroup `K₀` lies in
a compact open subgroup: `K₀ N` with `N = ⋂_{k ∈ K₀} k U k⁻¹` for a compact open subgroup `U`
(`N` is open by compactness of `K₀`, and normalized by `K₀`). -/
theorem exists_compactOpenSubgroup_ge [T2Space G₀] [LocallyCompactSpace G₀]
    [TotallyDisconnectedSpace G₀] (K₀ : Subgroup G₀) (hK₀ : IsCompact (K₀ : Set G₀)) :
    ∃ K : Subgroup G₀, IsOpen (K : Set G₀) ∧ IsCompact (K : Set G₀) ∧ K₀ ≤ K := by
  obtain ⟨U, hUo, hUc⟩ : ∃ U : Subgroup G₀, IsOpen (U : Set G₀) ∧ IsCompact (U : Set G₀) :=
    let ⟨U, hUc, _⟩ := NonarchimedeanGroup.nhds_one_hasBasis_isCompact_openSubgroup.mem_iff.1
      (Filter.univ_mem (f := 𝓝 (1 : G₀)))
    ⟨U, U.isOpen, hUc⟩
  have hev : ∀ᶠ x in 𝓝 (1 : G₀), ∀ k ∈ (K₀ : Set G₀), k⁻¹ * x * k ∈ U := by
    apply hK₀.eventually_forall_of_forall_eventually
    intro k _
    have hc : Continuous fun p : G₀ × G₀ => p.2⁻¹ * p.1 * p.2 := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hUo.mem_nhds U.one_mem)
  let N : Subgroup G₀ := ⨅ k : K₀, U.comap (MulAut.conj (k : G₀)⁻¹).toMonoidHom
  have hmemN : ∀ x, x ∈ N ↔ ∀ k ∈ K₀, k⁻¹ * x * k ∈ U := by
    intro x
    simp only [N, Subgroup.mem_iInf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv, Subtype.forall]
  have hNo : IsOpen (N : Set G₀) :=
    Subgroup.isOpen_of_mem_nhds N (hev.mono fun x hx => (hmemN x).2 hx)
  have hNU : (N : Set G₀) ⊆ U := fun x hx => by
    simpa using (hmemN x).1 hx 1 K₀.one_mem
  have hNc : IsCompact (N : Set G₀) :=
    hUc.of_isClosed_subset (Subgroup.isClosed_of_isOpen N hNo) hNU
  have hnorm : K₀ ≤ Subgroup.normalizer (N : Set G₀) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hmemN, hmemN]
    constructor
    · intro H k' hk'
      have := H (k⁻¹ * k') (K₀.mul_mem (K₀.inv_mem hk) hk')
      simpa [mul_assoc] using this
    · intro H k' hk'
      have := H (k * k') (K₀.mul_mem hk hk')
      simpa [mul_assoc] using this
  refine ⟨K₀ ⊔ N, Subgroup.isOpen_mono le_sup_right hNo, ?_, le_sup_left⟩
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K₀ N hnorm]
  exact hK₀.mul hNc

/-- A product `H·B` of two subgroups is open as soon as it is a neighbourhood of `1`:
`H B = H · interior (H B) · B`. -/
theorem isOpen_subgroup_mul_of_mem_nhds_one (H B : Subgroup G₀)
    (h : (H : Set G₀) * (B : Set G₀) ∈ 𝓝 (1 : G₀)) : IsOpen ((H : Set G₀) * (B : Set G₀)) := by
  have h1 : (1 : G₀) ∈ interior ((H : Set G₀) * (B : Set G₀)) := mem_interior_iff_mem_nhds.2 h
  have e : (H : Set G₀) * (B : Set G₀) =
      (H : Set G₀) * interior ((H : Set G₀) * (B : Set G₀)) * (B : Set G₀) := by
    apply subset_antisymm
    · rintro _ ⟨x, hx, y, hy, rfl⟩
      exact ⟨x * 1, ⟨x, hx, 1, h1, rfl⟩, y, hy, by rw [mul_one]⟩
    · rintro _ ⟨_, ⟨x, hx, z, hz, rfl⟩, y, hy, rfl⟩
      obtain ⟨u, hu, w, hw, rfl⟩ := interior_subset hz
      exact ⟨x * u, H.mul_mem hx hu, w * y, B.mul_mem hw hy, by simp only [mul_assoc]⟩
  rw [e]
  exact isOpen_interior.mul_left.mul_right

end CompactOpenSubgroups

end GSpinGGP
