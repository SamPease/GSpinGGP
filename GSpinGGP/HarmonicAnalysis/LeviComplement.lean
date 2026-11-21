/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The projection onto a complement of a normal subgroup

General group theory used for Levi subgroups (`GGP/LeviSubgroup.lean`).  If `H` is a complement of a normal subgroup `N` of `G`
(Mathlib's `Subgroup.IsComplement'`), every `g` is `h n` uniquely, and `g ↦ h` is a
homomorphism `G →* H` (`Subgroup.IsComplement'.proj`, through Mathlib's
`Subgroup.IsComplement'.QuotientMulEquiv : G ⧸ N ≃* H`).  For topological groups this
homomorphism is continuous as soon as `H` is σ-compact and `G ⧸ N` is locally compact and
Hausdorff (`Subgroup.IsComplement'.continuous_proj`): the bijection `H → G ⧸ N` is continuous,
hence open by the open mapping theorem (Mathlib's `MonoidHom.isOpenMap_of_sigmaCompact`).
For a parabolic subgroup `P = M U` of a `p`-adic group this is the continuity of `p ↦ m`.
-/

noncomputable section

open Topology

namespace Subgroup

variable {G : Type*} [Group G] {H N : Subgroup G}

/-- The complement element `h.QuotientMulEquiv q` represents the coset `q`. -/
theorem IsComplement'.mk_quotientMulEquiv [N.Normal] (h : H.IsComplement' N) (q : G ⧸ N) :
    (((h.QuotientMulEquiv q : H) : G) : G ⧸ N) = q :=
  h.quotientGroupMk_leftQuotientEquiv q

theorem IsComplement'.quotientMulEquiv_mk [N.Normal] (h : H.IsComplement' N) (x : H) :
    h.QuotientMulEquiv ((x : G) : G ⧸ N) = x := by
  rw [show ((x : G) : G ⧸ N) = h.QuotientMulEquiv.symm x from rfl, MulEquiv.apply_symm_apply]

/-- **The projection onto a complement**: for a complement `H` of a normal subgroup `N`,
`g = h n ↦ h`. -/
def IsComplement'.proj [N.Normal] (h : H.IsComplement' N) : G →* H :=
  h.QuotientMulEquiv.toMonoidHom.comp (QuotientGroup.mk' N)

theorem IsComplement'.proj_mul [N.Normal] (h : H.IsComplement' N) (x : H) {n : G} (hn : n ∈ N) :
    h.proj ((x : G) * n) = x := by
  rw [proj, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    show (((x : G) * n : G) : G ⧸ N) = ((x : G) : G ⧸ N) from
      QuotientGroup.eq.mpr (by simpa using hn)]
  exact h.quotientMulEquiv_mk x

theorem IsComplement'.proj_coe [N.Normal] (h : H.IsComplement' N) (x : H) : h.proj x = x := by
  simpa using h.proj_mul x N.one_mem

theorem IsComplement'.proj_eq_one [N.Normal] (h : H.IsComplement' N) {n : G} (hn : n ∈ N) :
    h.proj n = 1 := by
  simpa using h.proj_mul 1 hn

/-- `g = proj(g) · n` with `n ∈ N`. -/
theorem IsComplement'.inv_proj_mul_mem [N.Normal] (h : H.IsComplement' N) (g : G) :
    ((h.proj g : H) : G)⁻¹ * g ∈ N :=
  QuotientGroup.eq.mp (h.mk_quotientMulEquiv (g : G ⧸ N))

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The projection onto a complement is continuous** when `H` is σ-compact and `G ⧸ N` is a
locally compact Hausdorff space: the continuous bijective homomorphism `H → G ⧸ N` is open by the
open mapping theorem (`MonoidHom.isOpenMap_of_sigmaCompact`), so its inverse is continuous. -/
theorem IsComplement'.continuous_proj [N.Normal] (h : H.IsComplement' N) [SigmaCompactSpace H]
    [LocallyCompactSpace (G ⧸ N)] [T2Space (G ⧸ N)] : Continuous h.proj := by
  set f : H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hf : Continuous f := continuous_quotient_mk'.comp continuous_subtypeVal
  have hfe : ∀ q, f (h.QuotientMulEquiv q) = q := h.mk_quotientMulEquiv
  have hef : ∀ x, h.QuotientMulEquiv (f x) = x := h.quotientMulEquiv_mk
  have hsurj : Function.Surjective f := fun q => ⟨_, hfe q⟩
  have hopen : IsOpenMap f := f.isOpenMap_of_sigmaCompact hsurj hf
  have he : Continuous h.QuotientMulEquiv := by
    rw [continuous_def]
    intro S hS
    convert hopen S hS using 1
    ext q
    refine ⟨fun hq => ⟨_, hq, hfe q⟩, ?_⟩
    rintro ⟨x, hx, rfl⟩
    simpa [Set.mem_preimage, hef] using hx
  exact he.comp continuous_quotient_mk'

end Subgroup
