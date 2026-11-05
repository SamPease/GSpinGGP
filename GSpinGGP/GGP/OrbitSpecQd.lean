/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.Descent
import GSpinGGP.GGP.RegularNilpotent

/-!
# Luo's orbit `O_x` exists at quasi-split points

For semisimple `x ∈ GSpin(W)(F)` with abelian moved part and `G'_x` quasi-split, the regular
nilpotent orbit `O_x` of `𝔤_x` selected by Luo's recipe (`OrbitSpec`, Luo §7.1) exists
(the hypotheses are those of `IsQdAt`: `W'_x` and `V'_x` quasi-split)
(`exists_orbitSpec_of_quasiSplit`).  Luo's recipe applied to the descended GGP datum
`(W'_x, V'_x)` (`GGPData.restrictFix`) gives the split family of `O_ν` (resp. `O_{−ν}`) in
`V'_x` (resp. `W'_x`) (`exists_orbitNu_family_V`, `exists_orbitNu_family_W`); carried into `V`
(resp. `W`) by the isometric embedding, `regNil` of it lies in `O_ν` on `V'_x`
(`isInOrbitNu_regNil_of_le`) and is a regular element of its side (`side_regNil_bound`); paired with
a regular element of the other side (`exists_side_regNil`) it is regular nilpotent in `𝔤_x`
(`exists_nilReg_of_sides`).  This generalizes `exists_orbitSpec_one` (`x = 1`).
-/

noncomputable section

open CliffordAlgebra Module

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F) {x : GSpin d.QW} (hnd : IsNondeg (d.QW.comp (fixedSub x).subtype))

/-- `K^{dim W'_x} ≃ W'_x` is an isometry `fixQW x ≅ QWfix x`. -/
def fixQWIso : (d.fixQW x).IsometryEquiv (d.QWfix x) where
  toLinearEquiv := d.fixEquiv x
  map_app' _ := rfl

/-- The descended datum is quasi-split when `W'_x` and `V'_x` are. -/
theorem isQuasiSplit_restrictFix (hW : IsQuasiSplitQF (d.QWfix x))
    (hV : IsQuasiSplitQF (d.QVfix x)) : (d.restrictFix x hnd).IsQuasiSplit :=
  ⟨QuadClassify.isQuasiSplitQF_of_isometryEquiv (d.fixQWIso).symm hW,
    QuadClassify.isQuasiSplitQF_of_isometryEquiv
      ((d.fixQWIso).prod (QuadraticMap.IsometryEquiv.refl d.QZ)).symm hV⟩

/-- `dim W'_x` for the descended datum. -/
theorem finrank_restrictFix_W : finrank F (Fin (d.restrictFix x hnd).m → F) =
    finrank F ↥(fixedSub x) := by
  rw [Module.finrank_fin_fun]

/-- `V'_x = W'_x ⊕ Z` as a subspace of `V`. -/
theorem prod_top_eq_fixedSub_incl (x : GSpin d.QW) :
    (fixedSub x).prod (⊤ : Submodule F d.Z) = fixedSub (d.incl x) := by
  ext ⟨w, z⟩
  rw [d.mem_fixedSub_incl_iff, Submodule.mem_prod]
  simp

/-- `dim V'_x = dim (W'_x ⊕ Z)` for the descended datum. -/
theorem finrank_restrictFix_V : finrank F (d.restrictFix x hnd).V =
    finrank F ↥((fixedSub x).prod (⊤ : Submodule F d.Z)) := by
  rw [prod_top_eq_fixedSub_incl, ← (d.QVfixIso x).toLinearEquiv.finrank_eq, Module.finrank_prod,
    Module.finrank_prod, Module.finrank_fin_fun]

set_option maxHeartbeats 400000 in
/-- **Luo's orbit `O_x` exists at quasi-split points** (Luo §7.1, applied to `(G'_x, H'_x)`):
for semisimple `x` with abelian moved part and `W'_x`, `V'_x` quasi-split, some regular nilpotent
orbit of `𝔤_x` contains an element satisfying `OrbitSpec d x`.  Generalizes
`exists_orbitSpec_one`. -/
theorem exists_orbitSpec_of_quasiSplit (x : GSpin d.QW)
    (hx : IsSS F ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
    (hmoved : MovedPartAbelian d.QW x) (hW : IsQuasiSplitQF (d.QWfix x))
    (hV : IsQuasiSplitQF (d.QVfix x)) :
    ∃ O ∈ NilReg (grpCentralizer d.G ((d.diag x : d.G) : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag x : d.G) : d.ambientˣ) : d.ambient)),
      ∃ X ∈ nilOrbitSet O, OrbitSpec d x (X : d.ambient) := by
  have hν : (d.ν : F) ≠ 0 := d.ν.ne_zero
  have hdisj := fixedSub_inf_movedSub_of_isSS x hx
  have hcW := isCompl_fixedSub_orthogonal d.nondeg x hdisj
  have hcV := isCompl_fixedSub_orthogonal d.nondeg_QV (d.incl x)
    (fixedSub_inf_movedSub_incl d x hdisj)
  have hnd : IsNondeg (d.QW.comp (fixedSub x).subtype) := isNondeg_comp_subtype_of_isCompl hcW
  have hqx := d.isQuasiSplit_restrictFix hnd hW hV
  have hV' : IsQuasiSplitQF (d.QV.comp (fixedSub (d.incl x)).subtype) :=
    QuadClassify.isQuasiSplitQF_of_isometryEquiv (d.QVfixIso x) hV
  obtain ⟨XW, hXWm, hXWn, hXWb⟩ := exists_side_regNil d.nondeg x hcW hW
  obtain ⟨XV, hXVm, hXVn, hXVb⟩ := exists_side_regNil d.nondeg_QV (d.incl x) hcV hV'
  by_cases hVc : Even (finrank F ↥((fixedSub x).prod (⊤ : Submodule F d.Z))) ∧
      4 ≤ finrank F ↥((fixedSub x).prod (⊤ : Submodule F d.Z))
  · -- `O_ν` on `V'_x`
    obtain ⟨w, k, d₀, hw, hd₀, hd₀w, hdim⟩ := exists_orbitNu_family_V (d.restrictFix x hnd) hqx.1
      (by rw [finrank_restrictFix_V]; exact hVc.1)
    have hmem : ∀ v, d.fixIsoV hnd v ∈ fixedSub (d.incl x) := fun v => by
      rw [fixIsoV_apply, d.mem_fixedSub_incl_iff]; exact d.fixIsoW_mem x _
    let wA : ℤ → ↥(fixedSub (d.incl x)) := fun j => ⟨d.fixIsoV hnd (w j), hmem _⟩
    have hwA : IsSplitFamily (d.QV.comp (fixedSub (d.incl x)).subtype) wA (d.ν : F) k :=
      fun i j hi hj => by
        rw [bform_comp_subtype]; exact (hw.map_isometry (d.fixIsoV hnd)) i j hi hj
    have hUe := prod_top_eq_fixedSub_incl d x
    have hdimA : finrank F ↥(fixedSub (d.incl x)) ≤ 2 * k + 2 := by
      rw [← hUe, ← finrank_restrictFix_V d hnd, hdim]
    have hsb := side_regNil_bound (K := F) (V := d.V) (Q := d.QV) d.nondeg_QV (d.incl x) hcV
      (w := wA) (ν := (d.ν : F)) (k := k) hν hwA hdimA
    have hns := exists_nilReg_of_sides d x hx hmoved (XW := XW)
      (XV := regNil d.QV (fun j => (wA j : d.V)) (d.ν : F) k) hXWm hXWn hXWb hsb.1 hsb.2.1 hsb.2.2
    obtain ⟨O, hO, X, hX, hXe⟩ := hns
    refine ⟨O, hO, X, hX, ?_⟩
    unfold OrbitSpec
    rw [ite_eq_left_of_eq_true _ _ (eq_true hVc), hXe]
    refine isInOrbitNu_regNil_of_le (hw.map_isometry (d.fixIsoV hnd)) hν (d₀ := d.fixIsoV hnd d₀)
      (by rw [(d.fixIsoV hnd).map_app]; exact hd₀)
      (fun j hj => (bform_isometry _ _ _).trans (hd₀w j hj)) (hUe ▸ hmem d₀)
      (fun j _ => hUe ▸ hmem (w j)) (by rw [← finrank_restrictFix_V d hnd, hdim])
  by_cases hWc : Even (finrank F ↥(fixedSub x)) ∧ 4 ≤ finrank F ↥(fixedSub x)
  · -- `O_{−ν}` on `W'_x`
    have hfam := exists_orbitNu_family_W (d.restrictFix x hnd) hqx
      (show Even (d.fixDim x) from hWc.1) (show 4 ≤ d.fixDim x from hWc.2)
    obtain ⟨w, k, d₀, hw, hd₀, hd₀w, hdim⟩ := hfam
    let wA : ℤ → ↥(fixedSub x) := fun j => ⟨d.fixIsoW x (w j), d.fixIsoW_mem x _⟩
    have hwA : IsSplitFamily (d.QW.comp (fixedSub x).subtype) wA (-(d.ν : F)) k :=
      fun i j hi hj => by
        rw [bform_comp_subtype]; exact (hw.map_isometry (d.fixIsoW x)) i j hi hj
    have hdimA : finrank F ↥(fixedSub x) ≤ 2 * k + 2 := by
      rw [← finrank_restrictFix_W d hnd, hdim]
    have hsb := side_regNil_bound (K := F) (V := Fin d.m → F) (Q := d.QW) d.nondeg x hcW
      (w := wA) (ν := -(d.ν : F)) (k := k) (neg_ne_zero.2 hν) hwA hdimA
    have hns := exists_nilReg_of_sides d x hx hmoved
      (XW := regNil d.QW (fun j => (wA j : Fin d.m → F)) (-(d.ν : F)) k) (XV := XV)
      hsb.1 hsb.2.1 hsb.2.2 hXVm hXVn hXVb
    obtain ⟨O, hO, X, hX, hXe⟩ := hns
    refine ⟨O, hO, X, hX, ?_⟩
    unfold OrbitSpec
    rw [ite_eq_right_of_eq_false _ _ (eq_false hVc), ite_eq_left_of_eq_true _ _ (eq_true hWc), hXe]
    exact isInOrbitNu_regNil_of_le (hw.map_isometry (d.fixIsoW x)) (neg_ne_zero.2 hν)
      (d₀ := d.fixIsoW x d₀) (by rw [(d.fixIsoW x).map_app]; exact hd₀)
      (fun j hj => (bform_isometry _ _ _).trans (hd₀w j hj)) (d.fixIsoW_mem x _)
      (fun j _ => d.fixIsoW_mem x _) (by rw [← finrank_restrictFix_W d hnd, hdim])
  · have hne := nilReg_centralizer_nonempty_of_quasiSplit d x hx hmoved hW hV
    obtain ⟨O, hO⟩ := hne
    refine ⟨O, hO, ?_⟩
    refine ⟨⟨(Quotient.out O).1, (Quotient.out O).2.1⟩, ⟨(Quotient.out O).2.2, Quotient.out_eq O⟩, ?_⟩
    unfold OrbitSpec
    rw [ite_eq_right_of_eq_false _ _ (eq_false hVc), ite_eq_right_of_eq_false _ _ (eq_false hWc)]
    trivial

end GGPData

end GSpinGGP
