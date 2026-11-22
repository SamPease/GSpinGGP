/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.WeightVM
import GSpinGGP.Sanity.AxiomRedTeam.WaldspurgerXi
import GSpinGGP.Sanity.LeviAudit

/-!
# Sanity checks for the weight `v_M`

At the toy datum `toyD` (`W = 0`, `V` a line, `G = GL₁ × GL₁`) the empty flags give a reduced
Levi datum with `M = G`; the compact open subgroup of `toyXiPair` is good for it
(`GoodK.ofEqTop`), so `GoodK` is inhabited, and `v_G = 1`.  The lattice statement
`latticeMG_isLattice` holds there (in the zero space `a_G^G`).  At `Sanity.hypVData` (`V` a
hyperbolic plane) a nonempty flag still has `a_M = a_G` (`hypV_aG_eq_top`), as it must: `G` is
then a torus times `GL₁`, so `M = G`.  Nothing here uses an axiom.
-/

noncomputable section

open Module GSpinGGP.Sanity GSpinGGP.AxiomRedTeam

namespace GSpinGGP.GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝕋" => (toyD (F := F))

open MeasureTheory Measure Set in
/-- **The lattice normalization in dimension one**: for `Λ = ℤ ℓ ⊂ ℝ` the hull of `{0, x}` has
volume `|x| / ℓ` (`E/Λ` has volume `1`, whatever `addHaar` is). -/
theorem hullVolume_zmultiples_pair {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) :
    hullVolume (AddSubgroup.zmultiples ℓ) {0, x} = |x| / ℓ := by
  set c := addHaarScalarFactor (addHaar : Measure ℝ) volume
  have hμ : (addHaar : Measure ℝ) = c • volume :=
    isAddLeftInvariant_eq_smul_of_innerRegular _ _
  have hc : (c : ENNReal) ≠ 0 := by
    intro h0
    have : (addHaar : Measure ℝ) = 0 := by rw [hμ, show c = 0 from by exact_mod_cast h0, zero_smul]
    exact (NeZero.ne _ : (addHaar : Measure ℝ) ≠ 0) this
  have hD := isAddFundamentalDomain_Ioc hℓ 0 (addHaar : Measure ℝ)
  have hcov : addCovolume (AddSubgroup.zmultiples ℓ) ℝ addHaar = c * ENNReal.ofReal ℓ := by
    rw [hD.covolume_eq_volume, hμ, smul_apply, Real.volume_Ioc, zero_add, sub_zero]; rfl
  have hhull : convexHull ℝ ({0, x} : Set ℝ) = uIcc 0 x := by
    rw [convexHull_pair, segment_eq_uIcc]
  rw [hullVolume, latticeHaar, smul_apply, hcov, hhull, hμ, smul_apply, Real.volume_interval,
    sub_zero]
  rw [ENNReal.smul_def, smul_eq_mul, smul_eq_mul,
    ENNReal.mul_inv (Or.inl hc) (Or.inl ENNReal.coe_ne_top)]
  rw [show (c : ENNReal)⁻¹ * (ENNReal.ofReal ℓ)⁻¹ * (c * ENNReal.ofReal |x|) =
      ((c : ENNReal)⁻¹ * c) * ((ENNReal.ofReal ℓ)⁻¹ * ENNReal.ofReal |x|) by ring,
    ENNReal.inv_mul_cancel hc ENNReal.coe_ne_top, one_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hℓ.le, ENNReal.toReal_ofReal (abs_nonneg x), inv_mul_eq_div]

/-- A submodule of a space of dimension `≤ 1` is not a hyperbolic plane. -/
theorem not_isHypPlane_comp_of_finrank_le {K V : Type*} [Field K] [Invertible (2 : K)]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (S : Submodule K V) (h : finrank K V ≤ 1) :
    ¬ IsHypPlane (Q.comp S.subtype) := fun hS => by
  have := Submodule.finrank_le S
  have h2 := hS.1
  omega

/-- **`M = G` at `toyD`**: a reduced datum with empty flags, a good compact subgroup, `a_M = a_G`,
`v_G = 1`, and the lattice statement. -/
theorem toyD_vM_eq_one :
    ∃ (L : (𝕋).ReducedLeviDatum) (K : (𝕋).GoodK L.M), L.M = ⊤ ∧ L.aG = ⊤ ∧
      (∀ g, L.vM K g = 1) ∧
      (DiscreteTopology L.latticeMG.toIntSubmodule ∧
        Submodule.span ℝ (L.latticeMG.toIntSubmodule : Set L.aMG) = ⊤) := by
  classical
  obtain ⟨ιW, _, _, bW, wtW, hsW⟩ := exists_flagSplitting (𝕋).nondeg (emptyFlag (𝕋).QW)
  obtain ⟨ιV, _, _, bV, wtV, hsV⟩ := exists_flagSplitting (𝕋).nondeg_QV (emptyFlag (𝕋).QV)
  have hW1 : finrank F (Fin (𝕋).m → F) ≤ 1 := by
    rw [Module.finrank_fin_fun]; simp [toyD]
  have hV1 : finrank F (𝕋).V ≤ 1 := by
    simp only [GGPData.V]
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]; simp [toyD]
  let L : (𝕋).ReducedLeviDatum :=
    { FW := emptyFlag _, FV := emptyFlag _, ιW := ιW, ιV := ιV, bW := bW, wtW := wtW, bV := bV,
      wtV := wtV, hsW := hsW, hsV := hsV
      reducedW := not_isHypPlane_comp_of_finrank_le _ _ hW1
      reducedV := not_isHypPlane_comp_of_finrank_le _ _ hV1 }
  have hM := L.M_eq_top_of_len_eq_zero rfl rfl
  have hG := L.aG_eq_top_of_len_eq_zero rfl rfl
  let K : (𝕋).GoodK L.M := GoodK.ofEqTop hM toyXiPair.K toyXiPair.isOpen_K toyXiPair.isCompact_K
  have : Subsingleton L.aMG := Submodule.Quotient.subsingleton_iff.2 hG
  refine ⟨L, K, hM, hG, L.vM_eq_one_of_len_eq_zero rfl rfl K, ?_, ?_⟩
  · infer_instance
  · exact Subsingleton.elim _ _

/-- **`a_G` in the hyperbolic case**: at `Sanity.hypVData` (`V` a hyperbolic plane, so `GSpin(V)`
is a split torus and `A_G` is all of `GSpin(W) × GSpin(V)`) the Levi `M` of a full flag has
`a_M = a_G`, although the flag is nonempty: `a_G` is spanned by `H_M(A_G(F))`, not by the
`GSpin`-coordinates alone.  So `v_M = 1` and the lattice statement holds there. -/
theorem hypV_aG_eq_top :
    ∃ L : (Sanity.hypVData (F := F)).ReducedLeviDatum, 0 < L.FV.len ∧ L.aG = ⊤ ∧
      (∀ (K : (Sanity.hypVData (F := F)).GoodK L.M) g, L.vM K g = 1) ∧
      (DiscreteTopology L.latticeMG.toIntSubmodule ∧
        Submodule.span ℝ (L.latticeMG.toIntSubmodule : Set L.aMG) = ⊤) := by
  classical
  set D := Sanity.hypVData (F := F)
  obtain ⟨L, h, m, hm, -, hW0, hV1, hm1⟩ := exists_HM_ne_zero_hypV (F := F)
  have hmAG : (m : ↥D.G) ∈ D.AG := by
    refine ⟨(D.fst m, D.snd m), ⟨?_, ?_⟩, D.pair_fst_snd _⟩
    · rw [hm1]; exact Subgroup.one_mem _
    · show D.snd m ∈ splitCentralGSpin D.QV
      rw [splitCentralGSpin, ite_eq_left_of_eq_true _ _ (eq_true Sanity.hypVData_isHypPlane_QV)]
      trivial
  have hv : L.HM m ∈ L.aG := Submodule.subset_span ⟨⟨m, hmAG⟩, rfl⟩
  set a := L.HM m (Sum.inr (Sum.inl ⟨0, h⟩))
  set b := L.HM m (Sum.inr (Sum.inr ()))
  have hdec : L.HM m = a • Pi.single (Sum.inr (Sum.inl ⟨0, h⟩)) 1 +
      b • Pi.single (Sum.inr (Sum.inr ())) 1 := by
    funext x
    rcases x with (i | _) | (i | _)
    · exact absurd (i.isLt.trans_eq hW0) (Nat.not_lt_zero _)
    · simp [ReducedLeviDatum.HM, ReducedLeviDatum.char, hm1]
    · have : i = ⟨0, h⟩ := Fin.ext (by have := i.isLt; omega)
      subst this
      simp [a]
    · simp [b]
  have hGL : Pi.single (Sum.inr (Sum.inl ⟨0, h⟩)) (1 : ℝ) ∈ L.aG := by
    have h1 := L.aG.smul_mem a⁻¹ (L.aG.sub_mem hv (L.aG.smul_mem b L.single_gspin_mem_aG.2))
    rwa [hdec, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hm, one_smul] at h1
  have hG : L.aG = ⊤ := L.aG_eq_top_of_single_mem fun x => by
    rcases x with (i | _) | (i | _)
    · exact absurd (i.isLt.trans_eq hW0) (Nat.not_lt_zero _)
    · exact L.single_gspin_mem_aG.1
    · have : i = ⟨0, h⟩ := Fin.ext (by have := i.isLt; omega)
      exact this ▸ hGL
    · exact L.single_gspin_mem_aG.2
  have : Subsingleton L.aMG := Submodule.Quotient.subsingleton_iff.2 hG
  exact ⟨L, h, hG, fun K g => L.vM_eq_one_of_aG_eq_top hG K g, inferInstance,
    Subsingleton.elim _ _⟩

end GSpinGGP.GGPData
