/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.WeightVM
import GSpinGGP.Sanity.AxiomRedTeam.WaldspurgerXi
import GSpinGGP.Sanity.LeviAudit
import GSpinGGP.GGP.QuadClassify
import GSpinGGP.TraceFormula.WeakCartan

/-!
# Sanity checks for the weight `v_M`

At the toy datum `toyD` (`W = 0`, `V` a line, `G = GL₁ × GL₁`) the empty flags give a reduced
Levi datum with `M = G`; the compact open subgroup of `toyXiPair` is good for it
(`GoodK.ofEqTop`, with good position since `P(g) = 1` there), so `GoodK` is inhabited, and
`v_G = 1`.  At `Sanity.hypVData` (`V` a hyperbolic plane) a nonempty flag still has `a_M = a_G`
(`hypV_aG_eq_top`, from `single_mem_aG`), as it must: `G` is then a torus times `GL₁`, so
`M = G`.  At `gl2Data` (`W = 0`, `V` split of dimension `3`, `G = GL₁ × GSpin₃`) the torus `M`
of the flag `⟨z₁⟩` (the reduced Levi datum `gl2Levi`) has `a_M^G ≠ 0` and `latticeHaar` gives the fundamental domains of
`proj_M^G(H_M(A_M(F)))` volume `1` (`gl2_aMG_nontrivial`); a `GoodK` for this proper Levi is
constructed in `Sanity/GL2GoodK.lean` (`gl2GoodK`).  Nothing here uses an axiom.
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
  rw [hullVolume, latticeHaar_eq volume (isAddFundamentalDomain_Ioc hℓ 0), smul_apply,
    convexHull_pair, segment_eq_uIcc, Real.volume_Ioc, Real.volume_interval, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_inv, zero_add, sub_zero, sub_zero,
    ENNReal.toReal_ofReal hℓ.le, ENNReal.toReal_ofReal (abs_nonneg x), inv_mul_eq_div]

/-- **`P(g) = 1` at `toyD`**: every `g` is a pair of scalars (`toyD_exists_scalar`). -/
theorem toyD_specP_snd (g : ↥(𝕋).G) : specP (𝕋).QV ((𝕋).snd g) = 1 := by
  obtain ⟨c, hc⟩ := toyD_exists_scalar g
  have hc2 : ((((𝕋).snd g : GSpin (𝕋).QV) : (CliffordAlgebra (𝕋).QV)ˣ) :
      CliffordAlgebra (𝕋).QV) = algebraMap F _ c.2 := congrArg Prod.snd hc
  have hne : c.2 ≠ 0 := by
    rintro h
    rw [h, map_zero] at hc2
    exact (Units.ne_zero _) hc2
  have : (𝕋).snd g = scalarGSpin _ (Units.mk0 c.2 hne) := Subtype.ext (Units.ext hc2)
  rw [this, specP_scalarGSpin_eq_one]

/-- **Good position at `toyD`**: any `K` stabilizes the lattices spanned by splitting bases (on
`W = 0` there is nothing to check, and `P(g) = 1` on `V`). -/
theorem toyD_stabilizesSplitLattice (L : (𝕋).FlagLeviDatum) (S : Set ↥(𝕋).G) :
    StabilizesSplitLattice (𝕋).QW L.bW L.wtW ((𝕋).fst '' S) ∧
      StabilizesSplitLattice (𝕋).QV L.bV L.wtV ((𝕋).snd '' S) := by
  refine ⟨⟨L.ιW, inferInstance, L.bW, fun i => ⟨L.wtW i, Submodule.subset_span ⟨i, rfl, rfl⟩⟩,
    fun g _ v _ i => ?_⟩, ⟨L.ιV, inferInstance, L.bV,
    fun i => ⟨L.wtV i, Submodule.subset_span ⟨i, rfl, rfl⟩⟩, ?_⟩⟩
  · have : v = 0 := Subsingleton.elim _ _
    simp [this]
  · rintro _ ⟨g, -, rfl⟩ v hv i
    rw [toyD_specP_snd]
    exact hv i

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
    ∃ (L : (𝕋).ReducedLeviDatum) (K : (𝕋).GoodK L.toFlagLeviDatum), L.M = ⊤ ∧ L.aG = ⊤ ∧
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
  let K : (𝕋).GoodK L.toFlagLeviDatum := GoodK.ofEqTop hM toyXiPair.K toyXiPair.isOpen_K
    toyXiPair.isCompact_K (toyD_stabilizesSplitLattice _ _).1 (toyD_stabilizesSplitLattice _ _).2
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
      (∀ (K : (Sanity.hypVData (F := F)).GoodK L.toFlagLeviDatum) g, L.vM K g = 1) ∧
      (DiscreteTopology L.latticeMG.toIntSubmodule ∧
        Submodule.span ℝ (L.latticeMG.toIntSubmodule : Set L.aMG) = ⊤) := by
  obtain ⟨L, h, -, -, -, hW0, -, -⟩ := exists_HM_ne_zero_hypV (F := F)
  have hG : L.aG = ⊤ := L.aG_eq_top_of_single_mem fun x => L.single_mem_aG (by
    rcases x with (i | _) | (i | _)
    · exact absurd (i.isLt.trans_eq hW0) (Nat.not_lt_zero _)
    · trivial
    · exact Sanity.hypVData_isHypPlane_QV
    · trivial)
  exact ⟨L, h, hG, fun K g => L.vM_eq_one_of_aG_eq_top hG K g, L.latticeMG_isLattice⟩

/-- **The `GSpin₃ ≅ GL₂` datum**: `W = 0`, `V = Z` split of dimension `3` (`m = 0`, `r = 1`,
`ν = 1`), so `G = GL₁ × GSpin₃`. -/
abbrev gl2Data : GGPData F where
  m := 0
  QW := 0
  nondeg := ⟨fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
  r := 1
  ν := 1

theorem gl2Data_finrank_V : finrank F (gl2Data (F := F)).V = 3 := by
  show finrank F ((Fin 0 → F) × (Fin (2 * 1 + 1) → F)) = 3
  simp

/-- `V` is isotropic: `(0, e₀)` with `q(e₀) = ν Σᵢ e₀(i) e₀(2 − i) = 0`. -/
theorem gl2Data_one_le_wittIndex : 1 ≤ wittIndex (gl2Data (F := F)).QV := by
  refine QuadClassify.one_le_wittIndex_of_isotropic (v := ((0 : Fin 0 → F), (Pi.single 0 1 : Fin 3 → F)))
    (fun h => by simpa using congrArg (fun p : (gl2Data (F := F)).V => p.2 0) h) ?_
  show (0 : QuadraticForm F (Fin 0 → F)) 0 + splitOddForm 1 ((1 : Fˣ) : F) (Pi.single 0 1) = 0
  rw [LeviAux.splitOddForm_apply]
  simp [Fin.sum_univ_three, Fin.rev]

/-- The trivial splitting of the empty flag of `W = 0`. -/
theorem gl2_isFlagSplitting_W :
    IsFlagSplitting (emptyFlag (gl2Data (F := F)).QW) (Pi.basisFun F (Fin 0)) (Fin.elim0 : Fin 0 → ℤ) where
  mem i := i.elim0
  repr_eq_zero _ _ _ i := i.elim0
  orth i := i.elim0
  sum_wt := by simp

/-- **The reduced Levi datum of the torus**: the flag `⟨z₁⟩` of `V` with the standard basis and
weights `-1, 0, 1`, and the empty flag of `W = 0`. -/
def gl2Levi : (gl2Data (F := F)).ReducedLeviDatum where
  FW := emptyFlag _
  FV := (gl2Data (F := F)).flag
  ιW := Fin 0
  ιV := Fin (gl2Data (F := F)).m ⊕ Fin (2 * (gl2Data (F := F)).r + 1)
  bW := Pi.basisFun F (Fin 0)
  wtW := Fin.elim0
  bV := (gl2Data (F := F)).stdBasis
  wtV := (gl2Data (F := F)).stdWt
  hsW := gl2_isFlagSplitting_W
  hsV := (gl2Data (F := F)).isFlagSplitting_stdBasis
  reducedW := not_isHypPlane_comp_of_finrank_le _ _ (by rw [Module.finrank_fin_fun]; simp)
  reducedV := fun hp => by
    have h2 := hp.1
    have hsub : wtSpan (gl2Data (F := F)).stdBasis (gl2Data (F := F)).stdWt 0 ≤ Submodule.span F {(gl2Data (F := F)).stdBasis (Sum.inr 1)} := by
      rw [wtSpan, Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      rcases j with j | j
      · exact j.elim0
      · have : j = 1 := by
          have hj' : ((j : ℕ) : ℤ) - 1 = 0 := hj
          exact Fin.ext (by simp; omega)
        rw [this]; exact Submodule.mem_span_singleton_self _
    have h1 : finrank F (Submodule.span F {(gl2Data (F := F)).stdBasis (Sum.inr 1)}) ≤ 1 :=
      (finrank_span_le_card ({(gl2Data (F := F)).stdBasis (Sum.inr 1)} : Set (gl2Data (F := F)).V)).trans (by simp)
    have := (Submodule.finrank_mono hsub).trans h1
    omega

/-- **A Levi subgroup with `a_M^G ≠ 0` and a genuine normalization of `v_M`**: for the torus
`gl2Levi` of the flag `⟨z₁⟩` the `GL`-coordinate is not central (`V` is not a hyperbolic plane), so
`a_M^G ≠ 0`, and `latticeHaar` gives a fundamental domain of `proj_M^G(H_M(A_M(F)))` volume `1`.
(A `GoodK` for this Levi is `gl2GoodK` in `Sanity/GL2GoodK.lean`.) -/
theorem gl2_aMG_nontrivial :
    ¬ (gl2Levi (F := F)).IsCentralCoord (Sum.inr (Sum.inl ⟨0, Nat.zero_lt_one⟩)) ∧
      Nontrivial (gl2Levi (F := F)).aMG ∧
      ∃ D : Set (gl2Levi (F := F)).aMG,
        MeasureTheory.IsAddFundamentalDomain (gl2Levi (F := F)).latticeMG.toIntSubmodule D
          MeasureTheory.Measure.addHaar ∧
        MeasureTheory.Measure.latticeHaar (gl2Levi (F := F)).latticeMG D = 1 := by
  have hnotV : ¬ IsHypPlane (gl2Data (F := F)).QV := fun hp => by
    have := hp.1; rw [gl2Data_finrank_V] at this; omega
  exact ⟨hnotV, (gl2Levi (F := F)).nontrivial_aMG (c := Sum.inr (Sum.inl ⟨0, Nat.zero_lt_one⟩))
    hnotV, (gl2Levi (F := F)).exists_isAddFundamentalDomain_latticeHaar_eq_one⟩

end GSpinGGP.GGPData
