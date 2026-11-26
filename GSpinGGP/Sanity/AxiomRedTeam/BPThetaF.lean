/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.BPGeomExpansion
import GSpinGGP.TraceFormula.Scusp
import GSpinGGP.Sanity.AxiomRedTeam.WeylIntegration
import GSpinGGP.Sanity.AxiomRedTeam.HarishChandra
import GSpinGGP.Sanity.ThetaFBPAudit
import GSpinGGP.Sanity.GL2SpecialK
import GSpinGGP.Sanity.GL2IsMx
import GSpinGGP.Sanity.LieAudit
import GSpinGGP.Sanity.AxiomRedTeam.Measure

/-!
# Checks of `waldspurger2010_lemme_5_3`, `waldspurger2010_cor_5_9` and `bp_thm_5_5_1_iv`

All three axioms take the hypothesis `IsBPThetaF f θ` (`θ = θ_f` on `G_reg(F)` for every special
presentation, and some special presentation exists).

**The toy datum `toyD`** (`W = 0`, `V` a line, `G ≅ F^× × F^×`).
* Every isotropic flag has length `0` (`toyD_flag_len_eq_zero_W/V`), so every reduced Levi datum
  has `M = G`, and `IsMx L x` holds for all `L`, `x`.
* **A special `K` exists for every `L`** (`toyD_specialK`, `toyD_specialK_isSpecial`): the
  stabilizer
  of the special lattices `0 ⊆ W` and `𝒪_F z₀ ⊆ V` (`c = 0`, `q(z₀) = 1`).  Built here without
  `exists_specialK` (a `sorry`).
* `θ_f = c f` with `c = Measure.haar(A_G(𝒪)) > 0` for **every** presentation `(L, K)`
  (`toyD_thetaFBP_eq`).
* **Non-vacuity, both ways.**  `IsBPThetaF f θ ↔ θ = c f` (`toyD_isBPThetaF_iff`): the hypothesis
  is satisfiable (`toyD_isBPThetaF`), and it excludes every other `θ`, e.g. `c f + 1`
  (`toyD_not_isBPThetaF_add_one`).  On any datum, a too-strict or too-loose `IsSpecial` makes the
  hypothesis unsatisfiable (`not_isBPThetaF_of_not_exists`, `not_isBPThetaF_of_ne`,
  `TraceFormula/BPThetaF.lean`), so the axioms become vacuous, not false.
* **V**: the conclusions of all three axioms at `toyD`, proved without them:
  `toyD_lemme_5_3_check` (every continuous `f`),
  `toyD_cor_5_9_check` (test functions), `toyD_bp_thm_5_5_1_iv_check` (the whole statement, with
  the Haar family `haarFamily`, a genuine integral and finite sum).
* **C (joint model)**: at `toyD`, the conclusions of the three new axioms and of
  `bp_integrable_kernel_scusp` hold together for the same `f`, `f'`, `θ`, `J^A`
  (`toyD_joint_check`); `J^A` is computed independently from `measGmodAG` (`toyD_jA`), and agrees
  with the right side of (iv) only because `measGmodAG = dg/d_c a` (`toyD_jA_geom`).
* **`f = 0`** (`thetaFBP_zero`, `jA_zero_left`, `isBPThetaF_zero_eq`): on any datum,
  `θ_0 = 0`, `J^A(0, f') = 0`, and `IsBPThetaF 0 θ` forces `θ = 0` on `G_reg(F)`; so (iv) at
  `f = 0` says `0 = 0` (`bp_thm_5_5_1_iv_zero`), no junk value fires.

**The guard of `IsSpecial` on a nonabelian datum** (`Sanity/GL2SpecialK.lean`, `gl2Data`):
`IsSpecial`
is satisfiable (`gl2GoodK_isSpecial`); a `GoodK` that is not special exists
(`not_isSpecial_gl2GoodK'`); the Iwahori-normalizer lattice satisfies every condition of a special
lattice except `attained` (`gl2_iwahori_data`) and is excluded
(`not_exists_specialLattice_R_eq_iwahori`); the edge lattice is excluded
(`not_exists_specialLattice_R_eq_edge`).  Conjunct 1 of `waldspurger2010_lemme_5_3` is a bare `∀`
over special presentations, and these are the checks that `IsSpecial` is not too loose.

**Conflicts.**
* `bp_integrable_kernel_scusp` (BP 5.5.1(ii)) is about the same kernel and the same `A_G(F)\G(F)`;
  it is integrability of `x ↦ K^A(x, x)` for `Measure.haar` on `G(F)/A_G(F)`, which is equivalent
  to integrability for `measGmodAG` (a positive multiple, `integrable_kernelA_diag_scusp`).  No
  measure appears in both with different normalizations; joint model above.
* `luo_lie_geomExpansion_SO`, `germLie_unique_SO`, `waldspurger2010_thm_7_9` are statements on the
  Lie algebra of `SO(W) × SO(V)` (a `LuoDatum`), with all measures as parameters; none mentions
  `thetaFBP`, `IsBPThetaF`, `jA`, `measGmodAG` or `GoodK`.  The convention `dg/d_c a` reaches the
  Lie side only through the theorem-level transport `muG` (`TraceFormula/LuoTransfer.lean`), not
  through an axiom, so the new axioms and these share no object.
* `weyl_integration_exists`: different statement on the same `gammaIntegral`; the toy instances of
  both hold for the same family `haarFamily` (`toyD_weyl_integration_exists_check`,
  `toyD_bp_thm_5_5_1_iv_check`).
* `hc_character_isQuasiCharacter_admissible`, `germ_unique`: same `IsQuasiCharacter`/`jHat`; Cor 5.9
  presupposes that `ĵ(O, ·)` exists, which `germ_unique` already forces
  (`germ_unique_forces_jHat_ne_zero`).

**Automation probe** (run in a scratch file at `toyD` and at a general datum with all three axioms
in context, not kept: a failing search does not compile): `exact?` and `aesop` find no proof of
`False`.

**Presentation change** (any datum): `L` and `L.opp` (opposite flags, negated weights, same `M`)
have the same `A_M(F)` (`opp_AMF`, via `wtScalar_neg`) and the same `IsMx` (`IsMx.opp`).  The same
`K` is good and special for `L.opp` (`goodKOpp`, `isSpecial_goodKOpp`), so both presentations are
quantified over by `IsBPThetaF`.  For them: `dim a_M^G` (`opp_finrank_aMG`, via `opp_aG`),
`A_{G_x}(F)^1` (`opp_AGxOne`), `d_c t` (`opp_dcMeasure`) agree, and the lattice
`proj_M^G(H_M(A_M(F)))` of `L.opp` is the image of that of `L` under `−1` (`opp_latticeMG`; on
`A_M(F)` the `GL`-coordinates of `H_M` change sign, `opp_HM_add_mem_aG`).  Hence
`θ_f(L.opp, K) = θ_f(L, K)` as soon as `v_M(L.opp, K) = v_M(L, K)` (`opp_thetaFBP_of_vM`).

**A proper Levi subgroup** (`Sanity/GL2IsMx.lean`, `gl2Data`, `G = GL₁ × GSpin₃`, nonabelian): for
`x = inr (gl2Torus c)`, `c ≠ 1`, `x` is regular (`gl2_torus_mem_regularSet`), the torus datum is
`M(x)` (`gl2_isMx`; `G_x(F) ⊆ M(F) = A_M(F)`), and with `gl2GoodK_isSpecial` this witnesses the
`∃` half of `IsBPThetaF` with `M ≠ G` (`gl2_isBPThetaF_exists_half`).  The datum with `M = G`
is not `M(x)` (`gl2TopLevi_not_isMx`: `A_G(F)\G_x(F)` is not compact), so the `∀` half at `x`
consults exactly the presentations of the torus, among them `(gl2Levi, gl2GoodK)` and
`(gl2Levi.opp, gl2GoodK)` (`gl2_isBPThetaF_at_torus`).

**Owed (not reachable cheaply now).**
* `v_M(L.opp, K) = v_M(L, K)`, hence `thetaFBP L.opp K f x = thetaFBP L K f x` for every `f`
  (`opp_thetaFBP_of_vM`).  Missing: the duality `det(m|_{V_{−w}}) = det(m|_{V_w})⁻¹` for every
  `m ∈ M(F)` (proved here only on `A_M(F)`), which gives `H_P^{L.opp} = −H_P^{L}` modulo `a_G`;
  then `Measure.hullVolume_map` and `opp_latticeMG`.  Until then, if the two presentations
  disagreed for some `f`, `IsBPThetaF f θ` would be unsatisfiable at `gl2Data`
  (`gl2_isBPThetaF_at_torus`), making the axioms vacuous there, not false.

**Non-vacuity off `toyD`.**  On a general datum, non-vacuity of the hypothesis `IsBPThetaF` rests on
the `sorry`s `exists_isMx` and `exists_specialK`; if either failed, the axioms would be vacuous
there, not false.  `vM` is free of junk values only if `𝒫(M)` is finite, which is the `sorry`
`FlagLeviDatum.finite_parabolics` (at `toyD`, `M = G` and `v_M = 1`).

Not covered (accepted gap): the conclusions of the axioms off `toyD` (at `gl2Data` only the
hypothesis `IsBPThetaF` is tested), weighted orbital integrals with `v_M ≠ 1`, several tori,
nonzero nilpotent orbits.  No check here uses `exists_isMx` or `exists_specialK`.
-/

open MeasureTheory Module GSpinGGP GSpinGGP.Sanity GSpinGGP.GGPData

noncomputable section

namespace GSpinGGP.AxiomRedTeam

set_option linter.style.numericProjections false

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-! ## Any datum: `f = 0` -/

section Zero

variable {d : GGPData F}

/-- `θ_0 = 0` for every presentation. -/
theorem thetaFBP_zero (L : d.ReducedLeviDatum) (K : d.GoodK L.toFlagLeviDatum) (x : ↥d.G) :
    L.thetaFBP K 0 x = 0 := by
  rw [ReducedLeviDatum.thetaFBP_eq_integral]
  simp [weightedIntegrand]

/-- `J^A(0, f') = 0`. -/
theorem jA_zero_left (f' : ↥d.G → ℂ) : d.jA 0 f' = 0 := by
  simp [jA, kernelA]

/-- `IsBPThetaF 0 θ` forces `θ = 0` on `G_reg(F)`. -/
theorem isBPThetaF_zero_eq {θ : ↥d.G → ℂ} (hθ : d.IsBPThetaF 0 θ) {x : ↥d.G}
    (hx : x ∈ regularSet d.G d.lie) : θ x = 0 := by
  obtain ⟨L, K, hL, hK⟩ := (hθ x hx).1
  rw [(hθ x hx).2 L K hL hK, thetaFBP_zero]

/-- **(iv) at `f = 0` is `0 = 0`**: no junk value is needed to make it true. -/
theorem bp_thm_5_5_1_iv_zero (μ : ∀ T : Subgroup ↥d.G, Measure ↥T) {θ : ↥d.G → ℂ}
    (hθ : d.IsBPThetaF 0 θ) (f' : ↥d.G → ℂ) :
    d.jA 0 f' = 0 ∧ d.gammaIntegral μ (d.thetaWeylIntegrand μ θ f') = 0 := by
  refine ⟨jA_zero_left f', ?_⟩
  rw [thetaWeylIntegrand_congr μ (θ' := 0) (fun x hx => isBPThetaF_zero_eq hθ hx) f']
  simp [gammaIntegral, thetaWeylIntegrand]

end Zero

/-! ## Any datum: `IsMx` does not depend on the presentation `L` versus `L.opp`

`L.opp` has the opposite flags, the same bases and the negated weights, and the same Levi subgroup
(`FlagLeviDatum.opp_M`).  The identification (I5) of `Literature/BPThetaF.lean` asserts that
`thetaFBP` reads `L` only through `M`; here the part of it about `IsMx` and `A_M(F)` is checked. -/

section Opp

variable {d : GGPData F}

omit [PAdicField F] in
/-- The scalars on the weight spaces do not see the sign of the weights. -/
theorem wtScalar_neg {V : Type*} [AddCommGroup V] [Module F V] [Invertible (2 : F)]
    {Q : QuadraticForm F V} {ι : Type*} (b : Basis ι F V) (wt : ι → ℤ) :
    wtScalar Q b (-wt) = wtScalar Q b wt := by
  ext g
  constructor
  · rintro ⟨t, ht0, ht⟩
    exact ⟨fun w => t (-w), by simpa using ht0, fun j => by simpa using ht j⟩
  · rintro ⟨t, ht0, ht⟩
    exact ⟨fun w => t (-w), by simpa using ht0, fun j => by simpa using ht j⟩

/-- **`A_M(F)` is the same for `L` and `L.opp`.** -/
theorem opp_AMF (L : d.ReducedLeviDatum) : L.opp.AMF = L.AMF := by
  ext g
  rw [ReducedLeviDatum.mem_AMF_iff, ReducedLeviDatum.mem_AMF_iff]
  change d.fst g ∈ wtScalar d.QW L.bW (-L.wtW) ∧ d.snd g ∈ wtScalar d.QV L.bV (-L.wtV) ↔ _
  rw [wtScalar_neg, wtScalar_neg]

/-- **`IsMx` is the same for `L` and `L.opp`**: same `M`, same `A_M(F)`. -/
theorem IsMx.opp {L : d.ReducedLeviDatum} {x : ↥d.G} (h : L.IsMx x) : L.opp.IsMx x where
  regular := h.regular
  mem := by
    change x ∈ L.toFlagLeviDatum.opp.M
    rw [FlagLeviDatum.opp_M]; exact h.mem
  compact := by
    have e : L.opp.AGx x = L.AGx x := by
      simp only [ReducedLeviDatum.AGx, opp_AMF]
    rw [e]; exact h.compact

/-! ### The rest of `θ_f` under `L ↦ L.opp`

The same subgroup `K` is good and special for `L.opp` (`goodKOpp`, `isSpecial_goodKOpp`); the
sign `(−1)^{dim a_M^G}` (`opp_finrank_aMG`), `A_M(F)^1` (`opp_AGxOne`), `d_c t` (`opp_dcMeasure`)
and the lattice `proj_M^G(H_M(A_M(F)))` (`opp_latticeMG`: carried by `−1` under the
identification `oppAMGEquiv`) agree.  So `θ_f` agrees as soon as `v_M` does
(`opp_thetaFBP_of_vM`). -/

omit [PAdicField F] in
/-- The weight-`w` space of `−wt` is the weight-`(−w)` space of `wt`. -/
theorem wtSpan_neg_wt {V ι : Type*} [AddCommGroup V] [Module F V] (b : Basis ι F V) (wt : ι → ℤ)
    (w : ℤ) : wtSpan b (-wt) w = wtSpan b wt (-w) := by
  simp only [wtSpan, Pi.neg_apply, neg_eq_iff_eq_neg]

omit [PAdicField F] in
/-- Lying in some weight space does not see the sign of the weights. -/
theorem exists_mem_wtSpan_neg {V ι : Type*} [AddCommGroup V] [Module F V] {b : Basis ι F V}
    {wt : ι → ℤ} {v : V} (h : ∃ w, v ∈ wtSpan b wt w) : ∃ w, v ∈ wtSpan b (-wt) w := by
  obtain ⟨w, hw⟩ := h
  exact ⟨-w, by rwa [wtSpan_neg_wt, neg_neg]⟩

/-- Good position does not see the sign of the weights. -/
theorem stabilizesSplitLattice_neg {V ι : Type*} [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {b : Basis ι F V} {wt : ι → ℤ} {S : Set (GSpin Q)}
    (h : StabilizesSplitLattice Q b wt S) : StabilizesSplitLattice Q b (-wt) S := by
  obtain ⟨κ, hκ, e, he, hS⟩ := h
  exact ⟨κ, hκ, e, fun i => exists_mem_wtSpan_neg (he i), hS⟩

/-- **A good `K` for `L` is good for `L.opp`**: the same subgroup (`𝒫(M)` and the weight spaces
up to sign are the same). -/
def goodKOpp {L : d.FlagLeviDatum} (K : d.GoodK L) : d.GoodK L.opp where
  K := K.K
  isOpen := K.isOpen
  isCompact := K.isCompact
  mul_eq P hP := K.mul_eq P (L.opp_M ▸ hP)
  goodPositionW := stabilizesSplitLattice_neg K.goodPositionW
  goodPositionV := stabilizesSplitLattice_neg K.goodPositionV

omit [PAdicField F] in
/-- Adaptedness of a special lattice does not see the sign of the weights. -/
theorem isAdapted_neg {V ι : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Q : QuadraticForm F V} {S : SpecialLattice Q} {b : Basis ι F V}
    {wt : ι → ℤ} (h : S.IsAdapted b wt) : S.IsAdapted b (-wt) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i => exists_mem_wtSpan_neg (h1 i), fun i => exists_mem_wtSpan_neg (h2 i), ?_⟩
  rwa [wtSpan_neg]

/-- **`K` special for `L` is special for `L.opp`.** -/
theorem isSpecial_goodKOpp {L : d.FlagLeviDatum} {K : d.GoodK L} (h : K.IsSpecial) :
    (goodKOpp K).IsSpecial := by
  obtain ⟨SW, SV, hW, hV, hK⟩ := h
  exact ⟨SW, SV, isAdapted_neg hW, isAdapted_neg hV, hK⟩

/-- **`a_G` is the same for `L` and `L.opp`** (same `a_M`, the coordinates of the same characters up
to sign; `a_G` is spanned by the central coordinates, `mem_aG_iff`). -/
theorem opp_aG (L : d.ReducedLeviDatum) : L.opp.aG = L.aG := by
  ext H
  refine (L.opp.mem_aG_iff).trans (Iff.trans ?_ (L.mem_aG_iff (H := H)).symm)
  constructor <;> intro h c hc <;> rcases c with (i | u) | (i | u) <;> exact h _ hc


/-- `a_M^G` for `L` and `L.opp` (same `a_M`, same `a_G`). -/
def oppAMGEquiv (L : d.ReducedLeviDatum) : L.aMG ≃ₗ[ℝ] L.opp.aMG :=
  Submodule.quotEquivOfEq L.aG L.opp.aG (opp_aG L).symm

@[simp] theorem oppAMGEquiv_mkQ (L : d.ReducedLeviDatum) (H : L.aM) :
    oppAMGEquiv L (L.aG.mkQ H) = L.opp.aG.mkQ H := rfl

/-- **`dim a_M^G` is the same for `L` and `L.opp`**, so the sign `(−1)^{dim a_M^G}` of `θ_f` is. -/
theorem opp_finrank_aMG (L : d.ReducedLeviDatum) :
    finrank ℝ L.opp.aMG = finrank ℝ L.aMG :=
  (oppAMGEquiv L).finrank_eq.symm

/-- `A_{G_x}(F)` is the same for `L` and `L.opp` (`opp_AMF`). -/
theorem opp_AGx (L : d.ReducedLeviDatum) (x : ↥d.G) : L.opp.AGx x = L.AGx x := by
  simp only [ReducedLeviDatum.AGx, opp_AMF]

/-- **`A_M(F)^1` is the same for `L` and `L.opp`**: both are `A_M(F) ∩ latticeK` of the same bases
(`AGxOne_eq_preimage`). -/
theorem opp_AGxOne (L : d.ReducedLeviDatum) (x : ↥d.G) (a : ↥(d.centG x))
    (ha : a ∈ L.AGx x) (ha' : a ∈ L.opp.AGx x) :
    (⟨a, ha'⟩ : ↥(L.opp.AGx x)) ∈ L.opp.AGxOne x ↔ (⟨a, ha⟩ : ↥(L.AGx x)) ∈ L.AGxOne x := by
  rw [← SetLike.mem_coe, ← SetLike.mem_coe, ReducedLeviDatum.AGxOne_eq_preimage,
    ReducedLeviDatum.AGxOne_eq_preimage]
  rfl

/-- `IsDcMeasure` with `A_{G_x}(F)^1` written as `A_{G_x}(F) ∩ latticeK` (`AGxOne_eq_preimage`). -/
theorem isDcMeasure_iff_preimage (L : d.ReducedLeviDatum) (x : ↥d.G) (μ : Measure ↥(d.centG x)) :
    L.IsDcMeasure x μ ↔ μ.IsHaarMeasure ∧ ∃ (μA : Measure ↥(L.AGx x))
      (m : Measure (CosetSpace (L.AGx x).subtype)), μA.IsHaarMeasure ∧
        μA ((fun a : ↥(L.AGx x) => ((a : ↥(d.centG x)) : ↥d.G)) ⁻¹'
          d.latticeK L.bWFin L.bVFin) = 1 ∧
        IsWeilMeasure (L.AGx x).subtype μ μA m ∧ m Set.univ = 1 := by
  rw [ReducedLeviDatum.IsDcMeasure, ReducedLeviDatum.AGxOne_eq_preimage]

/-- **The normalization of `d_c t` is the same for `L` and `L.opp`.** -/
theorem opp_isDcMeasure (L : d.ReducedLeviDatum) (x : ↥d.G) :
    L.opp.IsDcMeasure x = L.IsDcMeasure x := by
  funext μ
  apply propext
  rw [isDcMeasure_iff_preimage, isDcMeasure_iff_preimage, opp_AGx]
  rfl

/-- **`d_c t` is the same for `L` and `L.opp`.** -/
theorem opp_dcMeasure (L : d.ReducedLeviDatum) (x : ↥d.G) :
    L.opp.dcMeasure x = L.dcMeasure x := by
  unfold ReducedLeviDatum.dcMeasure
  rw [opp_isDcMeasure]


omit [PAdicField F] in
/-- `∏_{wt j = w} f(wt j) = f(w)^{#{wt = w}}`. -/
theorem prod_ite_wt_eq {ι : Type*} [Fintype ι] (wt : ι → ℤ) (f : ℤ → F) (w : ℤ) :
    (∏ j, if wt j = w then f (wt j) else 1) = f w ^ Fintype.card {j // wt j = w} := by
  classical
  rw [← Finset.prod_filter, Finset.prod_congr rfl fun j hj => by
    rw [(Finset.mem_filter.1 hj).2], Finset.prod_const, Fintype.card_subtype]

omit [PAdicField F] in
/-- **On the split centre, the `GL`-coordinate of `H_M` changes sign under `wt ↦ −wt`**: an element
acting by `t(w)` on the weight-`w` space has `t(−w) = t(w)⁻¹` (`mul_neg_eq_one_of_orth`), and
opposite weight spaces have the same dimension (`card_wt_neg`). -/
theorem log_norm_prod_neg_add {V ι : Type*} [AddCommGroup V] [Module F V] [Fintype ι]
    [Invertible (2 : F)] {Q : QuadraticForm F V} (hQ : IsNondeg Q) {FL : IsotropicFlag Q}
    {b : Basis ι F V} {wt : ι → ℤ} (hs : IsFlagSplitting FL b wt) {g : GSpin Q} {t : ℤ → F}
    (ht : ∀ j, specP Q g (b j) = t (wt j) • b j) {w : ℤ} (h1 : 1 ≤ w) (h2 : w ≤ FL.len) :
    Real.log ‖∏ j, if (-wt) j = w then t (wt j) else 1‖ +
      Real.log ‖∏ j, if wt j = w then t (wt j) else 1‖ = 0 := by
  obtain ⟨j, hj⟩ := hs.exists_wt_eq h1 h2
  have hinv := mul_neg_eq_one_of_orth hQ hs.orth ht j
  rw [hj] at hinv
  have hneg : (∏ j, if (-wt) j = w then t (wt j) else 1) =
      t (-w) ^ Fintype.card {j // wt j = w} := by
    have := prod_ite_wt_eq (-wt) (fun v => t (-v)) w
    simp only [Pi.neg_apply, neg_neg] at this
    simp only [Pi.neg_apply]
    rw [this]
    congr 1
    rw [← hs.card_wt_neg hQ w]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun j => neg_eq_iff_eq_neg)
  rw [hneg, prod_ite_wt_eq, eq_inv_of_mul_eq_one_right hinv, inv_pow, norm_inv, Real.log_inv,
    neg_add_cancel]


/-- **On `A_M(F)`, `H_M` for `L.opp` is `−H_M` for `L` modulo `a_G`**: the `GL`-coordinates change
sign (`log_norm_prod_neg_add`), the `GSpin`-coordinates are the same and lie in `a_G`. -/
theorem opp_HM_add_mem_aG (L : d.ReducedLeviDatum) (m : ↥L.M) (m' : ↥L.opp.M)
    (hmm : (m' : ↥d.G) = m) (hm : (m : ↥d.G) ∈ L.AMF) :
    (show L.aM from L.opp.HM m') + L.HM m ∈ L.aG := by
  obtain ⟨⟨tW, -, htW⟩, ⟨tV, -, htV⟩⟩ := (L.mem_AMF_iff).1 hm
  have hW' : ∀ j, specP d.QW (d.fst m') (L.opp.bW j) = tW (L.wtW j) • L.opp.bW j := by
    rw [hmm]; exact htW
  have hV' : ∀ j, specP d.QV (d.snd m') (L.opp.bV j) = tV (L.wtV j) • L.opp.bV j := by
    rw [hmm]; exact htV
  rw [L.mem_aG_iff]
  rintro ((i | u) | (i | u)) hc
  · have h1 := L.opp.HM_inl_inl_of_diag m' hW' i
    have h2 := L.HM_inl_inl_of_diag m htW i
    change L.opp.HM m' (Sum.inl (Sum.inl i)) + L.HM m (Sum.inl (Sum.inl i)) = 0
    rw [h1, h2]
    exact log_norm_prod_neg_add d.nondeg L.hsW htW (by omega) (by have := i.2; omega)
  · exact absurd trivial hc
  · have h1 := L.opp.HM_inr_inl_of_diag m' hV' i
    have h2 := L.HM_inr_inl_of_diag m htV i
    change L.opp.HM m' (Sum.inr (Sum.inl i)) + L.HM m (Sum.inr (Sum.inl i)) = 0
    rw [h1, h2]
    exact log_norm_prod_neg_add d.nondeg_QV L.hsV htV (by omega) (by have := i.2; omega)
  · exact absurd trivial hc

/-- **`latticeMG` under `L ↦ L.opp`**: the lattice `proj_M^G(H_M(A_M(F)))` of `L.opp` is the
image of that of `L` under `−1`, transported by the identification of the two quotients
`a_M / a_G` (`oppAMGEquiv`). -/
theorem opp_latticeMG (L : d.ReducedLeviDatum) :
    L.opp.latticeMG = L.latticeMG.map (-(oppAMGEquiv L).toLinearMap).toAddMonoidHom := by
  have key : ∀ (m : ↥L.M) (m' : ↥L.opp.M), (m' : ↥d.G) = m → (m : ↥d.G) ∈ L.AMF →
      L.opp.aG.mkQ (L.opp.HM m') = -(oppAMGEquiv L (L.aG.mkQ (L.HM m))) := by
    intro m m' hmm hm
    rw [oppAMGEquiv_mkQ, eq_neg_iff_add_eq_zero]
    have h := opp_HM_add_mem_aG L m m' hmm hm
    rw [← opp_aG] at h
    exact (Submodule.Quotient.mk_eq_zero L.opp.aG).2 h
  rw [ReducedLeviDatum.latticeMG, ReducedLeviDatum.latticeMG, AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨⟨m', hm'⟩, rfl⟩
    have hmM : (m' : ↥d.G) ∈ L.M := L.toFlagLeviDatum.opp_M ▸ m'.2
    have hA : (m' : ↥d.G) ∈ L.AMF := opp_AMF L ▸ hm'
    exact ⟨_, ⟨⟨⟨m', hmM⟩, hA⟩, rfl⟩, (key ⟨m', hmM⟩ m' rfl hA).symm⟩
  · rintro ⟨_, ⟨⟨m, hm⟩, rfl⟩, rfl⟩
    have hmM : (m : ↥d.G) ∈ L.opp.M := L.toFlagLeviDatum.opp_M.symm ▸ m.2
    have hA : (m : ↥d.G) ∈ L.opp.AMF := (opp_AMF L).symm ▸ hm
    exact ⟨⟨⟨m, hmM⟩, hA⟩, key m ⟨m, hmM⟩ rfl hm⟩


/-- **What remains of the presentation change**: `θ_f` is the same for `(L, K)` and
`(L.opp, K)` as soon as `v_M` is; the sign (`opp_finrank_aMG`), `D^G(x)` and `d_c t`
(`opp_dcMeasure`) already agree. -/
theorem opp_thetaFBP_of_vM (L : d.ReducedLeviDatum) (K : d.GoodK L.toFlagLeviDatum)
    (hv : ∀ g, L.opp.vM (goodKOpp K) g = L.vM K g) (f : ↥d.G → ℂ) (x : ↥d.G) :
    L.opp.thetaFBP (goodKOpp K) f x = L.thetaFBP K f x := by
  simp only [ReducedLeviDatum.thetaFBP, weightedOrbitalIntegral, weightedIntegrand,
    opp_finrank_aMG, opp_dcMeasure, hv]

end Opp

/-! ## The toy datum -/

section Toy

local notation "𝕋" => (toyD (F := F))

local instance : Unique (Fin (𝕋).m → F) := inferInstanceAs (Unique (Fin 0 → F))

local instance : Subsingleton (Fin (2 * (𝕋).r + 1)) := inferInstanceAs (Subsingleton (Fin 1))

/-- Every isotropic subspace of `V` at `toyD` is `0` (the line `V` is anisotropic). -/
theorem toyD_isotropic_eq_bot_V (S : Submodule F (𝕋).V) (hS : IsTotallyIsotropic (𝕋).QV S) :
    S = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
  have h0 := hS v hv
  rw [show (𝕋).QV v = v.2 0 * v.2 0 from toyData_QV_apply v, mul_self_eq_zero] at h0
  refine Prod.ext (Subsingleton.elim _ _) (funext fun j => ?_)
  obtain ⟨j, hj⟩ := j
  have hj0 : j = 0 := by change j < 2 * 0 + 1 at hj; omega
  subst hj0
  exact h0

omit [PAdicField F] in
/-- A flag all of whose members are `0` has length `0`. -/
theorem len_eq_zero_of_forall_eq_bot {V : Type*} [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} (FL : IsotropicFlag Q) (h : ∀ i, FL.sub i = ⊥) : FL.len = 0 := by
  by_contra hne
  have hlt : FL.sub 0 < FL.sub ⟨1, by omega⟩ := FL.strictMono (Fin.mk_lt_mk.2 (by norm_num))
  rw [h, h] at hlt
  exact lt_irrefl _ hlt

theorem toyD_flag_len_eq_zero_W (FL : IsotropicFlag (𝕋).QW) : FL.len = 0 :=
  len_eq_zero_of_forall_eq_bot FL fun _ => Subsingleton.elim _ _

theorem toyD_flag_len_eq_zero_V (FL : IsotropicFlag (𝕋).QV) : FL.len = 0 :=
  len_eq_zero_of_forall_eq_bot FL fun i => toyD_isotropic_eq_bot_V _ (FL.isotropic i)

theorem toyD_M_eq_top (L : (𝕋).ReducedLeviDatum) : L.M = ⊤ :=
  L.M_eq_top_of_len_eq_zero (toyD_flag_len_eq_zero_W _) (toyD_flag_len_eq_zero_V _)

/-- **`θ_f = c f` at `toyD` for every presentation `(L, K)`**, `c = Measure.haar(A_G(𝒪)) > 0`
(the proof of `toyD_thetaFBP`, for an arbitrary `L` and `K`). -/
theorem toyD_thetaFBP_eq (L : (𝕋).ReducedLeviDatum) (K : (𝕋).GoodK L.toFlagLeviDatum)
    (f : ↥(𝕋).G → ℂ) (x : ↥(𝕋).G) :
    L.thetaFBP K f x = (Measure.haar : Measure ↥(𝕋).G).real toyOneSet * f x := by
  have hW := toyD_flag_len_eq_zero_W L.FW
  have hV := toyD_flag_len_eq_zero_V L.FV
  have hM := L.M_eq_top_of_len_eq_zero hW hV
  have hG := L.aG_eq_top_of_len_eq_zero hW hV
  have hdc : L.IsDcMeasure x (L.dcMeasure x) :=
    ReducedLeviDatum.isDcMeasure_dcMeasure (toyD_exists_isDcMeasure L hM x)
  have := hdc.1
  have := isMulRightInvariant_of_mem_regularSet
    (show x ∈ regularSet (𝕋).G (𝕋).lie by rw [toy_regularSet_eq_univ]; trivial) (L.dcMeasure x)
  have hpt : ∀ q : (𝕋).CentQuot x,
      f ((CosetSpace.out _ q)⁻¹ * x * CosetSpace.out _ q) = f x := fun q => by
    rw [mul_assoc, toyD_G_comm x, inv_mul_cancel_left]
  rw [ReducedLeviDatum.thetaFBP_of_aG_eq_top_eq_integral hG]
  simp_rw [hpt]
  rw [integral_const, toyD_orbQuotMeasure_dc L hW hV x hdc, Complex.real_smul]

/-! ### A special `K` at `toyD` -/

/-- The special lattice `0` of `W = 0`. -/
def toyD_specialW : SpecialLattice (𝕋).QW where
  n := 0
  v := Fin.elim0
  v' := Fin.elim0
  polar_v_v' i := i.elim0
  polar_v_v i := i.elim0
  polar_v'_v' i := i.elim0
  aniso x _ _ := Subsingleton.elim x 0
  r := 1
  exists_norm_eq := ⟨1, one_ne_zero, norm_one⟩
  attained h := (h (Submodule.eq_bot_of_subsingleton)).elim

/-- The vector `z₀` of the line `V`, `q(z₀) = 1`. -/
def toyZ0 : (𝕋).V := (0, fun _ => 1)

theorem toyD_QV_z0 : (𝕋).QV toyZ0 = 1 := by
  rw [show (𝕋).QV toyZ0 = toyZ0.2 0 * toyZ0.2 0 from toyData_QV_apply _]; simp [toyZ0]

theorem toyD_mem_hypOrth_V (x : (𝕋).V) :
    x ∈ hypOrth (𝕋).QV (Fin.elim0 : Fin 0 → (𝕋).V) Fin.elim0 :=
  mem_hypOrth.2 fun i => i.elim0

/-- The special lattice `𝒪_F z₀` of `V` (`n = 0`, `V_an = V`, `c = 0`). -/
def toyD_specialV : SpecialLattice (𝕋).QV where
  n := 0
  v := Fin.elim0
  v' := Fin.elim0
  polar_v_v' i := i.elim0
  polar_v_v i := i.elim0
  polar_v'_v' i := i.elim0
  aniso x _ hx := by
    rw [show (𝕋).QV x = x.2 0 * x.2 0 from toyData_QV_apply x, mul_self_eq_zero] at hx
    refine Prod.ext (Subsingleton.elim _ _) (funext fun j => ?_)
    obtain ⟨j, hj⟩ := j
    have hj0 : j = 0 := by change j < 2 * 0 + 1 at hj; omega
    subst hj0
    exact hx
  r := 1
  exists_norm_eq := ⟨1, one_ne_zero, norm_one⟩
  attained _ := ⟨toyZ0, toyD_mem_hypOrth_V _, by rw [toyD_QV_z0, norm_one]⟩

local instance : IsEmpty (Fin (toyD_specialV (F := F)).n) := inferInstanceAs (IsEmpty (Fin 0))

/-- The coordinate basis of `W = 0`. -/
def toyEW : Basis (Fin (𝕋).m) F (Fin (𝕋).m → F) := Pi.basisFun F (Fin (𝕋).m)

/-- The coordinate basis of `V`: the coordinate of `z₀`. -/
def toyEV : Basis (Fin (2 * (𝕋).r + 1)) F (𝕋).V :=
  (Pi.basisFun F (Fin (2 * (𝕋).r + 1))).map (LinearEquiv.uniqueProd).symm

theorem toyEV_repr (x : (𝕋).V) (i : Fin (2 * (𝕋).r + 1)) : toyEV.repr x i = x.2 i := by
  simp [toyEV]

theorem toyD_specialW_R : (toyD_specialW (F := F)).R = {x | ∀ i, ‖toyEW.repr x i‖ ≤ 1} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  refine ⟨fun _ i => i.elim0, fun _ => ?_⟩
  exact ⟨Fin.elim0, Fin.elim0, 0, fun i => i.elim0, fun i => i.elim0, zero_mem _,
    by simp [toyD_specialW], Subsingleton.elim _ _⟩

theorem toyD_specialV_R : (toyD_specialV (F := F)).R = {x | ∀ i, ‖toyEV.repr x i‖ ≤ 1} := by
  ext x
  simp only [Set.mem_ofPred_eq, toyEV_repr]
  have hx0 : ∀ i : Fin (2 * (𝕋).r + 1), i = 0 := fun i => Subsingleton.elim _ _
  constructor
  · rintro ⟨a, b, y, -, -, -, hQ, rfl⟩ i
    rw [hx0 i]
    change ‖(𝕋).QV y‖ ≤ 1 at hQ
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
    rw [show (𝕋).QV y = y.2 0 * y.2 0 from toyData_QV_apply y, norm_mul] at hQ
    nlinarith [norm_nonneg (y.2 0)]
  · intro hx
    refine ⟨Fin.elim0, Fin.elim0, x, fun i => i.elim0, fun i => i.elim0, toyD_mem_hypOrth_V x, ?_,
      by simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add]⟩
    change ‖(𝕋).QV x‖ ≤ 1
    rw [show (𝕋).QV x = x.2 0 * x.2 0 from toyData_QV_apply x, norm_mul]
    have := hx 0
    nlinarith [norm_nonneg (x.2 0)]

theorem toyD_not_isHypPlane_W : ¬ IsHypPlane (𝕋).QW := fun h => by
  have := h.1; simp only [finrank_fin_fun] at this; change 0 = 2 at this; omega

theorem toyD_not_isHypPlane_V : ¬ IsHypPlane (𝕋).QV := fun h => by
  have := h.1; simp [GGPData.V] at this; change 0 + (2 * 0 + 1) = 2 at this; omega

theorem toyD_specialStab_eq :
    (𝕋).specialStab toyD_specialW toyD_specialV = (𝕋).latticeK toyEW toyEV :=
  (𝕋).specialStab_eq_latticeK _ _ _ _ toyD_specialW_R toyD_specialV_R toyD_not_isHypPlane_W
    toyD_not_isHypPlane_V

/-- **A special `GoodK` for every reduced Levi datum of `toyD`**: the stabilizer of the special
lattices (`M = G`, so `G = P K` is trivial). -/
def toyD_specialK (L : (𝕋).ReducedLeviDatum) : (𝕋).GoodK L.toFlagLeviDatum :=
  GoodK.ofEqTop (toyD_M_eq_top L) ((𝕋).specialStab toyD_specialW toyD_specialV)
    ((𝕋).isOpen_specialStab toyEW toyEV _ _ toyD_specialW_R toyD_specialV_R)
    ((𝕋).isCompact_specialStab toyEW toyEV _ _ toyD_specialW_R toyD_specialV_R)
    (toyD_stabilizesSplitLattice _ _).1 (toyD_stabilizesSplitLattice _ _).2

theorem toyD_specialK_isSpecial (L : (𝕋).ReducedLeviDatum) : (toyD_specialK L).IsSpecial := by
  have hV := toyD_flag_len_eq_zero_V L.FV
  have htop : wtSpan L.bV L.wtV 0 = ⊤ := by
    rw [wtSpan, show {j | L.wtV j = 0} = Set.univ from
      Set.eq_univ_of_forall fun j => L.wtV_eq_zero hV j, Set.image_univ, L.bV.span_eq]
  refine ⟨toyD_specialW, toyD_specialV, ⟨fun i => i.elim0, fun i => i.elim0,
    fun x _ => Subsingleton.elim x 0 ▸ zero_mem _⟩, ⟨fun i => i.elim0, fun i => i.elim0,
    fun x _ => htop ▸ Submodule.mem_top⟩, rfl⟩

theorem toyD_isMx_all (L : (𝕋).ReducedLeviDatum) (x : ↥(𝕋).G) : L.IsMx x :=
  GGPData.toyD_isMx L (toyD_M_eq_top L) x

/-- `c = Measure.haar(A_G(𝒪))`. -/
abbrev toyC : ℂ := ((Measure.haar : Measure ↥(𝕋).G).real toyOneSet : ℂ)

local notation "𝕔" => (toyC (F := F))

/-- **`IsBPThetaF` is satisfiable at `toyD`**, by `θ = c f`, for every `f`. -/
theorem toyD_isBPThetaF (f : ↥(𝕋).G → ℂ) : (𝕋).IsBPThetaF f (fun x => 𝕔 * f x) := by
  obtain ⟨L, -⟩ := toyD_thetaFBP (F := F)
  exact fun x _ => ⟨⟨L, toyD_specialK L, toyD_isMx_all L x, toyD_specialK_isSpecial L⟩,
    fun L K _ _ => (toyD_thetaFBP_eq L K f x).symm⟩

/-- **`IsBPThetaF` pins `θ` down at `toyD`**: `IsBPThetaF f θ ↔ θ = c f`. -/
theorem toyD_isBPThetaF_iff (f θ : ↥(𝕋).G → ℂ) :
    (𝕋).IsBPThetaF f θ ↔ ∀ x, θ x = 𝕔 * f x := by
  refine ⟨fun h x => (h.eq (toyD_isBPThetaF f) (by rw [toy_regularSet_eq_univ]; trivial)), ?_⟩
  intro h
  exact (toyD_isBPThetaF f).congr fun x _ => h x

/-- An arbitrary `θ` does not satisfy the hypothesis. -/
theorem toyD_not_isBPThetaF_add_one (f : ↥(𝕋).G → ℂ) :
    ¬ (𝕋).IsBPThetaF f (fun x => 𝕔 * f x + 1) := fun h => by
  have := (toyD_isBPThetaF_iff f _).1 h 1
  simp at this

/-! ### The conclusions at `toyD`, without the axioms -/

/-- **`waldspurger2010_lemme_5_3` at `toyD`**, proved without it. -/
theorem toyD_lemme_5_3_check {f : ↥(𝕋).G → ℂ} (hf : Continuous f) :
    (∀ (x y : ↥(𝕋).G) (L L' : (𝕋).ReducedLeviDatum) (K : (𝕋).GoodK L.toFlagLeviDatum)
        (K' : (𝕋).GoodK L'.toFlagLeviDatum), L.IsMx x → L'.IsMx (y * x * y⁻¹) →
        K.IsSpecial → K'.IsSpecial → L'.thetaFBP K' f (y * x * y⁻¹) = L.thetaFBP K f x) ∧
    ∀ θ : ↥(𝕋).G → ℂ, (𝕋).IsBPThetaF f θ →
      LocallyIntegrable θ (Measure.haar : Measure ↥(𝕋).G) ∧
        ContinuousOn θ (regularSet (𝕋).G (𝕋).lie) := by
  refine ⟨fun x y L L' K K' _ _ _ _ => ?_, fun θ hθ => ?_⟩
  · rw [toyD_thetaFBP_eq, toyD_thetaFBP_eq, toyD_G_comm y x, mul_assoc, mul_inv_cancel, mul_one]
  · have hθ' : θ = fun x => 𝕔 * f x := funext ((toyD_isBPThetaF_iff f θ).1 hθ)
    subst hθ'
    have hc : Continuous fun x => 𝕔 * f x := continuous_const.mul hf
    exact ⟨hc.locallyIntegrable, hc.continuousOn⟩

/-- **`waldspurger2010_cor_5_9` at `toyD`**, proved without it: `c f` is a quasi-character
(`f` is locally constant and invariant, `G` being commutative). -/
theorem toyD_cor_5_9_check {f : ↥(𝕋).G → ℂ} (hf : f ∈ testFunctions ↥(𝕋).G) :
    ∀ θ : ↥(𝕋).G → ℂ, (𝕋).IsBPThetaF f θ → ∀ ψ : NontrivialAddChar F,
      IsQuasiCharacter (𝕋).G (𝕋).lie (𝕋).bilin ψ θ := by
  intro θ hθ ψ
  have hθ' : θ = fun x => 𝕔 * f x := funext ((toyD_isBPThetaF_iff f θ).1 hθ)
  subst hθ'
  have h1 := isQuasiCharacter_mul_of_isLocallyConstant (𝕋) ψ hf.1
    (fun x g => by rw [toyD_G_comm x g, mul_assoc, mul_inv_cancel, mul_one])
    (toyD_isQuasiCharacter_one ψ)
  have h2 := isQuasiCharacter_smul (𝕋) ψ 𝕔 h1
  convert h2 using 1
  funext x
  simp

/-- **`bp_thm_5_5_1_iv` at `toyD`**, the whole statement, proved without it (from
`toyD_jA_geom`, with the Haar family `haarFamily`). -/
theorem toyD_bp_thm_5_5_1_iv_check :
    ∃ μ : ∀ T : Subgroup ↥(𝕋).G, Measure ↥T, (∀ T : (𝕋).MaxTorus, (μ T.1).IsHaarMeasure) ∧
      ∀ f ∈ testFunctions ↥(𝕋).G, IsStronglyCuspidalInline (𝕋) f →
      ∀ θ : ↥(𝕋).G → ℂ, (𝕋).IsBPThetaF f θ →
      ∀ f' ∈ testFunctions ↥(𝕋).G,
        (∀ c : (𝕋).MaxTorusClass, Integrable
            (fun t : ↥(Quot.out c).1 => (𝕋).thetaWeylIntegrand μ θ f' (Quot.out c).1 t)
            (μ (Quot.out c).1)) ∧
        Summable (fun c : (𝕋).MaxTorusClass => ((weylCardG (𝕋) (Quot.out c).1 : ℝ))⁻¹ *
            ∫ t, ‖(𝕋).thetaWeylIntegrand μ θ f' (Quot.out c).1 t‖ ∂μ (Quot.out c).1) ∧
        (𝕋).jA f f' = (𝕋).gammaIntegral μ ((𝕋).thetaWeylIntegrand μ θ f') := by
  refine ⟨haarFamily _, isHaarMeasure_haarFamily _, fun f hf _ θ hθ f' hf' => ?_⟩
  have hθ' : θ = fun x => 𝕔 * f x := funext ((toyD_isBPThetaF_iff f θ).1 hθ)
  subst hθ'
  set μ := haarFamily (𝕋)
  have hμ := isHaarMeasure_haarFamily (𝕋)
  have hcf : Continuous fun x => 𝕔 * f x * f' x :=
    (continuous_const.mul hf.1.continuous).mul hf'.1.continuous
  have hcfc : HasCompactSupport fun x => 𝕔 * f x * f' x :=
    (hf.2.mul_left.mul_right)
  -- the integrand is `c f · weylIntegrand f'` = `weylIntegrand (c f f')`
  have hpt : ∀ T : (𝕋).MaxTorus, ∀ t, (𝕋).thetaWeylIntegrand μ (fun x => 𝕔 * f x) f' T.1 t =
      (𝕋).weylIntegrand μ (fun x => 𝕔 * f x * f' x) T.1 t := fun T t => by
    rw [thetaWeylIntegrand, toyD_weylIntegrand, toyD_weylIntegrand]
    ring
  have : Finite (𝕋).MaxTorusClass := Finite.of_subsingleton
  refine ⟨fun c => ?_, Summable.of_finite, ?_⟩
  · have := hμ (Quot.out c)
    simp_rw [hpt]
    exact toyD_integrable_weylIntegrand μ _ hcf hcfc
  · obtain ⟨L, K, -, h⟩ := toyD_jA_geom (F := F)
    rw [h μ hμ hf.1.continuous hf.2 hf']
    refine gammaIntegral_congr _ μ fun T t _ => ?_
    have hreg : t ∈ regularSet (𝕋).G (𝕋).lie := by rw [toy_regularSet_eq_univ]; trivial
    simp only [hreg, ↓reduceIte]
    rw [thetaWeylIntegrand_of_mem_regularSet μ _ f' T.1 hreg, toyD_thetaFBP_eq]

/-- **Joint model at `toyD`**: for `f, f' ∈ C_c^∞(G(F))` and `θ = c f`, the conclusions of the three
new axioms and of `bp_integrable_kernel_scusp` hold together, proved without any of them. -/
theorem toyD_joint_check {f f' : ↥(𝕋).G → ℂ} (hf : f ∈ testFunctions ↥(𝕋).G)
    (hf' : f' ∈ testFunctions ↥(𝕋).G) :
    (𝕋).IsBPThetaF f (fun x => 𝕔 * f x) ∧
      LocallyIntegrable (fun x => 𝕔 * f x) (Measure.haar : Measure ↥(𝕋).G) ∧
      (∀ ψ : NontrivialAddChar F,
        IsQuasiCharacter (𝕋).G (𝕋).lie (𝕋).bilin ψ (fun x => 𝕔 * f x)) ∧
      Integrable (fun x : ↥(𝕋).G ⧸ (𝕋).AG =>
        ∫ g, f ((Quotient.out x)⁻¹ * g * Quotient.out x) * f' g ∂Measure.haar) Measure.haar ∧
      ∃ μ : ∀ T : Subgroup ↥(𝕋).G, Measure ↥T, (∀ T : (𝕋).MaxTorus, (μ T.1).IsHaarMeasure) ∧
        (𝕋).jA f f' = (𝕋).gammaIntegral μ ((𝕋).thetaWeylIntegrand μ (fun x => 𝕔 * f x) f') := by
  have hθ := toyD_isBPThetaF f
  obtain ⟨μ, hμ, hiv⟩ := toyD_bp_thm_5_5_1_iv_check (F := F)
  have hcusp : IsStronglyCuspidalInline (𝕋) f := fun FW FV h =>
    (toyD_not_isProperFlagPair FW FV h).elim
  exact ⟨hθ, ((toyD_lemme_5_3_check hf.1.continuous).2 _ hθ).1,
    toyD_cor_5_9_check hf _ hθ, bp_conclusion_toyD f f', μ, hμ,
    (hiv f hf hcusp _ hθ f' hf').2.2⟩

end Toy

/-! ## A proper Levi subgroup: the torus of `GSpin₃ ≅ GL₂` (`Sanity/GL2IsMx.lean`) -/

section GL2

local notation "𝔾" => (gl2Data (F := F))

local notation "𝕃" => (gl2Levi (F := F))

/-- **The `∃` half of `IsBPThetaF` holds at a proper Levi subgroup** (for `x = inr (gl2Torus c)`,
`c ≠ 1`): `x` is regular, and `(gl2Levi, gl2GoodK)` is a special presentation of `M(x) ≠ G`. -/
theorem gl2_isBPThetaF_exists_half {c : Fˣ} (hc : (c : F) ≠ 1) :
    (𝔾).inr (gl2Torus c) ∈ regularSet (𝔾).G (𝔾).lie ∧
      ∃ (L : (𝔾).ReducedLeviDatum) (K : (𝔾).GoodK L.toFlagLeviDatum),
        L.IsMx ((𝔾).inr (gl2Torus c)) ∧ K.IsSpecial ∧ L.M ≠ ⊤ :=
  ⟨gl2_torus_mem_regularSet hc, gl2_exists_special_isMx hc⟩

/-- **What `IsBPThetaF` asks at a proper Levi subgroup**: at `x = inr (gl2Torus c)`, `c ≠ 1`, it
pins `θ x` to `θ_f` for both presentations `(gl2Levi, gl2GoodK)` and `(gl2Levi.opp, gl2GoodK)`
(`opp_thetaFBP_of_vM`: these agree once `v_M` does), and it does not consult the datum with
`M = G`, which is not `M(x)` (`gl2TopLevi_not_isMx`). -/
theorem gl2_isBPThetaF_at_torus {c : Fˣ} (hc : (c : F) ≠ 1) {f θ : ↥(𝔾).G → ℂ}
    (hθ : (𝔾).IsBPThetaF f θ) :
    θ ((𝔾).inr (gl2Torus c)) = (𝕃).thetaFBP gl2GoodK f ((𝔾).inr (gl2Torus c)) ∧
      θ ((𝔾).inr (gl2Torus c)) =
        (𝕃).opp.thetaFBP (goodKOpp gl2GoodK) f ((𝔾).inr (gl2Torus c)) ∧
      ¬ (gl2TopLevi (F := F)).IsMx ((𝔾).inr (gl2Torus c)) := by
  have h := (hθ _ (gl2_torus_mem_regularSet hc)).2
  exact ⟨h _ _ (gl2_isMx hc) gl2GoodK_isSpecial,
    h _ _ (IsMx.opp (gl2_isMx hc)) (isSpecial_goodKOpp gl2GoodK_isSpecial), gl2TopLevi_not_isMx c⟩

end GL2

end GSpinGGP.AxiomRedTeam
