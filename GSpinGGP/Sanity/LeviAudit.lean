/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.LeviLattice
import GSpinGGP.Sanity.LieAudit

/-!
# Sanity checks for Levi subgroups, `𝒫(M)` and `H_M` (`GGP/LeviSubgroup.lean`)

1. **Inhabited for every flag pair** (`exists_isLevi`): every `P_{F_W} × P_{F_V}` has a Levi
   subgroup, and `𝒫(M)` contains `P` and the opposite parabolic `P̄`.
2. **No junk Levi** (`not_isLevi_bot`, `whittU_eq_bot_of_isLevi_whittB`, `IsLevi.eq_of_le`):
   `M = 1` is never a Levi (`M` contains the central scalars), `M = P` is a Levi only when
   `U = 1`, and two Levi subgroups of the same parabolic are never properly nested.
3. **`H_M` is not trivial** (`exists_HM_ne_zero`): for a nonempty flag of `V`, the lift `T` of the
   cocharacter `λ(τ)`, `0 < |τ| < 1`, lies in `M` and `H_M(T) ≠ 0` on the first `GL`-coordinate
   (`det(T|_{V_1}) = τ^{dim V_1}` with `dim V_1 ≥ 1`), so the `GL`-coordinates of `H_M` are not
   identically zero.
   This is instantiated (`exists_HM_ne_zero_hypV`) at `Sanity.hypVData` (`V` a hyperbolic plane,
   a full flag of length `1`, a reduced datum), where also the opposite flag differs from the
   flag (`IsFlagSplitting.oppFlag_top_inf_top`: the two tops are transversal).
4. **Agreement with `H_G`** (`HM_gspin_eq_hcMap`): the `GSpin`-coordinate of `H_M` is the first
   coordinate of the existing Harish-Chandra map `hcMap` when the space is not a hyperbolic
   plane.
-/

noncomputable section

open Module

namespace GSpinGGP

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {d : GGPData F}

/-- Every parabolic `P_{F_W} × P_{F_V}` has a Levi subgroup, and lies with its opposite in
`𝒫(M)`. -/
theorem exists_isLevi (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) :
    ∃ L : d.FlagLeviDatum, L.FW = FW ∧ L.FV = FV ∧ d.IsLevi FW FV L.M ∧
      d.whittB FW FV ∈ d.parabolics L.M ∧ L.opp.P ∈ d.parabolics L.M := by
  obtain ⟨ιW, _, _, bW, wtW, hsW⟩ := exists_flagSplitting d.nondeg FW
  obtain ⟨ιV, _, _, bV, wtV, hsV⟩ := exists_flagSplitting d.nondeg_QV FV
  let L : d.FlagLeviDatum := ⟨FW, FV, ιW, ιV, bW, wtW, bV, wtV, hsW, hsV⟩
  exact ⟨L, rfl, rfl, L.isLevi, L.mem_parabolics, L.opp_mem_parabolics⟩

/-- **`M = 1` is never a Levi subgroup**: a Levi contains the central scalars, and `pair (2, 1)`
is not in `U` (its `C(W)`-component `2` is not unipotent). -/
theorem not_isLevi_bot {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV} :
    ¬ d.IsLevi FW FV ⊥ := by
  intro h
  have hPU : d.whittB FW FV = d.whittU FW FV := by
    refine le_antisymm (fun p hp => ?_) (d.whittU_le_whittB FW FV)
    obtain ⟨m, hm, u, hu, rfl⟩ := h.exists_mul hp
    rw [Subgroup.mem_bot] at hm
    rwa [hm, one_mul]
  obtain ⟨L, rfl, rfl, hL, -⟩ := exists_isLevi FW FV
  set c : Fˣ := Units.mk0 2 two_ne_zero
  set g : ↥d.G := d.pair (scalarGSpin d.QW c, 1)
  have hg : g ∈ L.M := ⟨scalarGSpin_mem_flagLevi (Q := d.QW) L.bW L.wtW c,
    (flagLevi (Q := d.QV) L.bV L.wtV).one_mem⟩
  have hgU : g ∈ d.whittU L.FW L.FV := hPU ▸ hL.le hg
  have : g ∈ L.M ⊓ d.whittU L.FW L.FV := ⟨hg, hgU⟩
  rw [hL.inf_eq_bot, Subgroup.mem_bot] at this
  have h1 := congrArg
    (fun x => ((((d.fst x : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))) this
  simp only [g, fst_pair, map_one] at h1
  simp [scalarGSpin, c] at h1

/-- `M = P` is a Levi subgroup only when `U = 1`. -/
theorem whittU_eq_bot_of_isLevi_whittB {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV}
    (h : d.IsLevi FW FV (d.whittB FW FV)) : d.whittU FW FV = ⊥ := by
  have := h.inf_eq_bot
  rwa [inf_eq_right.2 (d.whittU_le_whittB FW FV)] at this

/-- **`H_M` is not trivial on a nonempty flag**: `H_M(T) ≠ 0` for the lift `T` of a contracting
cocharacter. -/
theorem exists_HM_ne_zero (L : d.ReducedLeviDatum) (h : 0 < L.FV.len) :
    ∃ m : ↥L.M, d.fst m = 1 ∧ L.HM m (Sum.inr (Sum.inl ⟨0, h⟩)) ≠ 0 := by
  classical
  obtain ⟨τ, hτ0, hτ1⟩ := NormedField.exists_norm_lt_one F
  have hτ : τ ≠ 0 := norm_pos_iff.1 hτ0
  obtain ⟨T, hT⟩ := L.hsV.exists_cochar_lift d.nondeg_QV hτ
  have hTM : T ∈ flagLevi (Q := d.QV) L.bV L.wtV := by
    rw [mem_flagLevi_iff]
    intro j i hi
    have hij : j ≠ i := fun e => hi (e ▸ rfl)
    simp [hT j, L.bV.repr_self, hij]
  refine ⟨⟨d.pair (1, T), ⟨(flagLevi (Q := d.QW) L.bW L.wtW).one_mem, hTM⟩⟩, rfl, ?_⟩
  set m : ↥L.M := ⟨d.pair (1, T), ⟨(flagLevi (Q := d.QW) L.bW L.wtW).one_mem, hTM⟩⟩
  have hval : L.HM m (Sum.inr (Sum.inl ⟨0, h⟩)) =
      Real.log ‖∏ j, if L.wtV j = 1 then τ else (1 : F)‖ := by
    rw [L.HM_inr_inl_of_diag m (s := fun j => τ ^ L.wtV j)
      (fun j => by simpa [m, snd_pair] using hT j)]
    congr 2
    exact Finset.prod_congr rfl fun j _ => by split_ifs with hj <;> simp_all
  obtain ⟨j₀, hj₀⟩ := L.hsV.exists_wt_eq (w := 1) le_rfl (by exact_mod_cast h)
  have hlt : ‖∏ j, if L.wtV j = 1 then τ else (1 : F)‖ < 1 := by
    rw [norm_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j₀)]
    simp only [hj₀, ite_true]
    have hle : ∏ j ∈ Finset.univ.erase j₀, ‖if L.wtV j = 1 then τ else (1 : F)‖ ≤ 1 := by
      refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
      split_ifs <;> simp [hτ1.le]
    calc _ ≤ 1 * ‖τ‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hτ1
  have hpos : 0 < ‖∏ j, if L.wtV j = 1 then τ else (1 : F)‖ :=
    norm_pos_iff.2 (Finset.prod_ne_zero_iff.2 fun j _ => by split_ifs <;> simp [hτ])
  rw [hval]
  exact (Real.log_neg hpos hlt).ne

/-- The `GSpin(W)`-coordinate of `H_M` is the first coordinate of `hcMap` (the `H_G` of
`TraceFormula/SpinorNorm.lean`) when `W` is not a hyperbolic plane. -/
theorem HM_gspin_eq_hcMap (L : d.ReducedLeviDatum) (hW : ¬ IsHypPlane d.QW) (m : ↥L.M) :
    L.HM m (Sum.inl (Sum.inr ())) = Multiplicative.toAdd (hcMap d.QW (d.fst m)).1 := by
  simp [ReducedLeviDatum.HM, ReducedLeviDatum.char, hcMap, gspinChar₁, hW, logAbs_apply]

/-- **A nonempty reduced flag datum exists**: at `Sanity.hypVData` (`V` a hyperbolic plane) a full
flag of `V` has length `1` (that of the line `W` has length `0`); the datum is reduced (`W` is a
line, and `V` has no weight-`0` basis vector), `H_M` is nonzero (at an `m` with trivial
`GSpin(W)`-component), and the opposite flag of `V` differs from the flag. -/
theorem exists_HM_ne_zero_hypV :
    ∃ (L : (Sanity.hypVData (F := F)).ReducedLeviDatum) (h : 0 < L.FV.len) (m : ↥L.M),
      L.HM m (Sum.inr (Sum.inl ⟨0, h⟩)) ≠ 0 ∧ L.opp.FV.top ≠ L.FV.top ∧ L.FW.len = 0 ∧
        L.FV.len = 1 ∧ (Sanity.hypVData (F := F)).fst m = 1 := by
  set D := Sanity.hypVData (F := F)
  obtain ⟨FW, hFW⟩ := IsotropicFlag.exists_isFull D.QW
  obtain ⟨FV, hFV⟩ := IsotropicFlag.exists_isFull D.QV
  obtain ⟨L, hLW, hL, -⟩ := exists_isLevi FW FV
  have hW0 : L.FW.len = 0 := by
    rw [hLW, hFW.1]
    refine Sanity.wittIndex_eq_zero_of_anisotropic fun (z : Fin (2 * 0 + 1) → F) hz =>
      funext fun i => ?_
    have hz' : -1 * (z 0 * z 0) = 0 := by
      rw [← Sanity.splitOddForm_zero_apply]; exact hz
    rw [Sanity.fin_eq_zero_of rfl i]
    exact (by simpa using hz' : z 0 = 0)
  have h : 0 < L.FV.len := by
    rw [hL, hFV.1, Sanity.hypVData_isHypPlane_QV.2.2]; exact one_pos
  have hdimV : finrank F D.V = 2 := Sanity.hypVData_isHypPlane_QV.1
  have hred : ¬ IsHypPlane (D.QW.comp (wtSpan L.bW L.wtW 0).subtype) := fun hp => by
    have h1 := Submodule.finrank_le (wtSpan L.bW L.wtW 0)
    have h2 : finrank F (Fin D.m → F) = 1 := Module.finrank_fin_fun F
    have := hp.1
    omega
  have hredV : ¬ IsHypPlane (D.QV.comp (wtSpan L.bV L.wtV 0).subtype) := fun hp => by
    classical
    obtain ⟨j₁, hj₁⟩ := L.hsV.exists_wt_eq (w := 1) le_rfl (by exact_mod_cast h)
    obtain ⟨j₂, hj₂⟩ := L.hsV.exists_wt_eq_neg D.nondeg_QV (w := 1) le_rfl (by exact_mod_cast h)
    have hempty : {j | L.wtV j = 0} = (∅ : Set L.ιV) := by
      ext j
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hj
      have hcard : Fintype.card L.ιV = 2 := by rw [← finrank_eq_card_basis L.bV, hdimV]
      have n1 : j ≠ j₁ := fun e => by rw [e] at hj; omega
      have n2 : j ≠ j₂ := fun e => by rw [e] at hj; omega
      have n12 : j₁ ≠ j₂ := fun e => by rw [e] at hj₁; omega
      have h3 : ({j, j₁, j₂} : Finset L.ιV).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [n1, n2]), Finset.card_pair n12]
      have := Finset.card_le_univ ({j, j₁, j₂} : Finset L.ιV)
      omega
    have := hp.1
    rw [wtSpan, hempty, Set.image_empty, Submodule.span_empty, finrank_bot] at this
    omega
  let R : D.ReducedLeviDatum := ⟨L, hred, hredV⟩
  obtain ⟨m, hm1, hm⟩ := exists_HM_ne_zero R h
  have hV1 : R.FV.len = 1 := by
    change L.FV.len = 1
    rw [hL, hFV.1, Sanity.hypVData_isHypPlane_QV.2.2]
  refine ⟨R, h, m, hm, fun he => ?_, hW0, hV1, hm1⟩
  have htop := R.hsV.oppFlag_top_inf_top D.nondeg_QV
  change R.opp.FV.top ⊓ R.FV.top = ⊥ at htop
  rw [he, inf_idem] at htop
  have hlt := R.FV.strictMono (show (0 : Fin (R.FV.len + 1)) < Fin.last _ from by
    simp [Fin.lt_def]; omega)
  rw [R.FV.sub_zero] at hlt
  exact hlt.ne' htop

end GGPData

end GSpinGGP
