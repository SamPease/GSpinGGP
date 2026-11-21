/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.LeviSubgroup

/-!
# Sanity checks for Levi subgroups, `𝒫(M)` and `H_M` (`GGP/LeviSubgroup.lean`)

1. **Inhabited for every flag pair** (`exists_isLevi`): every `P_{F_W} × P_{F_V}` has a Levi
   subgroup, and `𝒫(M)` contains `P` and the opposite parabolic `P̄`.
2. **No junk Levi** (`whittB_eq_whittU_of_isLevi_bot`, `IsLevi.eq_of_le`): `M = 1` is a Levi only
   when `P = U`, and two Levi subgroups of the same parabolic are never properly nested.
3. **`H_M` is not trivial** (`exists_HM_ne_zero`): for a nonempty flag of `V`, the lift `T` of the
   cocharacter `λ(τ)`, `0 < |τ| < 1`, lies in `M` and `H_M(T) ≠ 0` on the first `GL`-coordinate
   (`det(T|_{V_1}) = τ^{dim V_1}` with `dim V_1 ≥ 1`), so the `GL`-coordinates of `H_M` are not
   identically zero.
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

/-- `M = 1` is a Levi subgroup only when `P = U`. -/
theorem whittB_eq_whittU_of_isLevi_bot {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV}
    (h : d.IsLevi FW FV ⊥) : d.whittB FW FV = d.whittU FW FV := by
  refine le_antisymm (fun p hp => ?_) (d.whittU_le_whittB FW FV)
  obtain ⟨m, hm, u, hu, rfl⟩ := h.exists_mul hp
  rw [Subgroup.mem_bot] at hm
  rwa [hm, one_mul]

/-- **`H_M` is not trivial on a nonempty flag**: `H_M(T) ≠ 0` for the lift `T` of a contracting
cocharacter. -/
theorem exists_HM_ne_zero (L : d.FlagLeviDatum) (h : 0 < L.FV.len) :
    ∃ m : ↥L.M, L.HM m (Sum.inr (Sum.inl ⟨0, h⟩)) ≠ 0 := by
  classical
  obtain ⟨τ, hτ0, hτ1⟩ := NormedField.exists_norm_lt_one F
  have hτ : τ ≠ 0 := norm_pos_iff.1 hτ0
  obtain ⟨T, hT⟩ := L.hsV.exists_cochar_lift d.nondeg_QV hτ
  have hTM : T ∈ flagLevi (Q := d.QV) L.bV L.wtV := by
    rw [mem_flagLevi_iff]
    intro j i hi
    have hij : j ≠ i := fun e => hi (e ▸ rfl)
    simp [hT j, L.bV.repr_self, hij]
  refine ⟨⟨d.pair (1, T), ⟨(flagLevi (Q := d.QW) L.bW L.wtW).one_mem, hTM⟩⟩, ?_⟩
  have hspec : (specP d.QV T : d.V →ₗ[F] d.V) = cochar L.bV L.wtV τ :=
    L.bV.ext fun i => by rw [cochar_basis]; exact hT i
  have hdiag : LinearMap.toMatrix L.bV L.bV (wtBlock L.bV L.wtV 1 (cochar L.bV L.wtV τ)) =
      Matrix.diagonal fun j => if L.wtV j = 1 then τ else 1 := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
    simp only [wtBlock, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, cochar_basis, map_smul, wtProj_basis]
    rcases eq_or_ne i j with rfl | hij
    · by_cases hj : L.wtV i = 1 <;> simp [hj, L.bV.repr_self]
    · by_cases hj : L.wtV j = 1 <;> simp [hj, hij, L.bV.repr_self]
  have hval : ((L.char (Sum.inr (Sum.inl ⟨0, h⟩)) ⟨d.pair (1, T), ⟨(flagLevi (Q := d.QW) L.bW L.wtW).one_mem, hTM⟩⟩ : Fˣ) : F) =
      ∏ j, if L.wtV j = 1 then τ else 1 := by
    change ((wtDet (Q := d.QV) L.bV L.wtV ((0 : ℕ) + 1 : ℤ) ⟨T, hTM⟩ : Fˣ) : F) = _
    rw [wtDet_apply]
    simp only [Nat.cast_zero, zero_add]
    rw [hspec, ← LinearMap.det_toMatrix L.bV, hdiag, Matrix.det_diagonal]
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
  simp only [FlagLeviDatum.HM, hval]
  exact (Real.log_neg hpos hlt).ne

/-- The `GSpin(W)`-coordinate of `H_M` is the first coordinate of `hcMap` (the `H_G` of
`TraceFormula/SpinorNorm.lean`) when `W` is not a hyperbolic plane. -/
theorem HM_gspin_eq_hcMap (L : d.FlagLeviDatum) (hW : ¬ IsHypPlane d.QW) (m : ↥L.M) :
    L.HM m (Sum.inl (Sum.inr ())) = Multiplicative.toAdd (hcMap d.QW (d.fst m)).1 := by
  simp [FlagLeviDatum.HM, FlagLeviDatum.char, hcMap, gspinChar₁, hW, logAbs_apply]

end GGPData

end GSpinGGP
