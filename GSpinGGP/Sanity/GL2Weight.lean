/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.GL2GoodK

/-!
# The weight `v_T` of the torus of `GSpin₃ ≅ GL₂`

At `gl2Data` (`W = 0`, `V` split of dimension `3`, `G = GL₁ × GSpin₃`) the torus `T = M` of the
flag `⟨z₁⟩` (`gl2Levi`) has the good compact subgroup `gl2GoodK` (`Sanity/GL2GoodK.lean`).  This
file computes the weight `v_T` of Arthur (Thesis §2.6; Beuzart-Plessis, Astérisque 418, §1.10)
at the lower unipotent elements, the first case with `a_M^G ≠ 0`.  Work in the basis
`z₋₁, z₀, ½ z₁` of `V` (`gl2Basis`), in which `q = ac + b²` and `K` is the stabilizer of the
standard lattice `Λ`.

* `gl2_parabolics`: `𝒫(T) = {B, B̄}`, the stabilizers of `⟨z₁⟩` and `⟨z₋₁⟩`.  The empty flag is
  excluded because `T ≠ G` (`gl2_len_ne_zero`); a `T`-stable isotropic line is an eigenline of
  `gl2Torus ϖ`, whose eigenvalues `ϖ, 1, ϖ⁻¹` are distinct.
* `gl2_hPar_B`, `gl2_hPar_Bbar`: in the coordinate of `a_M^G ≅ ℝ` (`gl2AMGEquiv`),
  `H_B(g) = −log ‖P(g)⁻¹ (½ z₁)‖_Λ` and `H_B̄(g) = log ‖P(g)⁻¹ z₋₁‖_Λ` (`‖·‖_Λ` the sup norm of the
  coordinates, normalized so that the basis vectors have norm `1`).
* `gl2Nbar t` (`n̄(t)`): the product of the reflections in `z₀` and `z₀ + t z₋₁`, which fixes
  `z₋₁` and lies in the unipotent radical of `B̄` (`gl2_nbar_mem_whittU`);
  `H_B(n̄(t)) = −2 log max(1, ‖t‖)` and `H_B̄(n̄(t)) = 0`.
* `gl2_latticeMG_map`: the lattice `proj_M^G(H_M(A_M(F)))` is `ℤ (−log ‖ϖ‖)`.
* `gl2_vM_nbar`: `v_T(n̄(t)) = 2 log max(1, ‖t‖) / (−log ‖ϖ‖) = 2 max(0, −val(t))`; in
  particular `v_T(n̄(ϖ^{−n})) = 2n` (`gl2_vM_nbar_zpow`) and `v_T(n̄(t)) = 0` iff `‖t‖ ≤ 1`
  (`gl2_vM_nbar_eq_zero_iff`).

Nothing here uses an axiom or `sorry`.
-/

noncomputable section

open Module GSpinGGP.Sanity

namespace GSpinGGP.GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝔾" => (gl2Data (F := F))

local notation "𝐟" => (gl2Basis (F := F))

/-! ## Coordinates of the form -/

theorem gl2_polar (x y : (𝔾).V) : QuadraticMap.polar (𝔾).QV x y =
    𝐟.repr x 0 * 𝐟.repr y 2 + 𝐟.repr y 0 * 𝐟.repr x 2 + 2 * (𝐟.repr x 1 * 𝐟.repr y 1) :=
  polar_eq_of_rank3 _ _ gl2_QV_eq x y

/-! ## Two explicit elements -/

theorem gl2_Q_one : (𝔾).QV (𝐟 1) ≠ 0 := by
  rw [gl2_QV_eq]; simp

theorem gl2_Q_nbar (t : F) : (𝔾).QV (𝐟 1 + t • 𝐟 0) ≠ 0 := by
  rw [gl2_QV_eq]; simp

/-- **The lower unipotent element `n̄(t)`**: the product of the reflections in `z₀` and
`z₀ + t z₋₁`.  It fixes `z₋₁` and `P(n̄(t))⁻¹ (½ z₁) = ½ z₁ − t z₀ − t² z₋₁` (in the basis
`z₋₁, z₀, ½ z₁`: `gl2_nbar_inv_two`). -/
def gl2Nbar (t : F) : ↥(𝔾).G := (𝔾).inr (gspinPair (𝔾).QV gl2_Q_one (gl2_Q_nbar t))

theorem gl2_nbar_inv_two (t : F) :
    specP (𝔾).QV ((𝔾).snd (gl2Nbar t))⁻¹ (𝐟 2) = 𝐟 2 - t • 𝐟 1 - t ^ 2 • 𝐟 0 := by
  rw [gl2Nbar, snd_inr, specP_gspinPair_inv_apply,
    quadReflection_apply_of_polar_eq_zero _ (u := 𝐟 1) (x := 𝐟 2)
      (by rw [gl2_polar]; simp),
    quadReflection_apply, gl2_polar]
  have hQ : (𝔾).QV (𝐟 1 + t • 𝐟 0) = 1 := by rw [gl2_QV_eq]; simp
  rw [hQ]
  simp [smul_add, smul_smul, pow_two]
  abel

theorem gl2_nbar_inv_zero (t : F) :
    specP (𝔾).QV ((𝔾).snd (gl2Nbar t))⁻¹ (𝐟 0) = 𝐟 0 := by
  rw [gl2Nbar, snd_inr, specP_gspinPair_inv_apply,
    quadReflection_apply_of_polar_eq_zero _ (u := 𝐟 1) (x := 𝐟 0)
      (by rw [gl2_polar]; simp),
    quadReflection_apply_of_polar_eq_zero _ (by rw [gl2_polar]; simp)]

theorem gl2_basisNorm_nbar (t : F) :
    basisNorm 𝐟 (𝐟 2 - t • 𝐟 1 - t ^ 2 • 𝐟 0) = max 1 ‖t‖ ^ 2 := by
  have hr : ∀ i, 𝐟.repr (𝐟 2 - t • 𝐟 1 - t ^ 2 • 𝐟 0) i = ![-t ^ 2, -t, 1] i := fun i => by
    fin_cases i <;> simp
  have hm : 0 ≤ max 1 ‖t‖ ^ 2 := by positivity
  refine le_antisymm ((basisNorm_le_iff hm).2 fun i => ?_) ?_
  · rw [hr]
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, norm_neg, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) 2
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, norm_neg]
      rcases le_total ‖t‖ 1 with h | h
      · exact h.trans (one_le_pow₀ (le_max_left _ _))
      · rw [max_eq_right h]; nlinarith
    · simp only [Fin.reduceFinMk, Matrix.cons_val, norm_one]
      exact one_le_pow₀ (le_max_left _ _)
  · have h0 := norm_repr_le_basisNorm (b := 𝐟) (𝐟 2 - t • 𝐟 1 - t ^ 2 • 𝐟 0) 0
    have h2 := norm_repr_le_basisNorm (b := 𝐟) (𝐟 2 - t • 𝐟 1 - t ^ 2 • 𝐟 0) 2
    rw [hr] at h0 h2
    simp only [Matrix.cons_val_zero, norm_neg, norm_pow] at h0
    simp only [Matrix.cons_val, norm_one] at h2
    rcases le_total ‖t‖ 1 with h | h
    · rw [max_eq_left h, one_pow]; exact h2
    · rw [max_eq_right h]; exact h0

theorem gl2_Q_torus_u : (𝔾).QV (𝐟 0 + 𝐟 2) ≠ 0 := by
  rw [gl2_QV_eq]; simp

theorem gl2_Q_torus_w (c : Fˣ) : (𝔾).QV (𝐟 0 + (c : F) • 𝐟 2) ≠ 0 := by
  rw [gl2_QV_eq]; simp

/-- **A torus element**: the product of the reflections in `z₋₁ + ½ z₁` and `z₋₁ + c ½ z₁`; it
acts by `c, 1, c⁻¹` on `z₋₁, z₀, z₁` (`gl2_torus_apply`). -/
def gl2Torus (c : Fˣ) : GSpin (𝔾).QV := gspinPair (𝔾).QV gl2_Q_torus_u (gl2_Q_torus_w c)

theorem gl2_torus_apply (c : Fˣ) (i : Fin 3) :
    specP (𝔾).QV (gl2Torus c) (𝐟 i) = (![(c : F), 1, (c : F)⁻¹] : Fin 3 → F) i • 𝐟 i := by
  have hc : (c : F) ≠ 0 := c.ne_zero
  have hu : (𝔾).QV (𝐟 0 + 𝐟 2) = 1 := by rw [gl2_QV_eq]; simp
  have hw : (𝔾).QV (𝐟 0 + (c : F) • 𝐟 2) = c := by rw [gl2_QV_eq]; simp
  change (specP (𝔾).QV (gl2Torus c) : (𝔾).V →ₗ[F] (𝔾).V) (𝐟 i) = _
  rw [gl2Torus, specP_gspinPair, mul_apply_eq_comp, quadReflection_apply,
    quadReflection_apply, hu, hw, gl2_polar, gl2_polar]
  fin_cases i <;> simp [smul_add, smul_smul, hc]

/-! ## Elements of the torus `M` are diagonal -/

theorem gl2_stdWt_injective : Function.Injective (𝔾).stdWt := by
  rintro (i | i) (j | j) h
  · exact i.elim0
  · exact i.elim0
  · exact j.elim0
  · simp only [stdWt, Sum.elim_inr] at h
    exact congrArg Sum.inr (Fin.ext (by omega))

/-- The eigenvalue of `P(y)` on `stdBasis (inr i)`, for `y` in the Levi subgroup. -/
def gl2Eig (y : GSpin (𝔾).QV) (i : Fin 3) : F :=
  (𝔾).stdBasis.repr (specP (𝔾).QV y ((𝔾).stdBasis (Sum.inr i))) (Sum.inr i)

theorem gl2_levi_apply {y : GSpin (𝔾).QV} (hy : y ∈ flagLevi (Q := (𝔾).QV) (𝔾).stdBasis (𝔾).stdWt)
    (i : Fin 3) : specP (𝔾).QV y (𝐟 i) = gl2Eig y i • 𝐟 i := by
  rw [gl2Basis_eq, map_smul, flagLevi_apply_basis_eq_smul gl2_stdWt_injective hy, smul_comm]
  rfl

local notation "𝕃" => (gl2Levi (F := F))

/-- The noncentral coordinate of `a_M`: the `GL₁`-factor of `M` acting on `⟨z₁⟩`. -/
abbrev gl2c₀ : (𝕃).Coord := Sum.inr (Sum.inl ⟨0, Nat.zero_lt_one⟩)

/-- **The character of the coordinate `gl2c₀`** is the eigenvalue on `z₁`. -/
theorem gl2_char_eq (m : ↥(𝕃).M) :
    (((𝕃).char gl2c₀ m : Fˣ) : F) = gl2Eig ((𝔾).snd m) 2 := by
  classical
  change LinearMap.det (wtBlock (𝔾).stdBasis (𝔾).stdWt ((0 : ℤ) + 1)
    (specP (𝔾).QV ((𝔾).snd m) : (𝔾).V →ₗ[F] (𝔾).V)) = _
  rw [det_wtBlock_of_diag (b := (𝔾).stdBasis) (wt := (𝔾).stdWt) (s := fun j => (𝔾).stdBasis.repr
    (specP (𝔾).QV ((𝔾).snd m) ((𝔾).stdBasis j)) j)
    (fun j => flagLevi_apply_basis_eq_smul (b := (𝔾).stdBasis) gl2_stdWt_injective
      m.property.2 j)]
  simp [Fintype.prod_sum_type, Fin.prod_univ_three, stdWt, gl2Eig]

/-- The eigenvalues on `z₋₁` and `z₁` are inverse (`P(y)` preserves `polar(z₋₁, z₁) ≠ 0`). -/
theorem gl2Eig_zero_mul_two {y : GSpin (𝔾).QV}
    (hy : y ∈ flagLevi (Q := (𝔾).QV) (𝔾).stdBasis (𝔾).stdWt) :
    gl2Eig y 0 * gl2Eig y 2 = 1 := by
  have h : QuadraticMap.polar (𝔾).QV (specP (𝔾).QV y (𝐟 0)) (specP (𝔾).QV y (𝐟 2)) =
      QuadraticMap.polar (𝔾).QV (𝐟 0) (𝐟 2) := by
    simp only [QuadraticMap.polar, ← map_add, specP_isometry]
  rw [gl2_levi_apply hy, gl2_levi_apply hy, gl2_polar, gl2_polar] at h
  simpa using h

/-! ## `H_P` through lattice norms -/

/-- **`H_P` from a lattice norm**: if `P = P_{F_W} × P_{F_V} ∈ 𝒫(M)` fixes the line of a unit
vector `v` of `Λ`, its unipotent radical fixes `v`, and `M` acts on `v` by the `e`-th power of
the eigenvalue on `z₁`, then `e · H_P(g) = −log ‖P(g)⁻¹ v‖_Λ` in the coordinate `gl2c₀`
(write `g = m u k`; `k` preserves `‖·‖_Λ`). -/
theorem gl2_hP_apply {FW : IsotropicFlag (𝔾).QW} {FV : IsotropicFlag (𝔾).QV}
    (hL : (𝔾).IsLevi FW FV (𝕃).M)
    (hPK : ∀ g : ↥(𝔾).G, ∃ p ∈ (𝔾).whittB FW FV, ∃ k ∈ gl2K (F := F), g = p * k)
    {v : (𝔾).V} (hv : basisNorm 𝐟 v = 1)
    (hU : ∀ u ∈ (𝔾).whittU FW FV, specP (𝔾).QV ((𝔾).snd u) v = v) (e : ℤ)
    (hM : ∀ m : ↥(𝕃).M, specP (𝔾).QV ((𝔾).snd m) v = gl2Eig ((𝔾).snd m) 2 ^ e • v)
    (g : ↥(𝔾).G) :
    e * (𝕃).hP hL gl2K ((𝔾).isOpen_latticeK _ _) ((𝔾).isCompact_latticeK _ _) hPK g gl2c₀ =
      -Real.log (basisNorm 𝐟 (specP (𝔾).QV ((𝔾).snd g)⁻¹ v)) := by
  obtain ⟨p, hp, k, hk, rfl⟩ := hPK g
  rw [(𝕃).hP_eq hL _ _ hPK ⟨p, hp⟩ hk]
  set m := hL.proj ⟨p, hp⟩
  have hu := hL.inv_proj_mul_mem ⟨p, hp⟩
  set χ := gl2Eig ((𝔾).snd m) 2
  have hχ : χ ≠ 0 := by
    rw [show χ = _ from (gl2_char_eq m).symm]; exact Units.ne_zero _
  have hpv : specP (𝔾).QV ((𝔾).snd p) v = χ ^ e • v := by
    have : p = (m : ↥(𝔾).G) * ((m : ↥(𝔾).G)⁻¹ * p) := by group
    rw [this, map_mul, specP_mul_apply, hU _ hu, hM]
  have hpv' : specP (𝔾).QV ((𝔾).snd p)⁻¹ v = (χ ^ e)⁻¹ • v := by
    apply (specP (𝔾).QV ((𝔾).snd p)).injective
    rw [specP_inv_apply_apply, map_smul, hpv, smul_smul, inv_mul_cancel₀ (zpow_ne_zero e hχ),
      one_smul]
  have hk' : ((𝔾).snd k)⁻¹ ∈ latticeSpin (𝔾).QV 𝐟 := inv_mem hk.2
  rw [map_mul, mul_inv_rev, specP_mul_apply, hpv', map_smul, basisNorm_smul,
    basisNorm_specP_of_mem_latticeSpin hk', hv, mul_one, norm_inv, norm_zpow, Real.log_inv,
    Real.log_zpow, neg_neg]
  simp only [ReducedLeviDatum.HM]
  rw [gl2_char_eq]

/-! ## `H_B` and `H_B̄` -/

/-- The parabolic `B`, the stabilizer of `⟨z₁⟩`. -/
abbrev gl2B : ↥((𝔾).parabolics (𝕃).M) :=
  ⟨(𝕃).toFlagLeviDatum.P, (𝕃).toFlagLeviDatum.mem_parabolics⟩

/-- The opposite parabolic `B̄`, the stabilizer of `⟨z₋₁⟩`. -/
abbrev gl2Bbar : ↥((𝔾).parabolics (𝕃).M) :=
  ⟨(𝕃).toFlagLeviDatum.opp.P, (𝕃).toFlagLeviDatum.opp_mem_parabolics⟩

theorem gl2_two_mem_flag : 𝐟 2 ∈ (𝕃).FV.sub 1 := by
  rw [gl2Basis_eq]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨0, Nat.zero_lt_one⟩, ?_⟩)
  rw [stdBasis_inr]; rfl

theorem gl2_zero_mem_oppFlag : 𝐟 0 ∈ (𝕃).toFlagLeviDatum.opp.FV.sub 1 := by
  rw [gl2Basis_eq]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr 0, ?_, rfl⟩)
  change ((gl2Data (F := F)).flag.len : ℤ) + 1 - 1 ≤ -(((0 : Fin 3) : ℕ) - (1 : ℤ))
  simp [flag]

/-- **`H_B(g) = −log ‖P(g)⁻¹ (½ z₁)‖_Λ`** in the coordinate `gl2c₀`. -/
theorem gl2_hPar_B (g : ↥(𝔾).G) : (𝕃).hPar gl2GoodK gl2B g gl2c₀ =
    -Real.log (basisNorm 𝐟 (specP (𝔾).QV ((𝔾).snd g)⁻¹ (𝐟 2))) := by
  rw [(𝕃).hPar_eq gl2GoodK gl2B rfl (𝕃).isLevi]
  have h := gl2_hP_apply (𝕃).isLevi (gl2_iwasawa _ _) (v := 𝐟 2) (basisNorm_basis 2)
    (fun u hu => by
      have := hu.2.2.1 ⟨0, Nat.zero_lt_one⟩ (𝐟 2) gl2_two_mem_flag
      change _ ∈ (𝕃).FV.sub 0 at this
      rw [(𝕃).FV.sub_zero, Submodule.mem_bot,
        sub_eq_zero] at this
      exact this)
    1 (fun m => by rw [zpow_one]; exact gl2_levi_apply m.property.2 2) g
  rw [Int.cast_one, one_mul] at h
  exact h

/-- **`H_B̄(g) = log ‖P(g)⁻¹ z₋₁‖_Λ`** in the coordinate `gl2c₀`. -/
theorem gl2_hPar_Bbar (g : ↥(𝔾).G) : (𝕃).hPar gl2GoodK gl2Bbar g gl2c₀ =
    Real.log (basisNorm 𝐟 (specP (𝔾).QV ((𝔾).snd g)⁻¹ (𝐟 0))) := by
  have hL : (𝔾).IsLevi (𝕃).toFlagLeviDatum.opp.FW (𝕃).toFlagLeviDatum.opp.FV (𝕃).M :=
    (𝕃).toFlagLeviDatum.opp_M ▸ (𝕃).toFlagLeviDatum.opp.isLevi
  rw [(𝕃).hPar_eq gl2GoodK gl2Bbar rfl hL]
  have h := gl2_hP_apply hL (gl2_iwasawa _ _) (v := 𝐟 0) (basisNorm_basis 0)
    (fun u hu => by
      have := hu.2.2.1 ⟨0, Nat.zero_lt_one⟩ (𝐟 0) gl2_zero_mem_oppFlag
      change _ ∈ (𝕃).toFlagLeviDatum.opp.FV.sub 0 at this
      rw [(𝕃).toFlagLeviDatum.opp.FV.sub_zero, Submodule.mem_bot, sub_eq_zero] at this
      exact this)
    (-1) (fun m => by
      rw [zpow_neg_one, gl2_levi_apply m.property.2 0,
        eq_inv_of_mul_eq_one_left (gl2Eig_zero_mul_two m.property.2)]) g
  rw [Int.cast_neg, Int.cast_one, neg_one_mul, neg_inj] at h
  exact h

/-- **`H_B(n̄(t)) = −2 log max(1, ‖t‖)`** in the coordinate `gl2c₀`. -/
theorem gl2_hPar_B_nbar (t : F) :
    (𝕃).hPar gl2GoodK gl2B (gl2Nbar t) gl2c₀ = -(2 * Real.log (max 1 ‖t‖)) := by
  rw [gl2_hPar_B, gl2_nbar_inv_two, gl2_basisNorm_nbar, Real.log_pow, Nat.cast_ofNat]

/-- **`H_B̄(n̄(t)) = 0`**: `n̄(t)` fixes `z₋₁`. -/
theorem gl2_hPar_Bbar_nbar (t : F) : (𝕃).hPar gl2GoodK gl2Bbar (gl2Nbar t) gl2c₀ = 0 := by
  rw [gl2_hPar_Bbar, gl2_nbar_inv_zero, basisNorm_basis, Real.log_one]

/-! ## `𝒫(M) = {B, B̄}` -/

/-- For a flag of length one, `P(g)` stabilizes it iff it stabilizes its line. -/
theorem gl2_mem_flagStab_iff {FV : IsotropicFlag (𝔾).QV} (h : FV.len = 1) {y : GSpin (𝔾).QV} :
    y ∈ flagStab FV ↔ ∀ v ∈ FV.top, specP (𝔾).QV y v ∈ FV.top := by
  revert h
  rcases FV with ⟨len, sub, sub_zero, -, -⟩
  rintro (rfl : len = 1)
  rw [mem_flagStab_iff]
  refine ⟨fun hy => hy (Fin.last 1), fun hy i => ?_⟩
  fin_cases i
  · intro v hv
    change v ∈ sub 0 at hv
    rw [sub_zero, Submodule.mem_bot] at hv
    rw [hv, map_zero]; exact zero_mem _
  · exact hy

/-- The line of a flag of length one is spanned by any of its nonzero vectors. -/
theorem gl2_top_eq_span {FV : IsotropicFlag (𝔾).QV} {w : (𝔾).V} (hw : w ≠ 0)
    (hmem : w ∈ FV.top) : FV.top = Submodule.span F {w} := by
  refine (Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).2 hmem)
    ?_).symm
  rw [finrank_span_singleton hw]
  exact gl2_finrank_le_one (FV.isotropic _)

theorem gl2Basis_ne_zero (i : Fin 3) : 𝐟 i ≠ 0 := (gl2Basis (F := F)).ne_zero i

/-- Flags of length one with the same line have the same stabilizer. -/
theorem gl2_flagStab_eq {FV FV' : IsotropicFlag (𝔾).QV} (h : FV.len = 1) (h' : FV'.len = 1)
    (ht : FV.top = FV'.top) : flagStab FV = flagStab FV' := by
  ext y; rw [gl2_mem_flagStab_iff h, gl2_mem_flagStab_iff h', ht]

theorem gl2_whittB_eq {FW FW' : IsotropicFlag (𝔾).QW} {FV FV' : IsotropicFlag (𝔾).QV}
    (h : flagStab FV = flagStab FV') : (𝔾).whittB FW FV = (𝔾).whittB FW' FV' := by
  simp only [whittB, gl2_flagStab_W FW, gl2_flagStab_W FW', h]

theorem gl2_torus_apply_std (c : Fˣ) (j : Fin 3) :
    specP (𝔾).QV (gl2Torus c) ((𝔾).stdBasis (Sum.inr j)) =
      (![(c : F), 1, (c : F)⁻¹] : Fin 3 → F) j • (𝔾).stdBasis (Sum.inr j) := by
  have h := gl2_torus_apply c j
  rw [gl2Basis_eq, map_smul] at h
  have hk : (![1, 1, 2⁻¹] : Fin 3 → F) j ≠ 0 := by fin_cases j <;> simp
  have := congrArg (fun x => ((![1, 1, 2⁻¹] : Fin 3 → F) j)⁻¹ • x) h
  simp only [smul_smul] at this
  rwa [inv_mul_cancel₀ hk, one_smul, mul_comm (![(c : F), 1, (c : F)⁻¹] j),
    inv_mul_cancel_left₀ hk] at this

/-- `gl2Torus c` lies in the split centre `A_M` (it acts by scalars on the weight spaces). -/
theorem gl2_torus_mem_wtScalar (c : Fˣ) :
    gl2Torus c ∈ wtScalar (𝔾).QV (𝔾).stdBasis (𝔾).stdWt := by
  refine ⟨fun w => if w = -1 then (c : F) else if w = 1 then (c : F)⁻¹ else 1, by simp,
    fun j => ?_⟩
  rcases j with j | j
  · exact j.elim0
  rw [gl2_torus_apply_std]
  fin_cases j <;> simp [stdWt]

theorem gl2_torus_mem_AMF (c : Fˣ) : (𝔾).inr (gl2Torus c) ∈ (𝕃).AMF :=
  ⟨(1, gl2Torus c), ⟨one_mem _, gl2_torus_mem_wtScalar c⟩, rfl⟩

theorem gl2_torus_mem_M (c : Fˣ) : (𝔾).inr (gl2Torus c) ∈ (𝕃).M := by
  refine ⟨?_, ?_⟩
  · change (𝔾).fst ((𝔾).inr (gl2Torus c)) ∈ flagLevi (Q := (𝔾).QW) (𝕃).bW (𝕃).wtW
    rw [fst_inr_eq_one]; exact one_mem _
  · exact wtScalar_le_flagLevi (gl2_torus_mem_wtScalar c)

/-- **`M ≠ G`**: the empty flag does not give a parabolic of `M`, since `n̄(1) ∈ G` does not
preserve the weight spaces. -/
theorem gl2_len_ne_zero {FW : IsotropicFlag (𝔾).QW} {FV : IsotropicFlag (𝔾).QV}
    (hL : (𝔾).IsLevi FW FV (𝕃).M) : FV.len ≠ 0 := by
  intro h0
  have hp : (gl2Nbar 1)⁻¹ ∈ (𝔾).whittB FW FV := by
    refine ⟨?_, ?_⟩
    · change _ ∈ flagStab FW; rw [gl2_flagStab_W]; trivial
    · change _ ∈ flagStab FV; rw [flagStab_eq_top_of_len_eq_zero FV h0]; trivial
  obtain ⟨m, hm, u, hu, he⟩ := hL.exists_mul hp
  have htop : FV.top = ⊥ := by
    rw [IsotropicFlag.top, show Fin.last FV.len = 0 from Fin.ext (by simp [h0]), FV.sub_zero]
  have hu' : specP (𝔾).QV ((𝔾).snd u) (𝐟 2) = 𝐟 2 := by
    have := hu.2.2.2.1 (𝐟 2) (fun x hx => by
      rw [htop, Submodule.mem_bot] at hx; subst hx; simp)
    rwa [htop, Submodule.mem_bot, sub_eq_zero] at this
  have key := gl2_nbar_inv_two (1 : F)
  rw [← map_inv, he, map_mul, specP_mul_apply, hu', gl2_levi_apply hm.2 2] at key
  have := congrArg (fun x => 𝐟.repr x 1) key
  simp at this

theorem gl2_torus_repr (c : Fˣ) (v : (𝔾).V) (i : Fin 3) :
    𝐟.repr (specP (𝔾).QV (gl2Torus c) v) i =
      (![(c : F), 1, (c : F)⁻¹] : Fin 3 → F) i * 𝐟.repr v i := by
  conv_lhs => rw [← 𝐟.sum_repr v]
  rw [Fin.sum_univ_three]
  simp only [map_add, map_smul, gl2_torus_apply, smul_smul, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul]
  fin_cases i <;> simp [mul_comm]

/-- **`𝒫(M) = {B, B̄}`**: an `M`-stable isotropic line is an eigenline of the torus element
`gl2Torus ϖ` (eigenvalues `ϖ, 1, ϖ⁻¹`), hence `⟨z₁⟩` or `⟨z₋₁⟩` (`⟨z₀⟩` is anisotropic); the
empty flag is excluded since `M ≠ G` (`gl2_len_ne_zero`). -/
theorem gl2_parabolics : (𝔾).parabolics (𝕃).M =
    {(𝕃).toFlagLeviDatum.P, (𝕃).toFlagLeviDatum.opp.P} := by
  ext P
  constructor
  · rintro ⟨FW, FV, rfl, hL⟩
    have hlen : FV.len = 1 :=
      le_antisymm (gl2_flag_len_le_one FV) (Nat.pos_of_ne_zero (gl2_len_ne_zero hL))
    have htop : FV.top ≠ ⊥ := by
      have h := FV.strictMono (show (0 : Fin (FV.len + 1)) < Fin.last FV.len from
        Fin.mk_lt_mk.2 (by simp [hlen]))
      rw [FV.sub_zero] at h
      exact h.ne'
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot htop
    obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one F
    set c : Fˣ := Units.mk0 x (norm_pos_iff.1 hx0)
    have hc1 : (c : F) ≠ 1 := fun h => by
      rw [Units.val_mk0] at h; rw [h, norm_one] at hx1; exact lt_irrefl _ hx1
    have hc1' : (c : F)⁻¹ ≠ 1 := fun h => hc1 (inv_eq_one.1 h)
    have ha : gl2Torus c ∈ flagStab FV := (hL.le (gl2_torus_mem_M c)).2
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.1
      (gl2_top_eq_span hv0 hv ▸ (gl2_mem_flagStab_iff hlen).1 ha v hv)
    have hco : ∀ i, μ * 𝐟.repr v i = (![(c : F), 1, (c : F)⁻¹] : Fin 3 → F) i * 𝐟.repr v i :=
      fun i => by rw [← gl2_torus_repr, ← hμ]; simp
    have hQ : 𝐟.repr v 0 * 𝐟.repr v 2 + 𝐟.repr v 1 ^ 2 = 0 := by
      rw [← gl2_QV_eq]; exact FV.isotropic _ v hv
    have h1 : 𝐟.repr v 1 = 0 := by
      by_contra h1
      have hμ1 : μ = 1 := by simpa [h1] using hco 1
      have h0 : 𝐟.repr v 0 = 0 := by
        have := hco 0; rw [hμ1] at this
        simp only [Matrix.cons_val_zero, one_mul] at this
        by_contra h; exact hc1 (mul_right_cancel₀ h (by rw [one_mul]; exact this.symm))
      have h2 : 𝐟.repr v 2 = 0 := by
        have := hco 2; rw [hμ1] at this
        simp only [Matrix.cons_val, one_mul] at this
        by_contra h; exact hc1' (mul_right_cancel₀ h (by rw [one_mul]; exact this.symm))
      rw [h0, zero_mul, zero_add] at hQ
      exact h1 (pow_eq_zero_iff two_ne_zero |>.1 hQ)
    rw [h1, sq, mul_zero, add_zero, mul_eq_zero] at hQ
    have hB : ∀ FV' : IsotropicFlag (𝔾).QV, FV'.len = 1 → ∀ i : Fin 3, 𝐟 i ∈ FV'.top →
        v = 𝐟.repr v i • 𝐟 i → (𝔾).whittB FW FV = (𝔾).whittB (𝕃).FW FV' := by
      intro FV' h' i hi hvi
      refine gl2_whittB_eq (gl2_flagStab_eq hlen h' ?_)
      rw [gl2_top_eq_span hv0 hv, gl2_top_eq_span (gl2Basis_ne_zero i) hi, hvi,
        Submodule.span_singleton_smul_eq (IsUnit.mk0 _ fun h => hv0 (by rw [hvi, h, zero_smul]))]
    rcases hQ with h0 | h2
    · left
      refine hB (𝕃).FV rfl 2 gl2_two_mem_flag (𝐟.ext_elem fun i => ?_)
      fin_cases i <;> simp [h0, h1]
    · right
      refine (hB (𝕃).toFlagLeviDatum.opp.FV rfl 0 gl2_zero_mem_oppFlag
        (𝐟.ext_elem fun i => ?_)).trans (gl2_whittB_eq rfl)
      fin_cases i <;> simp [h2, h1]
  · rintro (rfl | rfl)
    · exact (𝕃).toFlagLeviDatum.mem_parabolics
    · exact (𝕃).toFlagLeviDatum.opp_mem_parabolics

theorem gl2_nbar_apply (t : F) (v : (𝔾).V) : specP (𝔾).QV ((𝔾).snd (gl2Nbar t)) v =
    quadReflection (𝔾).QV (𝐟 1) (quadReflection (𝔾).QV (𝐟 1 + t • 𝐟 0) v) := by
  rw [gl2Nbar, snd_inr]
  exact LinearMap.congr_fun (specP_gspinPair (𝔾).QV gl2_Q_one (gl2_Q_nbar t)) v

/-- `n̄(t)` fixes `z₋₁`. -/
theorem gl2_nbar_apply_zero (t : F) : specP (𝔾).QV ((𝔾).snd (gl2Nbar t)) (𝐟 0) = 𝐟 0 := by
  conv_lhs => rw [← gl2_nbar_inv_zero t]
  exact specP_inv_apply_apply _ _

/-- **`n̄(t)` is lower unipotent**: it lies in the unipotent radical `Ū` of `B̄`. On `V` it fixes
`z₋₁` and moves `z₋₁^⊥ = ⟨z₋₁, z₀⟩` by multiples of `z₋₁`; in `C(V)`,
`n̄(t) − 1 = t z₀ z₋₁` squares to `0`. -/
theorem gl2_nbar_mem_whittU (t : F) :
    gl2Nbar t ∈ (𝔾).whittU (𝕃).toFlagLeviDatum.opp.FW (𝕃).toFlagLeviDatum.opp.FV := by
  have htop : (𝕃).toFlagLeviDatum.opp.FV.top = Submodule.span F {𝐟 0} :=
    gl2_top_eq_span ((gl2Basis (F := F)).ne_zero 0) gl2_zero_mem_oppFlag
  have hfix : ∀ v ∈ (𝕃).toFlagLeviDatum.opp.FV.top,
      specP (𝔾).QV ((𝔾).snd (gl2Nbar t)) v = v := by
    intro v hv
    rw [htop] at hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [map_smul, gl2_nbar_apply_zero]
  refine ⟨?_, ?_, fun i v hv => ?_, fun v hv => ?_, ?_⟩
  · change (𝔾).fst ((𝔾).inr _) ∈ flagUnip (𝕃).toFlagLeviDatum.opp.FW
    rw [fst_inr_eq_one]; exact one_mem _
  · exact (gl2_mem_flagStab_iff rfl).2 fun v hv => (hfix v hv).symm ▸ hv
  · obtain rfl : i = ⟨0, Nat.zero_lt_one⟩ :=
      Fin.ext (Nat.lt_one_iff.1 (show (i : ℕ) < 1 from i.isLt))
    rw [hfix v hv, sub_self]; exact zero_mem _
  · -- `v ⊥ z₋₁` has no `½ z₁`-coordinate
    have h0 : QuadraticMap.polar (𝔾).QV (𝐟 0) v = 0 := by
      have : bform (𝔾).QV (𝐟 0) v = 0 := hv (𝐟 0) (htop ▸ Submodule.mem_span_singleton_self _)
      rw [polar_eq_two_mul_bform, this, mul_zero]
    rw [gl2_polar] at h0
    simp only [Basis.repr_self, Finsupp.single_apply] at h0
    norm_num at h0
    have hQ : (𝔾).QV (𝐟 1 + t • 𝐟 0) = 1 := by rw [gl2_QV_eq]; simp
    have hQ1 : (𝔾).QV (𝐟 1) = 1 := by rw [gl2_QV_eq]; simp
    have key : specP (𝔾).QV ((𝔾).snd (gl2Nbar t)) v - v = (-(2 * t * 𝐟.repr v 1)) • 𝐟 0 := by
      rw [gl2_nbar_apply, quadReflection_apply, quadReflection_apply, hQ, hQ1,
        gl2_polar, gl2_polar]
      conv_lhs => rw [← 𝐟.sum_repr v]
      simp [h0, smul_add, smul_smul]
      module
    rw [key, htop]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · -- `n̄(t) − 1 = t ι(z₀) ι(z₋₁)` and `(ι(z₀) ι(z₋₁))² = 0`
    refine ⟨2, ?_⟩
    have hQ0 : (𝔾).QV (𝐟 0) = 0 := by rw [gl2_QV_eq]; simp
    have hQ1 : (𝔾).QV (𝐟 1) = 1 := by rw [gl2_QV_eq]; simp
    have hp : QuadraticMap.polar (𝔾).QV (𝐟 0) (𝐟 1) = 0 := by rw [gl2_polar]; simp
    change ((((𝔾).snd (gl2Nbar t) : (CliffordAlgebra (𝔾).QV)ˣ) : CliffordAlgebra (𝔾).QV) - 1) ^ 2
      = 0
    rw [gl2Nbar, snd_inr, coe_gspinPair, map_add, map_smul, mul_add, mul_smul_comm,
      CliffordAlgebra.ι_sq_scalar, hQ1, map_one, add_sub_cancel_left, smul_pow,
      pow_two (CliffordAlgebra.ι (𝔾).QV (𝐟 1) * CliffordAlgebra.ι (𝔾).QV (𝐟 0)), mul_assoc,
      ← mul_assoc (CliffordAlgebra.ι (𝔾).QV (𝐟 0)), CliffordAlgebra.ι_mul_ι_comm, hp,
      map_zero, zero_sub]
    simp only [neg_mul, mul_neg, ← mul_assoc, CliffordAlgebra.ι_sq_scalar, hQ1, map_one, one_mul,
      hQ0, map_zero, neg_zero, smul_zero]

/-! ## `a_M^G ≅ ℝ` and the lattice -/

theorem gl2_mem_aG_iff {H : (𝕃).aM} : H ∈ (𝕃).aG ↔ H gl2c₀ = 0 := by
  rw [(𝕃).mem_aG_iff]
  refine ⟨fun h => h _ gl2_aMG_nontrivial.1, fun h c hc => ?_⟩
  rcases c with (i | _) | (i | _)
  · exact i.elim0
  · exact absurd trivial hc
  · have hi : i = ⟨0, Nat.zero_lt_one⟩ :=
      Fin.ext (by have := i.isLt; change (i : ℕ) < 1 at this; simp only; omega)
    rwa [hi]
  · exact absurd trivial hc

/-- **`a_M^G ≅ ℝ`** through the coordinate `gl2c₀`. -/
def gl2AMGEquiv : (𝕃).aMG ≃L[ℝ] ℝ :=
  (LinearEquiv.ofBijective ((𝕃).aG.liftQ (LinearMap.proj gl2c₀) fun H hH =>
      LinearMap.mem_ker.2 (gl2_mem_aG_iff.1 hH))
    ⟨by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ fun H hH => gl2_mem_aG_iff.2 hH,
    fun r => ⟨(𝕃).aG.mkQ (Pi.single gl2c₀ r), by
      simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.proj_apply,
        Pi.single_eq_same]⟩⟩).toContinuousLinearEquiv

@[simp]
theorem gl2AMGEquiv_mkQ (H : (𝕃).aM) : gl2AMGEquiv ((𝕃).aG.mkQ H) = H gl2c₀ := rfl

theorem gl2Eig_torus (c : Fˣ) : gl2Eig (gl2Torus c) 2 = (c : F)⁻¹ := by
  have h := gl2_torus_apply_std c 2
  simp only [gl2Eig, h, map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one]
  rfl

/-- **`proj_M^G(H_M(A_M(F))) = ℤ ℓ`** under `a_M^G ≅ ℝ`, with `ℓ = −log ‖ϖ‖`: every
`log ‖χ(m)‖` is a multiple of `ℓ`, and `gl2Torus ϖ ∈ A_M(F)` gives `ℓ`. -/
theorem gl2_latticeMG_map {ϖ : F} (h0 : 0 < ‖ϖ‖) (h1 : ‖ϖ‖ < 1)
    (hmax : ∀ x : F, ‖x‖ < 1 → ‖x‖ ≤ ‖ϖ‖) :
    (𝕃).latticeMG.map (gl2AMGEquiv (F := F) : (𝕃).aMG →+ ℝ) =
      AddSubgroup.zmultiples (-Real.log ‖ϖ‖) := by
  rw [ReducedLeviDatum.latticeMG, AddMonoidHom.map_closure]
  refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) ?_
  · rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    obtain ⟨n, hn⟩ := exists_norm_eq_zpow h0 h1 hmax ((𝕃).char gl2c₀ m).ne_zero
    refine ⟨-n, ?_⟩
    change (-n) • (-Real.log ‖ϖ‖) = (𝕃).HM m gl2c₀
    simp only [ReducedLeviDatum.HM, hn, Real.log_zpow, zsmul_eq_mul]
    push_cast; ring
  · rw [AddSubgroup.zmultiples_le]
    have hϖ : ϖ ≠ 0 := norm_pos_iff.1 h0
    refine AddSubgroup.subset_closure ⟨_, ⟨⟨⟨_, gl2_torus_mem_M (Units.mk0 ϖ hϖ)⟩,
      gl2_torus_mem_AMF _⟩, rfl⟩, ?_⟩
    change (𝕃).HM _ gl2c₀ = _
    simp only [ReducedLeviDatum.HM]
    rw [gl2_char_eq, snd_inr, gl2Eig_torus, Units.val_mk0, norm_inv, Real.log_inv]

/-! ## The weight -/

theorem gl2_range_hPar (g : ↥(𝔾).G) :
    (Set.range fun P : ↥((𝔾).parabolics (𝕃).M) => (𝕃).aG.mkQ ((𝕃).hPar gl2GoodK P g)) =
      {(𝕃).aG.mkQ ((𝕃).hPar gl2GoodK gl2B g), (𝕃).aG.mkQ ((𝕃).hPar gl2GoodK gl2Bbar g)} := by
  ext y
  constructor
  · rintro ⟨P, rfl⟩
    have hP := (Set.ext_iff.1 gl2_parabolics _).1 P.property
    rcases hP with h | h
    · left; rw [show P = gl2B from Subtype.ext h]
    · right; rw [show P = gl2Bbar from Subtype.ext h]; rfl
  · rintro (rfl | rfl)
    · exact ⟨gl2B, rfl⟩
    · exact ⟨gl2Bbar, rfl⟩

/-- **The weight of the torus of `GSpin₃ ≅ GL₂` at `n̄(t)`**: for a uniformizer `ϖ` (largest norm
`< 1`), `v_T(n̄(t)) = 2 log max(1, ‖t‖) / (−log ‖ϖ‖)`, i.e. `2 max(0, −val(t))`.  The hull is the
segment between `H_B(n̄(t)) = −2 log max(1, ‖t‖)` and `H_B̄(n̄(t)) = 0` in `a_M^G ≅ ℝ`, whose
lattice is `ℤ (−log ‖ϖ‖)`. -/
theorem gl2_vM_nbar {ϖ : F} (h0 : 0 < ‖ϖ‖) (h1 : ‖ϖ‖ < 1)
    (hmax : ∀ x : F, ‖x‖ < 1 → ‖x‖ ≤ ‖ϖ‖) (t : F) :
    (𝕃).vM gl2GoodK (gl2Nbar t) = 2 * Real.log (max 1 ‖t‖) / (-Real.log ‖ϖ‖) := by
  rw [ReducedLeviDatum.vM, gl2_range_hPar,
    MeasureTheory.Measure.hullVolume_pair_of_equiv gl2AMGEquiv (neg_pos.2 (Real.log_neg h0 h1))
      (gl2_latticeMG_map h0 h1 hmax),
    gl2AMGEquiv_mkQ, gl2AMGEquiv_mkQ, gl2_hPar_B_nbar, gl2_hPar_Bbar_nbar, sub_zero, abs_neg,
    abs_of_nonneg (mul_nonneg zero_le_two (Real.log_nonneg (le_max_left _ _)))]

/-- **`v_T(n̄(ϖ^{−n})) = 2n`.** -/
theorem gl2_vM_nbar_zpow {ϖ : F} (h0 : 0 < ‖ϖ‖) (h1 : ‖ϖ‖ < 1)
    (hmax : ∀ x : F, ‖x‖ < 1 → ‖x‖ ≤ ‖ϖ‖) (n : ℕ) :
    (𝕃).vM gl2GoodK (gl2Nbar (ϖ ^ n)⁻¹) = 2 * n := by
  have hl : Real.log ‖ϖ‖ ≠ 0 := (Real.log_neg h0 h1).ne
  have h1' : 1 ≤ ‖(ϖ ^ n)⁻¹‖ := by
    rw [norm_inv, norm_pow]
    exact one_le_inv₀ (pow_pos h0 n) |>.2 (pow_le_one₀ h0.le h1.le)
  rw [gl2_vM_nbar h0 h1 hmax, max_eq_right h1', norm_inv, norm_pow, Real.log_inv, Real.log_pow]
  field_simp

/-- **`v_T(n̄(t)) = 0` iff `‖t‖ ≤ 1`**, i.e. iff the two points `H_B(n̄(t))`, `H_B̄(n̄(t))`
coincide. -/
theorem gl2_vM_nbar_eq_zero_iff (t : F) : (𝕃).vM gl2GoodK (gl2Nbar t) = 0 ↔ ‖t‖ ≤ 1 := by
  obtain ⟨ϖ, h0, h1, hmax⟩ := exists_norm_lt_one_isGreatest (F := F)
  have hl : 0 < -Real.log ‖ϖ‖ := neg_pos.2 (Real.log_neg h0 h1)
  rw [gl2_vM_nbar h0 h1 hmax, div_eq_zero_iff, or_iff_left hl.ne', mul_eq_zero,
    or_iff_right two_ne_zero, Real.log_eq_zero]
  constructor
  · rintro (h | h | h)
    · exact absurd h (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
    · exact max_eq_left_iff.1 h
    · exact absurd h (by linarith [le_max_left 1 ‖t‖])
  · intro h; exact Or.inr (Or.inl (max_eq_left h))

/-- **`v_T(n̄(t)) > 0` for `‖t‖ > 1`**: the weight of the torus is not identically zero (nor
identically one, by `gl2_vM_nbar_eq_zero_iff`). -/
theorem gl2_vM_nbar_pos {t : F} (ht : 1 < ‖t‖) : 0 < (𝕃).vM gl2GoodK (gl2Nbar t) := by
  obtain ⟨ϖ, h0, h1, hmax⟩ := exists_norm_lt_one_isGreatest (F := F)
  rw [gl2_vM_nbar h0 h1 hmax, max_eq_right ht.le]
  exact div_pos (mul_pos two_pos (Real.log_pos ht)) (neg_pos.2 (Real.log_neg h0 h1))

end GSpinGGP.GGPData
