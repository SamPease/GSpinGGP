/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Basic
import GSpinGGP.Foundations.WeakCartanTheorem
import GSpinGGP.Foundations.QuadraticForms
import GSpinGGP.Foundations.VanDantzig

/-!
# The good minimal parabolic subgroup of Thesis Prop. 8.1.1(i)

Let `z₀ = w₀, w₁, …, w_l` be a maximal frame of `V₀ = W ⊕ ⟨z₀⟩` (`WeakCartan.IsFrame`,
`q(wᵢ) = (-1)ⁱ ν`; it exists by `WeakCartan.exists_isFrame`), realised on the space
`V0 = W × F` (`iota0 : V₀ → V`). Following the proof of Thesis Prop. 8.1.1(i) (BP Prop. 6.4.1):

* `flagW`: the flag `⟨u′₁⟩ ⊂ ⟨u′₁, u′₂⟩ ⊂ ⋯` of `W`, `u′ᵢ = w_{2i-1} + w_{2i}`;
* `flagV`: the flag `⟨z_{-r}⟩ ⊂ ⋯ ⊂ ⟨z_{-r}, …, z_{-1}⟩ ⊂ ⟨z_{-r}, …, z_{-1}, u₁⟩ ⊂ ⋯` of `V`,
  `uᵢ = w_{2i-2} + w_{2i-1}`; its stabilizer is the `GSpin(V)` component of `P̄_min = P̄₀ T N̄`, with `P̄` opposite to the
  stabilizer `P` of the flag `⟨z_r⟩ ⊂ ⋯ ⊂ ⟨z_r, …, z_1⟩` defining `N`.

Results:

* `isFull_flagW`, `isFull_flagV`: both flags are full. The complement of the hyperbolic pairs is
  anisotropic by the maximality of the frame (`WeakCartan.IsFrame.anisotropic`), so the span of
  a flag is a maximal totally isotropic subspace (`IsHypFrame.wittIndex_eq`).
* `H_inf_whittU_eq_bot`: `H ∩ Ū_min = 1`. The thesis shows `H ∩ P̄_min = GSpin(W_an)`; for the
  unipotent radical: `N ∩ P̄ = 1` (`specP_eq_one_of_mem_N_of_fix`), then the frame induction
  (`A0_eq_id`) and the unipotence on `W_an`.
* `isOpen_H_mul_whittB`: `H(F) P̄_min(F)` is open in `G(F)`, from the statement that
  `P̄_W N P̄_V` is a neighbourhood of `1` in `GSpin(V)` (`flagStab_mul_N_mul_flagStab_mem_nhds`,
  `sorry`): `H P̄ = {g : g_W⁻¹ g_V ∈ P̄_W N P̄_V}` (`mem_H_mul_whittB_of_nPart`), and a product of
  two subgroups that is a neighbourhood of `1` is open (`isOpen_subgroup_mul_of_mem_nhds_one`).

General helpers used here live in Foundations: `IsotropicFlag.ofFamily` (`GSpin.lean`),
`orthFrame`/`isHypFrame_orthFrame` (`HypFrame.lean`).

The Haar-null complement of `H(F) P̄_min(F)` (the remaining clause of
`exists_good_minimal_parabolic`) and the `H(F)`-conjugacy of good minimal parabolics are not
treated here.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Module QuadraticMap

namespace GSpinGGP

/-! ## 1. The space `V₀ = W ⊕ ⟨z₀⟩` and its embedding in `V` -/


namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

/-- `V₀ = W ⊕ ⟨z₀⟩`, with `z₀` the generator of `Fin 1 → F` (`q(z₀) = ν`). -/
abbrev V0 : Type := (Fin d.m → F) × (Fin (2 * 0 + 1) → F)

/-- The form of `V₀ = W ⊕^⊥ ⟨z₀⟩`. -/
abbrev Q0 : QuadraticForm F d.V0 := d.QW.prod (splitOddForm 0 (d.ν : F))

theorem nondeg_Q0 : IsNondeg d.Q0 :=
  isNondeg_prod d.nondeg (isNondeg_splitOddForm 0 d.ν.ne_zero)

/-- The vector `z₀ ∈ V₀`. -/
def z00 : d.V0 := (0, zvec 0 0)

theorem Q0_z00 : d.Q0 d.z00 = d.ν := by
  simp [z00, splitOddForm_zvec_zero]

/-- The embedding `V₀ → V`, `(w, c z₀) ↦ (w, c z₀)`. -/
def iota0 : d.V0 →ₗ[F] d.V :=
  LinearMap.prodMap LinearMap.id ((LinearMap.proj 0).smulRight (zvec d.r 0))

/-- The projection `V → V₀` along `⟨z_{±1}, …, z_{±r}⟩`. -/
def pi0 : d.V →ₗ[F] d.V0 :=
  LinearMap.prodMap LinearMap.id ((LinearMap.proj ⟨d.r, by omega⟩).smulRight (zvec 0 0))

theorem iota0_apply (x : d.V0) : d.iota0 x = (x.1, x.2 0 • zvec d.r 0) := rfl

theorem fin_one_eq (c : Fin (2 * 0 + 1) → F) : c = c 0 • zvec 0 0 := by
  ext i
  have : i = 0 := Fin.ext (by have := i.2; omega)
  subst this
  simp [zvec]

theorem pi0_iota0 (x : d.V0) : d.pi0 (d.iota0 x) = x := by
  obtain ⟨w, c⟩ := x
  simp only [pi0, iota0, LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]
  refine Prod.ext rfl ?_
  conv_rhs => rw [fin_one_eq c]
  simp [zvec]

theorem pi0_zV {k : ℤ} (hk : k ≠ 0) : d.pi0 (d.zV k) = 0 := by
  simp only [pi0, zV, LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, zvec]
  rw [ite_eq_right (by push_cast; omega)]
  simp

/-- Vectors with vanishing coordinates off `V₀` lie in `ι₀(V₀)`. -/
theorem eq_iota0_pi0 {v : d.V} (hv : ∀ i : Fin (2 * d.r + 1), (i : ℕ) ≠ d.r → v.2 i = 0) :
    v = d.iota0 (d.pi0 v) := by
  refine Prod.ext rfl (funext fun i => ?_)
  simp only [iota0_apply, pi0, LinearMap.prodMap_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul, zvec]
  by_cases hi : (i : ℕ) = d.r
  · have hlt : d.r < 2 * d.r + 1 := by omega
    rw [show i = ⟨d.r, hlt⟩ from Fin.ext hi]; simp
  · rw [hv i hi]; simp [show ¬ ((i : ℤ) - d.r = 0) by omega]

theorem QV_iota0 (x : d.V0) : d.QV (d.iota0 x) = d.Q0 x := by
  obtain ⟨w, c⟩ := x
  rw [iota0_apply]
  simp only [QV, QZ, Q0, QuadraticMap.prod_apply, QuadraticMap.map_smul,
    splitOddForm_zvec_zero]
  conv_rhs => rw [fin_one_eq c]
  rw [QuadraticMap.map_smul, splitOddForm_zvec_zero]

theorem polar_iota0 (x y : d.V0) :
    polar d.QV (d.iota0 x) (d.iota0 y) = polar d.Q0 x y := by
  simp only [polar, ← map_add, QV_iota0]

theorem bform_iota0_zV {k : ℤ} (hk : k ≠ 0) (hkr : |k| ≤ d.r) (x : d.V0) :
    bform d.QV (d.iota0 x) (d.zV k) = 0 := by
  rw [iota0_apply, zV, bform_prod]
  simp only [map_zero, add_zero, zero_add, LinearMap.map_smul_of_tower, LinearMap.smul_apply]
  rw [bform_splitOddForm_zvec _ _ (by simp) hkr, ite_eq_right (by omega), smul_zero]

theorem polar_iota0_zV {k : ℤ} (hk : k ≠ 0) (hkr : |k| ≤ d.r) (x : d.V0) :
    polar d.QV (d.iota0 x) (d.zV k) = 0 := by
  rw [polar_eq_two_mul_bform, d.bform_iota0_zV hk hkr, mul_zero]

theorem polar_zV_zV {i j : ℤ} (hi : |i| ≤ d.r) (hj : |j| ≤ d.r) :
    polar d.QV (d.zV i) (d.zV j) = if i + j = 0 then 2 * (d.ν : F) else 0 := by
  rw [polar_eq_two_mul_bform, bform_QV_zV, bform_splitOddForm_zvec _ _ hi hj]
  split_ifs <;> simp

/-- `b(x, z_j)` is `ν` times the `z_{-j}`-coordinate of `x`. -/
theorem bform_zV_eq (x : d.V) {j : ℤ} (hj : |j| ≤ d.r) :
    bform d.QV x (d.zV j) =
      (d.ν : F) * x.2 ⟨(d.r - j).toNat, by have := abs_le.mp hj; omega⟩ := by
  rw [zV, bform_prod]
  simp only [map_zero, zero_add]
  rw [zvec_eq_single _ hj, bform_splitOddForm_single]
  congr 2
  refine congrArg x.2 (Fin.ext ?_)
  simp only [Fin.val_rev]
  have := abs_le.mp hj
  omega

/-- `polar(z₀, (w, c)) = 2 ν c` in `V₀`: the frame vectors orthogonal to `z₀` lie in `W`. -/
theorem snd_eq_zero_of_polar_z00 {x : d.V0} (h : polar d.Q0 d.z00 x = 0) : x.2 = 0 := by
  rw [polar_comm, polar_eq_two_mul_bform, bform_prod, z00] at h
  simp only [map_zero, zero_add] at h
  rw [zvec_eq_single _ (by simp), bform_splitOddForm_single] at h
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hx : x.2 0 = 0 := by
    have := (mul_eq_zero.mp h).resolve_left h2
    have := (mul_eq_zero.mp this).resolve_left d.ν.ne_zero
    simpa using this
  rw [fin_one_eq x.2, hx, zero_smul]

end GGPData

/-! ## 2. The explicit full flags of a frame (Thesis Prop. 8.1.1(i)) -/

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

open WeakCartan

section Flags

variable {d} {n l : ℕ} {b : Module.Basis (Fin n) F d.V0}

/-- The frame vectors `w_m`, `m ≥ 1`, lie in `W`. -/
theorem snd_basis_eq_zero (hb : IsOrthoBasis d.Q0 b) (h0 : ∀ h, b ⟨0, h⟩ = d.z00) {m : Fin n}
    (hm : m.val ≠ 0) : (b m).2 = 0 := by
  have hn : 0 < n := by omega
  apply d.snd_eq_zero_of_polar_z00
  rw [← h0 hn]
  exact hb.polar_eq_zero _ _ (fun h => hm (by simp [← h]))

variable (hb : IsOrthoBasis d.Q0 b) (hf : IsFrame d.Q0 b (d.Q0 d.z00) l)
  (h0 : ∀ h, b ⟨0, h⟩ = d.z00)

include hb h0 in
theorem snd_pairE_one (i : Fin (numPairs l 1)) : (pairE hf 1 i).2 = 0 := by
  rw [pairE, Prod.snd_add, snd_basis_eq_zero hb h0 (by simp), snd_basis_eq_zero hb h0 (by simp),
    add_zero]

include hb h0 in
theorem snd_pairF_one (i : Fin (numPairs l 1)) : (pairF hf 1 i).2 = 0 := by
  rw [pairF, Prod.smul_snd, Prod.snd_sub, snd_basis_eq_zero hb h0 (by simp),
    snd_basis_eq_zero hb h0 (by simp), sub_zero, smul_zero]

theorem polar_Q0_of_snd {x y : d.V0} (hx : x.2 = 0) : polar d.Q0 x y = polar d.QW x.1 y.1 := by
  rw [polar_prod, hx, polar_zero_left, add_zero]

/-- The isotropic vectors `u′ᵢ = w_{2i-1} + w_{2i}` of `W` (Thesis Prop. 8.1.1(i)). -/
def eW (i : Fin (numPairs l 1)) : Fin d.m → F := (pairE hf 1 i).1

/-- Their dual isotropic vectors. -/
def fW (i : Fin (numPairs l 1)) : Fin d.m → F := (pairF hf 1 i).1

include hb h0 in
theorem inl_eW (i : Fin (numPairs l 1)) : ((eW hf i, 0) : d.V0) = pairE hf 1 i :=
  Prod.ext rfl (snd_pairE_one hb hf h0 i).symm

include hb h0 in
theorem inl_fW (i : Fin (numPairs l 1)) : ((fW hf i, 0) : d.V0) = pairF hf 1 i :=
  Prod.ext rfl (snd_pairF_one hb hf h0 i).symm

include hb h0 in
theorem isHypFrame_W : IsHypFrame d.QW (orthFrame d.QW (eW hf) (fW hf)) (eW hf) (fW hf) := by
  have H := isHypFrame_pair hb hf 1
  have e : ∀ x y : Fin d.m → F, polar d.QW x y = polar d.Q0 (x, 0) (y, 0) := fun x y => by
    rw [polar_Q0_of_snd rfl]
  refine isHypFrame_orthFrame (fun i j => ?_) (fun i j => ?_) (fun i j => ?_)
  · rw [e, inl_eW hb hf h0, inl_eW hb hf h0]; exact H.polar_ee i j
  · rw [e, inl_fW hb hf h0, inl_fW hb hf h0]; exact H.polar_ff i j
  · rw [e, inl_eW hb hf h0, inl_fW hb hf h0]; exact H.polar_ef i j

include hb h0 in
/-- The complement of the pairs `(u′ᵢ, ·)` in `W` (the anisotropic kernel of `W`) is
anisotropic. -/
theorem aniso_W {y : Fin d.m → F} (hy : y ∈ orthFrame d.QW (eW hf) (fW hf)) (hQ : d.QW y = 0) :
    y = 0 := by
  have H := isHypFrame_pair hb hf 1
  set x : d.V0 := (y, 0)
  have hxc : x ∈ pairCompl b l 1 := by
    rw [H.mem_iff]
    intro i
    rw [← inl_eW hb hf h0, ← inl_fW hb hf h0, polar_Q0_of_snd rfl, polar_Q0_of_snd rfl]
    exact hy i
  rw [pairCompl, Basis.mem_span_image] at hxc
  have hx : ∀ i : Fin n, i.val < l → b.repr x i = 0 := by
    intro i hi
    by_cases hi0 : i.val = 0
    · have hi' : i = ⟨0, by omega⟩ := Fin.ext hi0
      have hp : polar d.Q0 (b i) x = 0 := by
        rw [hi', h0, polar_comm, polar_Q0_of_snd rfl]
        simp [z00]
      rw [hb.repr_eq_polar_div, hp, zero_div]
    · by_contra hne
      have := hxc (Finsupp.mem_support_iff.mpr hne)
      simp only [Set.mem_ofPred_eq, numPairs] at this
      omega
  have hx0 := hf.anisotropic hb hx (by simp [x, hQ])
  exact congrArg Prod.fst hx0

/-- The full isotropic flag `⟨u′₁⟩ ⊂ ⟨u′₁, u′₂⟩ ⊂ ⋯` of `W` (Thesis Prop. 8.1.1(i)). -/
def flagW : IsotropicFlag d.QW :=
  IsotropicFlag.ofFamily (eW hf)
    ((isHypFrame_W hb hf h0).linearIndependent.comp Sum.inl Sum.inl_injective)
    (isHypFrame_W hb hf h0).isTotallyIsotropic_span_e

theorem isFull_flagW : (flagW hb hf h0).IsFull :=
  IsotropicFlag.isFull_ofFamily
    ((isHypFrame_W hb hf h0).wittIndex_eq d.nondeg
      (fun x hx => Subtype.ext (aniso_W hb hf h0 x.2 hx))).symm

/-- `z_{-r}, …, z_{-1}`: the first `r` vectors of the flag of `V`. -/
def zb (k : Fin d.r) : d.V := d.zV (-((d.r : ℤ) - (k : ℕ)))

/-- Their duals `(2ν)⁻¹ z_r, …, (2ν)⁻¹ z_1`. -/
def zbD (k : Fin d.r) : d.V := (2 * (d.ν : F))⁻¹ • d.zV ((d.r : ℤ) - (k : ℕ))

/-- The isotropic vectors `z_{-r}, …, z_{-1}, u₁, u₂, …` of `V` (Thesis Prop. 8.1.1(i): the
flag of `P̄_min = P̄₀ T N̄`, `P̄` opposite to the stabilizer `P` of `⟨z_r⟩ ⊂ ⋯ ⊂ ⟨z_r, …, z_1⟩`). -/
def eV : Fin (d.r + numPairs l 0) → d.V := Fin.append (zb (d := d)) (d.iota0 ∘ pairE hf 0)

/-- Their duals. -/
def fV : Fin (d.r + numPairs l 0) → d.V := Fin.append (zbD (d := d)) (d.iota0 ∘ pairF hf 0)

theorem abs_neg_le (k : Fin d.r) : |(-((d.r : ℤ) - (k : ℕ)))| ≤ d.r := by
  have := k.2; rw [abs_le]; constructor <;> omega

theorem abs_pos_le (k : Fin d.r) : |((d.r : ℤ) - (k : ℕ))| ≤ d.r := by
  have := k.2; rw [abs_le]; constructor <;> omega

theorem polar_zb_zb (k k' : Fin d.r) : polar d.QV (zb (d := d) k) (zb (d := d) k') = 0 := by
  rw [zb, zb, d.polar_zV_zV (abs_neg_le k) (abs_neg_le k'),
    ite_eq_right (by have := k.2; have := k'.2; omega)]

theorem polar_zbD_zbD (k k' : Fin d.r) : polar d.QV (zbD (d := d) k) (zbD (d := d) k') = 0 := by
  rw [zbD, zbD, polar_smul_left, polar_smul_right, d.polar_zV_zV (abs_pos_le k) (abs_pos_le k'),
    ite_eq_right (by have := k.2; have := k'.2; omega)]
  simp

theorem polar_zb_zbD (k k' : Fin d.r) :
    polar d.QV (zb (d := d) k) (zbD (d := d) k') = if k = k' then 1 else 0 := by
  rw [zb, zbD, polar_smul_right, d.polar_zV_zV (abs_neg_le k) (abs_pos_le k')]
  by_cases h : k = k'
  · subst h
    rw [ite_eq_left (by ring), ite_eq_left rfl, smul_eq_mul]
    exact inv_mul_cancel₀ (mul_ne_zero two_ne_zero d.ν.ne_zero)
  · rw [ite_eq_right (fun h' => h (Fin.ext (by omega))), ite_eq_right h, smul_zero]

theorem polar_zb_iota0 (k : Fin d.r) (x : d.V0) : polar d.QV (zb (d := d) k) (d.iota0 x) = 0 := by
  rw [polar_comm, zb, d.polar_iota0_zV (by have := k.2; omega) (abs_neg_le k)]

theorem polar_zbD_iota0 (k : Fin d.r) (x : d.V0) :
    polar d.QV (zbD (d := d) k) (d.iota0 x) = 0 := by
  rw [polar_comm, zbD, polar_smul_right, d.polar_iota0_zV (by have := k.2; omega) (abs_pos_le k),
    smul_zero]

include hb h0 in
theorem isHypFrame_V : IsHypFrame d.QV (orthFrame d.QV (eV hf) (fV hf)) (eV hf) (fV hf) := by
  have H := isHypFrame_pair hb hf 0
  refine isHypFrame_orthFrame (fun i j => ?_) (fun i j => ?_) (fun i j => ?_)
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
      refine Fin.addCases (fun k' => ?_) (fun k' => ?_) j <;>
      simp only [eV, Fin.append_left, Fin.append_right, Function.comp_apply]
    · exact polar_zb_zb k k'
    · exact polar_zb_iota0 k _
    · rw [polar_comm]; exact polar_zb_iota0 k' _
    · rw [d.polar_iota0]; exact H.polar_ee k k'
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
      refine Fin.addCases (fun k' => ?_) (fun k' => ?_) j <;>
      simp only [fV, Fin.append_left, Fin.append_right, Function.comp_apply]
    · exact polar_zbD_zbD k k'
    · exact polar_zbD_iota0 k _
    · rw [polar_comm]; exact polar_zbD_iota0 k' _
    · rw [d.polar_iota0]; exact H.polar_ff k k'
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
      refine Fin.addCases (fun k' => ?_) (fun k' => ?_) j <;>
      simp only [eV, fV, Fin.append_left, Fin.append_right, Function.comp_apply]
    · rw [polar_zb_zbD]
      simp only [(Fin.castAdd_injective _ _).eq_iff]
    · rw [polar_zb_iota0, ite_eq_right (fun h => by
        have := congrArg Fin.val h; simp at this; omega)]
    · rw [polar_comm, polar_zbD_iota0, ite_eq_right (fun h => by
        have := congrArg Fin.val h; simp at this; omega)]
    · rw [d.polar_iota0, H.polar_ef k k']
      simp only [(Fin.natAdd_injective _ _).eq_iff]

include hb h0 in
/-- `V_an`, the complement of the pairs of `V`, is anisotropic. -/
theorem aniso_V {y : d.V} (hy : y ∈ orthFrame d.QV (eV hf) (fV hf)) (hQ : d.QV y = 0) :
    y = 0 := by
  have H := isHypFrame_pair hb hf 0
  -- `y ⊥ z_j` for `j ≠ 0`
  have hz : ∀ j : ℤ, j ≠ 0 → |j| ≤ d.r → bform d.QV y (d.zV j) = 0 := by
    intro j hj hjr
    have hj' := abs_le.mp hjr
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    rcases lt_or_gt_of_ne hj with hneg | hpos
    · have := (hy (Fin.castAdd _ ⟨(d.r - (-j).toNat : ℕ), by omega⟩)).1
      simp only [eV, Fin.append_left, zb] at this
      rw [polar_eq_two_mul_bform] at this
      have e : (-((d.r : ℤ) - ((d.r - (-j).toNat : ℕ) : ℕ))) = j := by omega
      rw [e] at this
      exact (mul_eq_zero.mp this).resolve_left h2
    · have := (hy (Fin.castAdd _ ⟨(d.r - j.toNat : ℕ), by omega⟩)).2
      simp only [fV, Fin.append_left, zbD] at this
      rw [polar_smul_right, polar_eq_two_mul_bform, smul_eq_mul] at this
      have e : ((d.r : ℤ) - ((d.r - j.toNat : ℕ) : ℕ)) = j := by omega
      rw [e] at this
      have hν : (2 * (d.ν : F))⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero h2 d.ν.ne_zero)
      exact (mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hν)).resolve_left h2
  -- so `y = ι₀ (π₀ y)`
  have hyi : y = d.iota0 (d.pi0 y) := by
    refine d.eq_iota0_pi0 fun t ht => ?_
    have ht2 := t.2
    have habs : |(d.r : ℤ) - t| ≤ d.r := by rw [abs_le]; constructor <;> omega
    have hj := hz ((d.r : ℤ) - t) (by omega) habs
    rw [bform_zV_eq _ _ habs] at hj
    have e : (⟨((d.r : ℤ) - ((d.r : ℤ) - t)).toNat, by omega⟩ : Fin (2 * d.r + 1)) = t :=
      Fin.ext (by simp)
    rw [e] at hj
    exact (mul_eq_zero.mp hj).resolve_left d.ν.ne_zero
  -- and `π₀ y` lies past the frame
  set x := d.pi0 y
  have hxc : x ∈ pairCompl b l 0 := by
    rw [H.mem_iff]
    intro i
    have := hy (Fin.natAdd _ i)
    simp only [eV, fV, Fin.append_right, Function.comp_apply] at this
    rw [hyi, d.polar_iota0, d.polar_iota0] at this
    exact this
  rw [pairCompl, Basis.mem_span_image] at hxc
  have hx : ∀ i : Fin n, i.val < l → b.repr x i = 0 := by
    intro i hi
    by_contra hne
    have := hxc (Finsupp.mem_support_iff.mpr hne)
    simp only [Set.mem_ofPred_eq, numPairs] at this
    omega
  have hQx : d.Q0 x = 0 := by rw [← d.QV_iota0, ← hyi, hQ]
  rw [hyi, hf.anisotropic hb hx hQx, map_zero]

/-- The full isotropic flag `⟨z_{-r}⟩ ⊂ ⋯ ⊂ ⟨z_{-r}, …, z_{-1}⟩ ⊂ ⟨z_{-r}, …, z_{-1}, u₁⟩ ⊂ ⋯`
of `V` (Thesis Prop. 8.1.1(i)). -/
def flagV : IsotropicFlag d.QV :=
  IsotropicFlag.ofFamily (eV hf)
    ((isHypFrame_V hb hf h0).linearIndependent.comp Sum.inl Sum.inl_injective)
    (isHypFrame_V hb hf h0).isTotallyIsotropic_span_e

theorem isFull_flagV : (flagV hb hf h0).IsFull :=
  IsotropicFlag.isFull_ofFamily
    ((isHypFrame_V hb hf h0).wittIndex_eq d.nondeg_QV
      (fun x hx => Subtype.ext (aniso_V hb hf h0 x.2 hx))).symm

end Flags

end GGPData

/-! ## 3. `H ∩ Ū_min = 1` -/


namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

/-- **`N ∩ P̄ = 1` at the level of `SO(V)`, first half.** If `n ∈ N` moves `z_{-k}` only by
earlier vectors `z_{-r}, …, z_{-k-1}` of the opposite flag, it fixes `z_{-k}`. -/
theorem specP_zb_of_mem_N {nn : GSpin d.QV} (hn : nn ∈ d.N) (k : Fin d.r)
    (hz : specP d.QV nn (zb (d := d) k) - zb (d := d) k ∈
      Submodule.span F (Set.range (d.zV ∘ fun j : Fin k => -((d.r : ℤ) - (j : ℕ))))) :
    specP d.QV nn (zb (d := d) k) = zb (d := d) k := by
  have hk := k.2
  rw [← sub_eq_zero]
  refine d.eq_zero_of_mem_span_zV _ (fun a c h => Fin.ext (by simp at h; omega))
    (fun j => by have := j.2; rw [abs_le]; constructor <;> omega) hz (fun j => ?_)
  have hj := j.2
  rw [neg_neg, map_sub, LinearMap.sub_apply]
  set s : ℕ := d.r - j with hs
  have hs' : ((d.r : ℤ) - (j : ℕ)) = ((s : ℕ) : ℤ) := by omega
  rw [hs']
  have e : bform d.QV (specP d.QV nn (zb (d := d) k)) (d.zV (s : ℕ)) =
      bform d.QV (zb (d := d) k) (specP d.QV nn⁻¹ (d.zV (s : ℕ))) := by
    conv_lhs => arg 2; rw [← specP_inv_apply_apply nn (d.zV (s : ℕ))]
    rw [bform_specP]
  have hzs : bform d.QV (zb (d := d) k) (d.zV (s : ℕ)) = 0 := by
    rw [zb, bform_QV_zV, bform_splitOddForm_zvec _ _ (abs_neg_le k)
      (by rw [abs_le]; constructor <;> omega), ite_eq_right (by omega)]
  have hε := d.specP_zV_sub_mem (s := s) (by omega) (d.N.inv_mem hn)
  have hε0 : bform d.QV (zb (d := d) k) (specP d.QV nn⁻¹ (d.zV (s : ℕ)) - d.zV (s : ℕ)) = 0 :=
    d.bform_zV_eq_zero_of_mem_span (fun j' : Fin (d.r - s) => (d.r : ℤ) - (j' : ℕ))
      (abs_neg_le k) (fun j' => by have := j'.2; rw [abs_le]; constructor <;> omega)
      (fun j' => by have := j'.2; omega) hε
  rw [e, hzs, sub_zero]
  rw [map_sub, hzs, sub_zero] at hε0
  exact hε0

/-- `P_W(a) ⊕ 1` on `V₀ = W ⊕ ⟨z₀⟩`: the action of `a ∈ GSpin(W) ⊆ GSpin(V)` on `V₀`. -/
def A0 (a : GSpin d.QW) : d.V0 →ₗ[F] d.V0 :=
  ((specP d.QW a : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).prodMap
    LinearMap.id

theorem A0_apply (a : GSpin d.QW) (x : d.V0) : d.A0 a x = (specP d.QW a x.1, x.2) := rfl

theorem specP_incl_iota0 (a : GSpin d.QW) (x : d.V0) :
    specP d.QV (d.incl a) (d.iota0 x) = d.iota0 (d.A0 a x) := by
  have e : d.iota0 x = (x.1, 0) + (0, x.2 0 • zvec d.r 0) := by
    rw [iota0_apply]; simp
  rw [e, map_add, specP_incl_inl, d.specP_incl_inr, iota0_apply, A0_apply]
  simp

theorem polar_A0 (a : GSpin d.QW) (x y : d.V0) :
    polar d.Q0 (d.A0 a x) (d.A0 a y) = polar d.Q0 x y := by
  rw [A0_apply, A0_apply, polar_prod, polar_prod, Steinberg.polar_specP]

end GGPData

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {d : GGPData F}

open WeakCartan

section HU

variable {n l : ℕ} {b : Module.Basis (Fin n) F d.V0}
  (hb : IsOrthoBasis d.Q0 b) (hf : IsFrame d.Q0 b (d.Q0 d.z00) l) (h0 : ∀ h, b ⟨0, h⟩ = d.z00)

theorem eV_of_lt {i : Fin (d.r + numPairs l 0)} (hi : (i : ℕ) < d.r) :
    eV hf i = zb (d := d) ⟨i, hi⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k : Fin d.r, Fin.castAdd (numPairs l 0) k = i := ⟨⟨i, hi⟩, Fin.ext rfl⟩
  rw [eV, Fin.append_left]
  rfl

theorem eV_of_ge {i : Fin (d.r + numPairs l 0)} (hi : d.r ≤ (i : ℕ)) :
    eV hf i = d.iota0 (pairE hf 0 ⟨i - d.r, by have := i.2; omega⟩) := by
  obtain ⟨k, rfl⟩ : ∃ k : Fin (numPairs l 0), Fin.natAdd d.r k = i :=
    ⟨⟨i - d.r, by have := i.2; omega⟩, Fin.ext (by simp; omega)⟩
  rw [eV, Fin.append_right]
  simp

include hb h0 in
/-- The induction over the frame: `P_W(a) ⊕ 1` fixes `V₀` if it moves each `u_i` (resp. `u′_i`)
only by earlier frame vectors, and each `w ∈ W_an` only within `⟨u′⟩`. -/
theorem A0_eq_id {a : GSpin d.QW}
    (hFV : ∀ i : Fin (numPairs l 0), d.A0 a (pairE hf 0 i) - pairE hf 0 i ∈
      Submodule.span F (b '' {m | m.val < 2 * (i : ℕ)}))
    (hFW : ∀ i : Fin (numPairs l 1), d.A0 a (pairE hf 1 i) - pairE hf 1 i ∈
      Submodule.span F (b '' {m | m.val < 1 + 2 * (i : ℕ)}))
    (hWan : ∀ m : Fin n, l < m.val →
      d.A0 a (b m) - b m ∈ Submodule.span F (b '' {m | m.val ≤ l})) :
    d.A0 a = LinearMap.id := by
  have hiso := d.polar_A0 a
  have hlow : ∀ M, ∀ m : Fin n, m.val ≤ l → m.val = M → d.A0 a (b m) = b m := by
    intro M
    induction M using Nat.strong_induction_on with
    | _ M ih =>
    intro m hml hmM
    have hS : ∀ j ∈ {j : Fin n | j.val < M}, d.A0 a (b j) = b j :=
      fun j hj => ih j.val hj j (by simp only [Set.mem_ofPred_eq] at hj; omega) rfl
    have hm : m ∉ {j : Fin n | j.val < M} := by simp only [Set.mem_ofPred_eq]; omega
    have hlt := hf.lt
    rcases Nat.even_or_odd M with ⟨i, hi⟩ | ⟨i, hi⟩
    · rcases Nat.eq_zero_or_pos i with rfl | hipos
      · have : m = ⟨0, by omega⟩ := Fin.ext (by simp; omega)
        rw [this, h0, A0_apply]
        simp [z00]
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        have hi' : i' < numPairs l 1 := by simp only [numPairs]; omega
        refine hb.apply_eq_of_sub_mem_span hiso hS hm ?_
        have e : d.A0 a (b m) - b m =
            d.A0 a (pairE hf 1 ⟨i', hi'⟩) - pairE hf 1 ⟨i', hi'⟩ := by
          have hm' : m = ⟨1 + 2 * i' + 1, by omega⟩ := Fin.ext (by simp; omega)
          simp only [pairE, map_add, Fin.val_mk]
          rw [hS ⟨1 + 2 * i', by omega⟩ (show 1 + 2 * i' < M by omega), ← hm']
          abel
        rw [e]
        exact Submodule.span_mono (Set.image_mono fun j hj => by
          simp only [Set.mem_ofPred_eq] at hj ⊢; omega) (hFW _)
    · have hi' : i < numPairs l 0 := by simp only [numPairs]; omega
      refine hb.apply_eq_of_sub_mem_span hiso hS hm ?_
      have e : d.A0 a (b m) - b m =
          d.A0 a (pairE hf 0 ⟨i, hi'⟩) - pairE hf 0 ⟨i, hi'⟩ := by
        have hm' : m = ⟨0 + 2 * i + 1, by omega⟩ := Fin.ext (by simp; omega)
        simp only [pairE, map_add, Fin.val_mk]
        rw [hS ⟨0 + 2 * i, by omega⟩ (show 0 + 2 * i < M by omega), ← hm']
        abel
      rw [e]
      exact Submodule.span_mono (Set.image_mono fun j hj => by
        simp only [Set.mem_ofPred_eq] at hj ⊢; omega) (hFV _)
  refine b.ext fun m => ?_
  rw [LinearMap.id_apply]
  by_cases hml : m.val ≤ l
  · exact hlow _ m hml rfl
  · exact hb.apply_eq_of_sub_mem_span hiso (S := {j | j.val ≤ l})
      (fun j hj => hlow _ j hj rfl) (by simp only [Set.mem_ofPred_eq]; omega)
      (hWan m (by omega))

include hb h0 in
/-- **`H ∩ Ū_min = 1`** for the explicit good minimal parabolic (Thesis Prop. 8.1.1(i); the proof
of `H ∩ P̄_min = GSpin(W_an)` there). For `g = (a, a n) ∈ H ∩ Ū_min`: `n ∈ N` fixes the opposite
flag `z_{-r}, …, z_{-1}`, hence acts trivially (`N ∩ P̄ = 1`), so `n = 1`; then `a` fixes
`w₀ = z₀`, and alternately the flags of `V` and of `W` force it to fix `w₁, …, w_l`, and finally
`W_an`; so `a` is a unipotent scalar, `a = 1`. -/
theorem H_inf_whittU_eq_bot : d.H ⊓ d.whittU (flagW hb hf h0) (flagV hb hf h0) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgH, hgU⟩
  rw [Subgroup.mem_bot]
  obtain ⟨haU, hbU⟩ := hgU
  replace haU : d.fst g ∈ flagUnip (flagW hb hf h0) := haU
  replace hbU : d.snd g ∈ flagUnip (flagV hb hf h0) := hbU
  set a := d.fst g with ha
  set bb := d.snd g with hbb'
  have hnn : d.nPart g ∈ d.N := hgH
  set nn := d.nPart g with hnn'
  have hbb : bb = d.incl a * nn := by rw [hnn', nPart, mul_inv_cancel_left]
  have hlen : (flagV hb hf h0).len = d.r + numPairs l 0 := rfl
  -- step 1: `n` fixes `z_{-r}, …, z_{-1}`
  have hfix : ∀ k : Fin d.r, specP d.QV nn (zb (d := d) k) = zb (d := d) k := by
    intro k
    have hk := k.2
    apply d.specP_zb_of_mem_N hnn k
    have hv : zb (d := d) k ∈ (flagV hb hf h0).sub (Fin.succ ⟨k, by rw [hlen]; omega⟩) := by
      rw [← eV_of_lt hf (i := ⟨k, by omega⟩) hk]
      exact IsotropicFlag.mem_ofFamily_sub (by simp)
    have hcl := hbU.2.1 ⟨k, by rw [hlen]; omega⟩ _ hv
    have hsub : (flagV hb hf h0).sub (Fin.castSucc ⟨k, by rw [hlen]; omega⟩) =
        Submodule.span F (Set.range (d.zV ∘ fun j : Fin k => -((d.r : ℤ) - (j : ℕ)))) := by
      change Submodule.span F (Set.range (eV hf ∘ Fin.castLE (Fin.is_le _))) = _
      congr 2
      funext j
      simp only [Function.comp_apply]
      rw [eV_of_lt hf (by simp; omega)]
      rfl
    rw [hsub] at hcl
    have hfst : (specP d.QV bb (zb (d := d) k) - zb (d := d) k).1 = 0 := by
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hcl
      rw [← hc]
      simp [Prod.fst_sum, zV]
    have e : specP d.QV nn (zb (d := d) k) - zb (d := d) k =
        specP d.QV bb (zb (d := d) k) - zb (d := d) k := by
      have h1 : ∀ v : d.V, v.1 = 0 → specP d.QV (d.incl a)⁻¹ v = v := by
        rintro ⟨w, z⟩ hw
        simp only at hw
        rw [hw, ← map_inv]
        exact d.specP_incl_inr _ z
      have hnn2 : nn = (d.incl a)⁻¹ * bb := by rw [hbb]; group
      rw [hnn2, specP_mul_apply]
      set δ := specP d.QV bb (zb (d := d) k) - zb (d := d) k
      have : specP d.QV bb (zb (d := d) k) = zb (d := d) k + δ := by simp [δ]
      rw [this, map_add, h1 _ rfl, h1 _ hfst]
      abel
    rw [e]; exact hcl
  -- step 2: `n = 1`
  have hn1 : nn = 1 :=
    eq_one_of_specP_eq_one d.nondeg_QV (d.specP_eq_one_of_mem_N_of_fix hnn hfix) hnn.2.2.2
  have hbb1 : bb = d.incl a := by rw [hbb, hn1, mul_one]
  -- step 3: `a` acts trivially on `V₀`, by the induction over the frame
  have hFW : ∀ i : Fin (numPairs l 1), d.A0 a (pairE hf 1 i) - pairE hf 1 i ∈
      Submodule.span F (b '' {m | m.val < 1 + 2 * (i : ℕ)}) := by
    intro i
    have hv : eW hf i ∈ (flagW hb hf h0).sub (Fin.succ (⟨i, i.2⟩ : Fin (numPairs l 1))) :=
      IsotropicFlag.mem_ofFamily_sub (Nat.lt_succ_self (i : ℕ))
    have hcl := haU.2.1 ⟨i, i.2⟩ _ hv
    change _ ∈ Submodule.span F
      (Set.range (eW hf ∘ Fin.castLE (Fin.is_le _))) at hcl
    have e : d.A0 a (pairE hf 1 i) - pairE hf 1 i =
        LinearMap.inl F _ (Fin (2 * 0 + 1) → F) (specP d.QW a (eW hf i) - eW hf i) := by
      rw [← inl_eW hb hf h0, A0_apply]
      ext <;> simp
    rw [e]
    have hmap := Submodule.mem_map_of_mem
      (f := LinearMap.inl F (Fin d.m → F) (Fin (2 * 0 + 1) → F)) hcl
    rw [Submodule.map_span] at hmap
    refine Submodule.span_le.mpr ?_ hmap
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    simp only [Function.comp_apply, LinearMap.inl_apply]
    rw [inl_eW hb hf h0]
    exact pairE_mem_span hf 1 _ (by simp; omega)
  have hFV : ∀ i : Fin (numPairs l 0), d.A0 a (pairE hf 0 i) - pairE hf 0 i ∈
      Submodule.span F (b '' {m | m.val < 2 * (i : ℕ)}) := by
    intro i
    have hi := i.2
    have hv : eV hf (Fin.natAdd d.r i) ∈
        (flagV hb hf h0).sub (Fin.succ (⟨d.r + i, by rw [hlen]; omega⟩ : Fin _)) :=
      IsotropicFlag.mem_ofFamily_sub (by simp)
    have hcl := hbU.2.1 ⟨d.r + i, by rw [hlen]; omega⟩ _ hv
    change _ ∈ Submodule.span F
      (Set.range (eV hf ∘ Fin.castLE (Fin.is_le _))) at hcl
    have hev : eV hf (Fin.natAdd d.r i) = d.iota0 (pairE hf 0 i) := by
      rw [eV, Fin.append_right]; rfl
    rw [hev, hbb1, d.specP_incl_iota0, ← map_sub] at hcl
    have hmap := Submodule.mem_map_of_mem (f := d.pi0) hcl
    rw [d.pi0_iota0, Submodule.map_span] at hmap
    refine Submodule.span_le.mpr ?_ hmap
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    simp only [Function.comp_apply]
    have hj : (j : ℕ) < d.r + i := j.2
    by_cases hjr : (j : ℕ) < d.r
    · rw [eV_of_lt hf (by simpa using hjr), zb, d.pi0_zV (by omega)]
      exact zero_mem _
    · rw [eV_of_ge hf (by simp; omega), d.pi0_iota0]
      exact pairE_mem_span hf 0 _ (by simp; omega)
  have hpolar_ne : ∀ p q : Fin n, p ≠ q → polar d.Q0 (b p) (b q) = 0 := hb.polar_eq_zero
  have hWan : ∀ m : Fin n, l < m.val →
      d.A0 a (b m) - b m ∈ Submodule.span F (b '' {m | m.val ≤ l}) := by
    intro m hm
    have hm2 : (b m).2 = 0 := snd_basis_eq_zero hb h0 (by omega)
    have horth : (b m).1 ∈ (bform d.QW).orthogonal (flagW hb hf h0).top := by
      intro t ht
      change t ∈ Submodule.span F
        (Set.range (eW hf ∘ Fin.castLE (Fin.is_le _))) at ht
      refine Submodule.span_induction (p := fun t _ => bform d.QW t (b m).1 = 0) ?_ (by simp)
        (fun x y _ _ hx hy => by rw [map_add, LinearMap.add_apply, hx, hy, add_zero])
        (fun c x _ hx => by rw [map_smul, LinearMap.smul_apply, hx, smul_zero]) ht
      rintro _ ⟨j, rfl⟩
      simp only [Function.comp_apply]
      have hj : (j : ℕ) < l / 2 := j.2
      have hp : polar d.QW (eW hf (Fin.castLE (Fin.is_le _) j)) (b m).1 = 0 := by
        rw [eW, ← polar_Q0_of_snd (snd_pairE_one hb hf h0 _), pairE, polar_add_left,
          hpolar_ne _ _ (fun h => by
            have h' := congrArg Fin.val h
            try simp only [Fin.val_castLE] at h'
            omega),
          hpolar_ne _ _ (fun h => by
            have h' := congrArg Fin.val h
            try simp only [Fin.val_castLE] at h'
            omega),
          add_zero]
      rw [polar_eq_two_mul_bform] at hp
      exact (mul_eq_zero.mp hp).resolve_left two_ne_zero
    have hcl := haU.2.2.1 _ horth
    change _ ∈ Submodule.span F
      (Set.range (eW hf ∘ Fin.castLE (Fin.is_le _))) at hcl
    have e : d.A0 a (b m) - b m =
        LinearMap.inl F _ (Fin (2 * 0 + 1) → F) (specP d.QW a (b m).1 - (b m).1) := by
      rw [A0_apply]
      ext <;> simp [hm2]
    rw [e]
    have hmap := Submodule.mem_map_of_mem
      (f := LinearMap.inl F (Fin d.m → F) (Fin (2 * 0 + 1) → F)) hcl
    rw [Submodule.map_span] at hmap
    refine Submodule.span_le.mpr ?_ hmap
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    simp only [Function.comp_apply, LinearMap.inl_apply]
    rw [inl_eW hb hf h0]
    have hj : (j : ℕ) < l / 2 := j.2
    exact Submodule.span_mono (Set.image_mono fun q hq => by
        simp only [Set.mem_ofPred_eq] at hq ⊢; omega)
      (pairE_mem_span hf 1 _ (M := l + 1) (by simp only [Fin.val_castLE]; omega))
  have hA := A0_eq_id hb hf h0 hFV hFW hWan
  have hPa : specP d.QW a = 1 := LinearEquiv.ext fun w => by
    have := congrArg Prod.fst (LinearMap.congr_fun hA (w, 0))
    simpa [A0_apply] using this
  have ha1 : a = 1 := eq_one_of_specP_eq_one d.nondeg hPa haU.2.2.2
  refine d.G_ext ?_ ?_
  · rw [map_one, ← ha, ha1]
  · rw [map_one, ← hbb', hbb1, ha1, map_one]

end HU

end GGPData

/-! ## 4. Openness of `H·P̄_min` -/

open scoped Pointwise Topology


namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

/-- **`H·P̄` described through `n(g) = g_W⁻¹ g_V`**: if `n(g) ∈ P̄_W N P̄_V` (with `P̄_W ⊆ GSpin(W)`
embedded in `GSpin(V)`), then `g ∈ H·P̄`: for `n(g) = q n p`,
`g = (g_W q, g_W q n) · (q⁻¹, p)`. -/
theorem mem_H_mul_whittB_of_nPart {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV}
    {g : d.G} (hg : d.nPart g ∈ (d.incl '' (flagStab FW : Set (GSpin d.QW))) * (d.N : Set _) *
      (flagStab FV : Set (GSpin d.QV))) :
    g ∈ (d.H : Set d.G) * (d.whittB FW FV : Set d.G) := by
  obtain ⟨_, ⟨_, ⟨q, hq, rfl⟩, n, hn, rfl⟩, p, hp, he⟩ := hg
  set a := d.fst g * q
  refine ⟨d.pair (a, d.incl a * n), ?_, d.pair (q⁻¹, p), ?_, ?_⟩
  · show d.nPart _ ∈ d.N
    rw [nPart, fst_pair, snd_pair, inv_mul_cancel_left]
    exact hn
  · exact ⟨show q⁻¹ ∈ flagStab FW from (flagStab FW).inv_mem hq, show p ∈ flagStab FV from hp⟩
  · refine d.G_ext ?_ ?_
    · rw [map_mul, fst_pair, fst_pair]
      simp [a]
    · rw [map_mul, snd_pair, snd_pair]
      have : d.snd g = d.incl (d.fst g) * d.nPart g := by rw [nPart, mul_inv_cancel_left]
      rw [this, ← he]
      simp only [a, map_mul]
      group

section Open

variable {d} {n l : ℕ} {b : Module.Basis (Fin n) F d.V0}
  (hb : IsOrthoBasis d.Q0 b) (hf : WeakCartan.IsFrame d.Q0 b (d.Q0 d.z00) l)
  (h0 : ∀ h, b ⟨0, h⟩ = d.z00)

/-- **`P̄_W N P̄_V` is a neighbourhood of `1` in `GSpin(V)`** for the explicit flags (equivalently,
`H·P̄_min` is open in `G`; Thesis Prop. 8.1.1(i), (8.1.4) and its consequence (8.1.5) for
`P̄_min = P̄₀ T N̄`). The thesis shows `H₀ ∩ P̄₀ = GSpin(W_an)` (8.1.4), deduces that `H₀ P̄₀` is
Zariski open by a dimension count, and then (8.1.5). A direct proof: for `x ∈ GSpin(V)` near `1`, solve
`x · F_V = q n · F_V` (`q ∈ P̄_W`, `n ∈ N`) for the flag `F_V` vector by vector, alternating
between the flag of `V` and that of `W` as in the frame induction; each step divides by a pairing
which is nonzero at `x = 1`, and Witt's extension theorem produces `q` and `n`. -/
theorem flagStab_mul_N_mul_flagStab_mem_nhds :
    (d.incl '' (flagStab (flagW hb hf h0) : Set (GSpin d.QW))) * (d.N : Set _) *
      (flagStab (flagV hb hf h0) : Set (GSpin d.QV)) ∈ 𝓝 (1 : GSpin d.QV) := by
  sorry

/-- **`H·P̄_min` is open in `G(F)`** for the explicit good minimal parabolic (Thesis Prop.
8.1.1(i)). -/
theorem isOpen_H_mul_whittB :
    IsOpen ((d.H : Set d.G) * (d.whittB (flagW hb hf h0) (flagV hb hf h0) : Set d.G)) := by
  refine isOpen_subgroup_mul_of_mem_nhds_one _ _ ?_
  have hc : ContinuousAt d.nPart 1 := d.continuous_nPart_GSpin.continuousAt
  have h1 : d.nPart 1 = 1 := by simp [nPart]
  have hpre := hc.preimage_mem_nhds (h1 ▸ flagStab_mul_N_mul_flagStab_mem_nhds hb hf h0)
  exact Filter.mem_of_superset hpre fun g hg => d.mem_H_mul_whittB_of_nPart hg

end Open

end GGPData

end GSpinGGP
