/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.WeakCartan

/-!
# The cone `A₀⁺ A(F)` lies in the split torus of two frames; Thesis Prop. 8.4.1(iii)

The weak Cartan data of `H(F)\G(F)/A_G(F)` (`GGPData.weakCartanData`,
`TraceFormula/WeakCartan.lean`) take the polynomial growth of the cone `A_G A₀⁺ A(F)`
(`GGPData.cone`) modulo `A_G` (BP (6.7.12)) as hypotheses. `TraceFormula/AMinGrowth.lean`
proves that growth for every subset of `A_G · frameTorus`,
the preimage under `P̄` of the split tori of two hyperbolic frames of `V`. This file shows that the
cone is such a subset, for the frames attached to the frame `b` of `V₀` (Thesis §8.1, §8.3):

* for `SO(W)`, acting on `V` by `g ↦ g ⊕ 1`: the pairs `ι₀(w_{2i-1} ± w_{2i})` of level `1`
  (`pairE hf 1`, `pairF hf 1` pushed along `ι₀ : V₀ → V`);
* for `SO(V)`: the joint frame `z_{-r}, …, z_{-1}, ι₀(u₁), …` of `GoodParabolic.lean`
  (`eV`, `fV`, `isHypFrame_V`), whose torus contains both the split torus `A` of the Levi
  (`torusZ`) and `SO(V₀)`'s torus `multiTorus … 0` extended by `1` (`extV0`).

With this, the growth hypotheses of `GGPData.prop_6_7_1_iii_of_growth` are discharged, which proves
**Thesis Prop. 8.4.1(iii)** (`GGPData.prop_6_7_1_iii`). Its proof now depends on the weak Cartan
decomposition at the level of `SO` (`GGPData.exists_weakCartan_SO`, still a `sorry`). The
consumers `distribJ_convergent` and `distribJ_add` (Thesis §10.1) are stated here as well, since
this file comes after `Analytic.lean`.

## Main results

* `GGPData.isHypFrame_iota0`, `GGPData.extV0_mem_hypTorus`: frames of `V₀` and their tori pushed to
  `V` along `ι₀`, `g ↦ g ⊕ 1`.
* `GGPData.extZ_eq_extV0`: `g ⊕ 1` on `V = W ⊕ Z` is `(g ⊕ 1 on V₀) ⊕ 1`.
* `GGPData.torusZ_mem_hypTorus_V`, `GGPData.extV0_mem_hypTorus_V`: the two factors of the
  `V`-component of the cone lie in the torus of the joint frame.
* `GGPData.cone_subset_frameTorus`, `GGPData.exists_growth_cone`: the cone lies in `frameTorus`,
  and its polynomial growth modulo `A_G` in the shape of `WeakCartanData.growth`.
* `GGPData.prop_6_7_1_iii`, `GGPData.distribJ_convergent`, `GGPData.distribJ_add`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Module QuadraticMap MeasureTheory Topology Filter
open scoped Pointwise

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

open WeakCartan

/-! ## 1. Frames of `V₀` pushed to `V` -/

/-- `polar(π₀ v, x) = polar(v, ι₀ x)`: `v − ι₀(π₀ v)` is orthogonal to `ι₀(V₀)`. -/
theorem polar_pi0 (v : d.V) (x : d.V0) : polar d.Q0 (d.pi0 v) x = polar d.QV v (d.iota0 x) := by
  have hu : d.pi0 (v - d.iota0 (d.pi0 v)) = 0 := by rw [map_sub, pi0_iota0, sub_self]
  have h := d.polar_iota0_of_pi0_eq_zero x hu
  rw [← d.polar_iota0]
  conv_rhs => rw [← add_sub_cancel (d.iota0 (d.pi0 v)) v]
  rw [polar_add_left, polar_comm _ (v - _), h, add_zero]

variable {N : ℕ} {W' : Submodule F d.V0} {e f : Fin N → d.V0}

/-- A hyperbolic frame of `V₀` is one of `V` along `ι₀`. -/
theorem isHypFrame_iota0 (hF : IsHypFrame d.Q0 W' e f) :
    IsHypFrame d.QV (orthFrame d.QV (d.iota0 ∘ e) (d.iota0 ∘ f)) (d.iota0 ∘ e) (d.iota0 ∘ f) :=
  isHypFrame_orthFrame
    (fun i j => by simpa only [Function.comp_apply, d.polar_iota0] using hF.polar_ee i j)
    (fun i j => by simpa only [Function.comp_apply, d.polar_iota0] using hF.polar_ff i j)
    (fun i j => by simpa only [Function.comp_apply, d.polar_iota0] using hF.polar_ef i j)

/-- `π₀` maps the complement of `ι₀(e, f)` in `V` into the complement `W'` of `(e, f)` in `V₀`. -/
theorem pi0_mem_of_mem_orthFrame (hF : IsHypFrame d.Q0 W' e f) {v : d.V}
    (hv : v ∈ orthFrame d.QV (d.iota0 ∘ e) (d.iota0 ∘ f)) : d.pi0 v ∈ W' :=
  (hF.mem_iff _).2 fun i => ⟨by rw [polar_pi0]; exact (hv i).1, by rw [polar_pi0]; exact (hv i).2⟩

/-- `g ⊕ 1` fixes every `v` with `π₀ v` fixed by `g`. -/
theorem extV0_apply_of_fixed {g : d.V0 ≃ₗ[F] d.V0} {v : d.V} (hv : g (d.pi0 v) = d.pi0 v) :
    d.extV0 g v = v := by
  rw [extV0_apply, hv, sub_self, map_zero, add_zero]

/-- **`g ⊕ 1` lies in the torus of the pushed frame** when `g` lies in the torus of the frame of
`V₀`. -/
theorem extV0_mem_hypTorus (hF : IsHypFrame d.Q0 W' e f) {g : d.V0 ≃ₗ[F] d.V0}
    (hg : g ∈ hypTorus W' e f) :
    d.extV0 g ∈ hypTorus (orthFrame d.QV (d.iota0 ∘ e) (d.iota0 ∘ f)) (d.iota0 ∘ e)
      (d.iota0 ∘ f) := by
  obtain ⟨hW, t, ht⟩ := hg
  refine ⟨fun v hv => d.extV0_apply_of_fixed (hW _ (d.pi0_mem_of_mem_orthFrame hF hv)), t,
    fun i => ⟨?_, ?_⟩⟩
  · simp only [Function.comp_apply, extV0_iota0, (ht i).1, map_smul]
  · simp only [Function.comp_apply, extV0_iota0, (ht i).2, map_smul]

/-- `g ⊕ 1` on `V = W ⊕ Z` (`extZ`) is `(g ⊕ 1 on V₀) ⊕ 1` (`extV0 ∘ base.extZ`). -/
theorem extZ_eq_extV0 (g : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F)) :
    d.extZ g = d.extV0 (d.base.extZ g) := by
  refine LinearEquiv.ext fun v => ?_
  rw [extV0_apply, ← pi0_extZ, ← map_sub]
  have h : d.extZ g v - v = d.iota0 (d.pi0 (d.extZ g v - v)) := by
    refine Prod.ext ?_ ?_
    · simp [iota0_apply, pi0, extZ_apply]
    · simp only [Prod.snd_sub, extZ_coord, sub_self, iota0_apply]
      simp [pi0, extZ_apply]
  rw [← h, add_sub_cancel]

/-! ## 2. The torus of the joint frame of `V` -/

section JointFrame

variable {d} {n l : ℕ} {b : Module.Basis (Fin n) F d.V0} (hb : IsOrthoBasis d.Q0 b)
  (hf : IsFrame d.Q0 b (d.Q0 d.z00) l) (h0 : ∀ h, b ⟨0, h⟩ = d.z00)

/-- The `ι₀(V₀)`-part of the joint frame: the complement of the joint frame lies in that of
`ι₀(pairE hf 0, pairF hf 0)`. -/
theorem mem_orthFrame_iota0_of_mem_V {v : d.V} (hv : v ∈ orthFrame d.QV (eV hf) (fV hf)) :
    v ∈ orthFrame d.QV (d.iota0 ∘ pairE hf 0) (d.iota0 ∘ pairF hf 0) := fun i => by
  have := hv (Fin.natAdd d.r i)
  simpa only [eV, fV, Fin.append_right] using this

/-- `a(τ) z_j = c • z_j` with `c` the torus coefficient at `z_j`. -/
theorem torusZ_zV (τ : Fin d.r → Fˣ) {j : ℤ} (hj : |j| ≤ d.r) :
    d.torusZ τ (d.zV j) =
      (d.torusCoeff τ ⟨(j + d.r).toNat, by have := abs_le.mp hj; omega⟩ : F) • d.zV j := by
  rw [torusZ_apply, zV]
  refine Prod.ext (by simp) (funext fun i => ?_)
  simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, zvec]
  by_cases hi : ((i : ℕ) : ℤ) - d.r = j
  · have : i = ⟨(j + d.r).toNat, by have := abs_le.mp hj; omega⟩ := Fin.ext (by simp; omega)
    simp [this]
  · simp only [hi, ↓reduceIte, mul_zero]

/-- `a(τ) z_{-(r-k)} = c_k z_{-(r-k)}` with `c_k` the torus coefficient at that coordinate. -/
theorem torusZ_zb (τ : Fin d.r → Fˣ) (k : Fin d.r) :
    d.torusZ τ (zb (d := d) k) = (d.torusCoeff τ ⟨k, by omega⟩ : F) • zb (d := d) k := by
  rw [zb, d.torusZ_zV τ (abs_neg_le k)]
  congr 3
  ext; simp

/-- `a(τ)` acts on the dual vector `zbD k` by the inverse coefficient. -/
theorem torusZ_zbD (τ : Fin d.r → Fˣ) (k : Fin d.r) :
    d.torusZ τ (zbD (d := d) k) =
      (((d.torusCoeff τ ⟨k, by omega⟩)⁻¹ : Fˣ) : F) • zbD (d := d) k := by
  rw [zbD, map_smul, d.torusZ_zV τ (abs_pos_le k), smul_comm]
  congr 1
  have h := d.torusCoeff_mul_rev τ ⟨k, by omega⟩
  refine (congrArg (fun i => ((d.torusCoeff τ i : Fˣ) : F))
    (Fin.ext (b := (⟨k, by omega⟩ : Fin (2 * d.r + 1)).rev) ?_)).trans ?_
  · simp only [Fin.val_rev]; omega
  · rw [eq_inv_of_mul_eq_one_right h]

/-- The complement of the joint frame has vanishing `z_{±k}`-coordinates (`k ≥ 1`). -/
theorem coord_eq_zero_of_mem_V {v : d.V} (hv : v ∈ orthFrame d.QV (eV hf) (fV hf))
    (i : Fin (2 * d.r + 1)) (hi : (i : ℕ) ≠ d.r) : v.2 i = 0 := by
  have hν : (d.ν : F) ≠ 0 := d.ν.ne_zero
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  rcases Nat.lt_or_gt_of_ne hi with hlt | hgt
  · -- `i < r`: pair with `z_{r - i}` (in `zbD`)
    set k : Fin d.r := ⟨i, hlt⟩
    have h := (hv (Fin.castAdd _ k)).2
    simp only [fV, Fin.append_left, zbD, polar_smul_right, smul_eq_mul] at h
    have h' : polar d.QV v (d.zV ((d.r : ℤ) - (k : ℕ))) = 0 :=
      (mul_eq_zero.1 h).resolve_left (inv_ne_zero (mul_ne_zero h2 hν))
    rw [polar_eq_two_mul_bform, bform_zV_eq _ _ (abs_pos_le k)] at h'
    have h'' := (mul_eq_zero.1 ((mul_eq_zero.1 h').resolve_left h2)).resolve_left hν
    convert h'' using 2
    ext; simp [k]
  · -- `i > r`: pair with `z_{-(i - r)}` (in `zb`)
    set k : Fin d.r := ⟨2 * d.r - i, by have := i.2; omega⟩
    have h := (hv (Fin.castAdd _ k)).1
    simp only [eV, Fin.append_left, zb] at h
    rw [polar_eq_two_mul_bform, bform_zV_eq _ _ (abs_neg_le k)] at h
    have h'' := (mul_eq_zero.1 ((mul_eq_zero.1 h).resolve_left h2)).resolve_left hν
    convert h'' using 2
    ext; simp only [k]; have := i.2; omega

include hb h0 in
/-- **`a(τ)` lies in the torus of the joint frame of `V`.** -/
theorem torusZ_mem_hypTorus_V (τ : Fin d.r → Fˣ) :
    d.torusZ τ ∈ hypTorus (orthFrame d.QV (eV hf) (fV hf)) (eV hf) (fV hf) := by
  refine ⟨fun v hv => ?_, Fin.append (fun k : Fin d.r => d.torusCoeff τ ⟨k, by omega⟩)
    (fun _ => 1), fun i => ?_⟩
  · rw [torusZ_apply]
    refine Prod.ext rfl (funext fun i => ?_)
    change (d.torusCoeff τ i : F) * v.2 i = v.2 i
    by_cases hi : (i : ℕ) = d.r
    · have : i = ⟨d.r, by omega⟩ := Fin.ext hi
      rw [this, torusCoeff_r, Units.val_one, one_mul]
    · rw [coord_eq_zero_of_mem_V hf hv i hi, mul_zero]
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simp only [eV, fV, Fin.append_left]
      exact ⟨d.torusZ_zb τ k, d.torusZ_zbD τ k⟩
    · simp only [eV, fV, Fin.append_right, Function.comp_apply, torusZ_iota0, Units.val_one,
        one_smul, inv_one, and_self]

include hb h0 in
/-- **`g ⊕ 1` lies in the torus of the joint frame of `V`** for `g` in the torus of the level-`0`
frame of `V₀` (e.g. `g = (multiTorus hb hf 0 t)⁻¹`). -/
theorem extV0_mem_hypTorus_V {g : d.V0 ≃ₗ[F] d.V0}
    (hg : g ∈ hypTorus (pairCompl b l 0) (pairE hf 0) (pairF hf 0)) :
    d.extV0 g ∈ hypTorus (orthFrame d.QV (eV hf) (fV hf)) (eV hf) (fV hf) := by
  have H := isHypFrame_pair hb hf 0
  obtain ⟨hW, t, ht⟩ := hg
  have hz : ∀ {j : ℤ}, j ≠ 0 → d.extV0 g (d.zV j) = d.zV j := fun hj =>
    d.extV0_apply_of_fixed (by rw [d.pi0_zV hj, map_zero])
  refine ⟨fun v hv => d.extV0_apply_of_fixed (hW _ (d.pi0_mem_of_mem_orthFrame H
    (mem_orthFrame_iota0_of_mem_V hf hv))), Fin.append (fun _ => 1) t, fun i => ?_⟩
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simp only [eV, fV, Fin.append_left, zb, zbD, map_smul, Units.val_one, inv_one, one_smul]
    exact ⟨hz (by have := k.2; omega), by rw [hz (by have := k.2; omega)]⟩
  · simp only [eV, fV, Fin.append_right, Function.comp_apply, extV0_iota0, (ht k).1, (ht k).2,
      map_smul, and_self]

end JointFrame

/-! ## 3. The cone lies in the torus of the two frames -/

section Cone

variable {d} {n l : ℕ} {b : Module.Basis (Fin n) F d.V0} (hb : IsOrthoBasis d.Q0 b)
  (hf : IsFrame d.Q0 b (d.Q0 d.z00) l) (h0 : ∀ h, b ⟨0, h⟩ = d.z00)

include hb h0 in
/-- **The cone `A_G A₀⁺ A(F)` lies in the split torus of the two frames** `ι₀(pairE hf 1)` (for
`SO(W)`) and `eV hf` (for `SO(V)`). -/
theorem cone_subset_frameTorus :
    d.cone hb hf ⊆ d.frameTorus (orthFrame d.QV (d.iota0 ∘ pairE hf 1) (d.iota0 ∘ pairF hf 1))
      (orthFrame d.QV (eV hf) (fV hf)) (d.iota0 ∘ pairE hf 1) (d.iota0 ∘ pairF hf 1)
      (eV hf) (fV hf) := by
  rintro x ⟨s, t, τ, -, -, hW, hV⟩
  refine ⟨?_, ?_⟩
  · change d.PbarW x ∈ hypTorus _ _ _
    rw [PbarW_apply, extZ_eq_extV0, hW]
    exact d.extV0_mem_hypTorus (isHypFrame_pair hb hf 1)
      ((hypTorus _ _ _).inv_mem (multiTorus_mem_hypTorus hb hf 1 s))
  · change d.PbarV x ∈ hypTorus _ _ _
    rw [PbarV_apply, hV]
    exact mul_mem (torusZ_mem_hypTorus_V hb hf h0 τ) (extV0_mem_hypTorus_V hb hf h0
      ((hypTorus _ _ _).inv_mem (multiTorus_mem_hypTorus hb hf 0 t)))

include hb h0 in
/-- **BP (6.7.12) for the cone** (polynomial growth of `A_G A₀⁺ A(F)` modulo `A_G`), in the shape
of the hypotheses of `weakCartanData` and `prop_6_7_1_iii_of_growth`. -/
theorem exists_growth_cone :
    ∃ CS : Set d.G, IsCompact CS ∧ ∃ (M : ℝ) (N : ℕ), ∀ R : ℝ, 1 ≤ R →
      ∃ t : Finset d.G, (t.card : ℝ) ≤ M * (1 + R) ^ N ∧
        d.mkHG '' {s ∈ d.cone hb hf | d.logNormModAG s < R} ⊆
          ⋃ j ∈ t, d.mkHG '' ((j * ·) '' CS) := by
  obtain ⟨CS, hCS, M, N, h⟩ := d.exists_growth_mkHG_frameTorus
    (d.isHypFrame_iota0 (isHypFrame_pair hb hf 1)) (isHypFrame_V hb hf h0)
  refine ⟨CS, hCS, M, N, h _ fun x hx => ⟨1, one_mem _, x, cone_subset_frameTorus hb hf h0 hx,
    one_mul x⟩⟩

end Cone

/-! ## 4. Thesis Prop. 8.4.1(iii) and the convergence of `J` -/

/-- **Thesis Prop 8.4.1(iii)** (adapted from BP Prop 6.7.1(iii)): there is `d > 0` with
`∫_{H(F)\G(F)/A_G(F)} Ξ^{H\G}(x)² σ_{H\G}(x)^{-d} dx < ∞`.  Stated for every compact `C₀`
with nonempty interior defining `Ξ^{H\G} = Ξ^{H\G}_{C₀}` (`xiHG`); the thesis fixes one such
`C₀`, and different choices give equivalent functions (Thesis §8.4).  Proof: BP's argument
(`prop_6_7_1_iii_of_growth`) for the explicit good pair of a maximal frame `z₀ = w₀, w₁, …` of
`V₀`, with the polynomial growth of the cone from `exists_growth_cone`. -/
theorem prop_6_7_1_iii (C₀ : Set ↥d.G) (hC₀ : IsCompact C₀) (hC₀' : (interior C₀).Nonempty) :
    ∃ d₀ : ℝ, 0 < d₀ ∧
      Integrable (fun q : d.HGQuot => d.xiHG C₀ q ^ 2 * d.logNormHG q ^ (-d₀)) d.weilMeasureHG := by
  obtain ⟨n, l, b, hb, hf, h0⟩ := WeakCartan.exists_isFrame
    ((isNondeg_iff_nondegenerate _).1 d.nondeg_Q0) (v₀ := d.z00)
    (by rw [d.Q0_z00]; exact d.ν.ne_zero)
  have h0' : ∀ h, b ⟨0, h⟩ = d.z00 := fun _ => h0
  have hb0 : ∀ i : Fin n, (i : ℕ) = 0 → (b i).1 = 0 := fun i hi => by
    rw [show i = ⟨0, (Nat.zero_le l).trans_lt hf.lt⟩ from Fin.ext hi, h0]; rfl
  obtain ⟨CS, hCS, M, N, hg⟩ := exists_growth_cone hb hf h0'
  exact d.prop_6_7_1_iii_of_growth hb hf hb0 CS hCS M N hg C₀ hC₀ hC₀'

variable (χ : CentralCharOn d) (ψ : NontrivialAddChar F)

/-- **`J(f)` converges** for `f ∈ ScuspTestFn d χ` (Thesis §10.1): `f` is Schwartz
(`scuspTestFn_subset_scuspSchwartz`), so Thm 10.1.1(ii) (`kernelK_bound_scusp`) bounds
`|K(f,x)|` by a multiple of `Ξ^{H\G}(x)² σ_{H\G}(x)^{-d}` for every `d > 0`, which is integrable
for `d` large by Thesis Prop 8.4.1(iii) (`prop_6_7_1_iii`); `K(f,·)` is continuous on
`H(F)\G(F)/A_G(F)` (`continuous_kernelK_repHG`). -/
theorem distribJ_convergent (f : ↥d.G → ℂ) (hf : f ∈ ScuspTestFn d χ) :
    Integrable (fun q : d.HGQuot => kernelK d ψ f (d.repHG q)) d.weilMeasureHG := by
  obtain ⟨IW⟩ := d.exists_iwasawaDatum
  have hf' := d.scuspTestFn_subset_scuspSchwartz χ IW hf
  obtain ⟨⟨K', hK'o, hK'c, hbi⟩, hchi, -⟩ := hf'.1
  have hC₀' : (interior (K' : Set ↥d.G)).Nonempty :=
    ⟨1, mem_interior_iff_mem_nhds.2 (hK'o.mem_nhds K'.one_mem)⟩
  obtain ⟨d₀, hd₀, hint⟩ := d.prop_6_7_1_iii (K' : Set ↥d.G) hK'c hC₀'
  obtain ⟨C, n, hb⟩ := d.kernelK_bound_scusp χ ψ IW (K' : Set ↥d.G) hK'c hC₀' d₀ hd₀ K' hK'o hK'c
  refine (hint.const_mul (C * d.schwartzSeminorm IW n f)).mono'
    (d.continuous_kernelK_repHG χ ψ f hchi hK'o hbi).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  have := hb f hf' hbi (d.repHG q)
  rw [d.mkHG_repHG] at this
  simpa only [mul_assoc] using this

/-- `J` is additive on `ScuspTestFn d χ` (Thesis §10.1: `J` is a linear form). -/
theorem distribJ_add (f g : ↥d.G → ℂ) (hf : f ∈ ScuspTestFn d χ) (hg : g ∈ ScuspTestFn d χ) :
    distribJ d ψ (f + g) = distribJ d ψ f + distribJ d ψ g := by
  have e : ∀ q : d.HGQuot, kernelK d ψ (f + g) (d.repHG q) =
      kernelK d ψ f (d.repHG q) + kernelK d ψ g (d.repHG q) :=
    fun q => d.kernelK_add χ ψ f g hf hg _
  unfold distribJ
  change ∫ q, kernelK d ψ (f + g) (d.repHG q) ∂d.weilMeasureHG =
    ∫ q, kernelK d ψ f (d.repHG q) ∂d.weilMeasureHG +
      ∫ q, kernelK d ψ g (d.repHG q) ∂d.weilMeasureHG
  simp_rw [e]
  exact integral_add (d.distribJ_convergent χ ψ f hf) (d.distribJ_convergent χ ψ g hg)

end GGPData

end GSpinGGP
