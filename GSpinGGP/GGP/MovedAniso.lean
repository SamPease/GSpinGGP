/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.Descent
import GSpinGGP.Foundations.QuadraticForms
import GSpinGGP.TraceFormula.SpinorNorm

/-!
# The moved space of an element of `GSpin`

For `x ∈ GSpin(V)` with `V = V'_x ⊕ V''_x`, `V''_x = (V'_x)^⊥` (`V'_x = ker(P(x) − 1)`):
* `finrank_orthogonal_fixedSub_ne_one`: `V''_x` is not a line (on a line `P(x)` would be the
  reflection in it, of determinant `−1`, while `det P(x) = 1`, `det_specP`).
-/

noncomputable section

open Module

namespace GSpinGGP

variable {K V : Type*} [Field K] [CharZero K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- **`V''_x` is not a line**: for `x ∈ GSpin(V)` with `V = V'_x ⊕ (V'_x)^⊥`. -/
theorem finrank_orthogonal_fixedSub_ne_one {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (x : GSpin Q) (hc : IsCompl (fixedSub x) ((bform Q).orthogonal (fixedSub x))) :
    finrank K ↥((bform Q).orthogonal (fixedSub x)) ≠ 1 := by
  intro h1
  set U := (bform Q).orthogonal (fixedSub x) with hUdef
  set P : Module.End K V := (specP Q x : Module.End K V) with hPdef
  obtain ⟨⟨u, huU⟩, hu0, hspan⟩ := finrank_eq_one_iff'.1 h1
  have hu0' : u ≠ 0 := fun h => hu0 (Subtype.ext h)
  have hmemU : ∀ v ∈ U, ∃ c : K, c • u = v := fun v hv => by
    obtain ⟨c, hc⟩ := hspan ⟨v, hv⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  -- `bform(u, ·) = 0` on `V'_x`
  have huW : ∀ w ∈ fixedSub x, bform Q u w = 0 := fun w hw => by
    rw [QuadraticMap.associated_isSymm]; exact huU w hw
  -- `Q u ≠ 0`
  have hQu : Q u ≠ 0 := by
    intro hQ0
    apply hu0'
    refine hQ.1 u fun v => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
    obtain ⟨c, rfl⟩ := hmemU b hb
    rw [map_add, map_smul, huW a ha, zero_add, smul_eq_mul,
      QuadraticMap.associated_eq_self_apply, hQ0, mul_zero]
  -- `P u = -u`
  obtain ⟨μ, hμ⟩ := hmemU _ (specP_mem_orthogonal_fixedSub x huU)
  have hμ1 : μ ≠ 1 := by
    rintro rfl
    have : u ∈ fixedSub x ⊓ U := ⟨(mem_fixedSub_iff x u).2 (by rw [← hμ, one_smul]), huU⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at this
    exact hu0' this
  have hμsq : μ * μ = 1 := by
    have h : Q (μ • u) = Q u := by rw [hμ]; exact (specPIso x).map_app u
    rw [QuadraticMap.map_smul, smul_eq_mul] at h
    exact mul_right_cancel₀ hQu (h.trans (one_mul _).symm)
  have hμm : μ = -1 := by
    have : (μ - 1) * (μ + 1) = 0 := by linear_combination hμsq
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hμ1
    · linear_combination h
  -- `P = s_u`
  have hPs : P = quadReflection Q u := by
    ext v
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
    obtain ⟨c, rfl⟩ := hmemU b hb
    have hPa : P a = a := (mem_fixedSub_iff x a).1 ha
    have hpa : QuadraticMap.polar Q u a = 0 := by rw [polar_eq_two_mul_bform, huW a ha, mul_zero]
    have hpu : QuadraticMap.polar Q u u = 2 * Q u := by
      rw [polar_eq_two_mul_bform, QuadraticMap.associated_eq_self_apply]
    have hPu : P u = μ • u := hμ.symm
    rw [map_add, map_smul, hPa, map_add, map_smul, quadReflection_apply, quadReflection_apply, hpa,
      hpu, hPu, hμm]
    have h2 : (Q u)⁻¹ * (2 * Q u) = 2 := by field_simp
    simp only [smul_smul, h2, zero_smul, smul_zero, sub_zero]
    module
  have hdet := det_specP x
  rw [← hPdef, hPs, det_quadReflection hQu] at hdet
  norm_num at hdet

omit [Invertible (2 : K)] [FiniteDimensional K V] in
/-- **The split torus of a hyperbolic pair as a product of two reflections**: for a hyperbolic pair
`f, f'` (`q(f) = q(f') = 0`, `polar(f, f') = 1`) and `s ≠ 0`, `s_{f+f'} s_{f+s f'}` maps `f ↦ s f`,
`f' ↦ s⁻¹ f'`, and fixes every vector polar-orthogonal to `f` and `f'`. -/
theorem hypPair_reflections {Q : QuadraticForm K V} {f f' : V} (hf : Q f = 0) (hf' : Q f' = 0)
    (hp : QuadraticMap.polar Q f f' = 1) {s : K} (hs : s ≠ 0) :
    Q (f + f') ≠ 0 ∧ Q (f + s • f') ≠ 0 ∧
      (quadReflection Q (f + f') * quadReflection Q (f + s • f')) f = s • f ∧
      (quadReflection Q (f + f') * quadReflection Q (f + s • f')) f' = s⁻¹ • f' ∧
      ∀ v, QuadraticMap.polar Q f v = 0 → QuadraticMap.polar Q f' v = 0 →
        (quadReflection Q (f + f') * quadReflection Q (f + s • f')) v = v := by
  have hff : QuadraticMap.polar Q f f = 0 := by rw [QuadraticMap.polar_self, hf, smul_zero]
  have hf'f' : QuadraticMap.polar Q f' f' = 0 := by rw [QuadraticMap.polar_self, hf', smul_zero]
  have hf'f : QuadraticMap.polar Q f' f = 1 := by rw [QuadraticMap.polar_comm, hp]
  have hQa : Q (f + f') = 1 := by rw [QuadraticMap.map_add Q f f', hf, hf', hp]; ring
  have hQb : Q (f + s • f') = s := by
    rw [QuadraticMap.map_add Q f (s • f'), QuadraticMap.map_smul, QuadraticMap.polar_smul_right, hf, hf', hp]
    simp
  refine ⟨by rw [hQa]; exact one_ne_zero, by rw [hQb]; exact hs, ?_, ?_, fun v hv hv' => ?_⟩
  · simp only [Module.End.mul_apply, quadReflection_apply, hQa, hQb, QuadraticMap.polar_add_left,
      QuadraticMap.polar_add_right, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_sub_right, hff, hf'f', hp, hf'f, smul_eq_mul]
    match_scalars <;> field_simp <;> ring
  · simp only [Module.End.mul_apply, quadReflection_apply, hQa, hQb, QuadraticMap.polar_add_left,
      QuadraticMap.polar_add_right, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_sub_right, hff, hf'f', hp, hf'f, smul_eq_mul]
    match_scalars <;> field_simp <;> ring
  · have hvf : QuadraticMap.polar Q v f = 0 := by rw [QuadraticMap.polar_comm, hv]
    have hvf' : QuadraticMap.polar Q v f' = 0 := by rw [QuadraticMap.polar_comm, hv']
    simp only [Module.End.mul_apply, quadReflection_apply, QuadraticMap.polar_add_left,
      QuadraticMap.polar_smul_left, hv, hv', smul_eq_mul, mul_zero, add_zero, zero_smul,
      smul_zero, sub_zero]

omit [CharZero K] [Invertible (2 : K)] in
/-- In a plane `U` containing a hyperbolic pair `f, f'`, every `u ∈ U` is
`polar(f', u) f + polar(f, u) f'`. -/
theorem eq_of_mem_hypPlane {Q : QuadraticForm K V} {U : Submodule K V} (h2 : finrank K U = 2)
    {f f' : V} (hfU : f ∈ U) (hf'U : f' ∈ U) (hf : Q f = 0) (hf' : Q f' = 0)
    (hp : QuadraticMap.polar Q f f' = 1) {u : V} (hu : u ∈ U) :
    u = QuadraticMap.polar Q f' u • f + QuadraticMap.polar Q f u • f' := by
  have hff : QuadraticMap.polar Q f f = 0 := by rw [QuadraticMap.polar_self, hf, smul_zero]
  have hf'f' : QuadraticMap.polar Q f' f' = 0 := by rw [QuadraticMap.polar_self, hf', smul_zero]
  have hf'f : QuadraticMap.polar Q f' f = 1 := by rw [QuadraticMap.polar_comm, hp]
  -- `f, f'` are independent, hence span `U`
  have hli : LinearIndependent K ![f, f'] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg (QuadraticMap.polar Q f') hab
    have h2 := congrArg (QuadraticMap.polar Q f) hab
    simp only [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, hf'f, hf'f', hff, hp,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, QuadraticMap.polar_zero_right] at h1 h2
    exact ⟨h1, h2⟩
  have hspan : Submodule.span K (Set.range ![f, f']) = U := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i <;> simp [hfU, hf'U]
    · rw [finrank_span_eq_card hli, h2]; rfl
  rw [← hspan] at hu
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hu
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, hf'f, hf'f', hff, hp,
    smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]

/-- **`P(x)` is diagonal on a hyperbolic pair of `V''_x`**: if `V''_x = (V'_x)^⊥` is a plane with
hyperbolic pair `f, f'`, then `P(x) f = λ f`, `P(x) f' = λ⁻¹ f'` (swapping the two isotropic lines
would make `P(x)` the reflection in `f − μ f'`, of determinant `−1`). -/
theorem exists_eigen_hypPair {Q : QuadraticForm K V} (x : GSpin Q)
    (hc : IsCompl (fixedSub x) ((bform Q).orthogonal (fixedSub x)))
    (h2 : finrank K ↥((bform Q).orthogonal (fixedSub x)) = 2) {f f' : V}
    (hfU : f ∈ (bform Q).orthogonal (fixedSub x)) (hf'U : f' ∈ (bform Q).orthogonal (fixedSub x))
    (hf : Q f = 0) (hf' : Q f' = 0) (hp : QuadraticMap.polar Q f f' = 1) :
    ∃ μ : K, μ ≠ 0 ∧ (specP Q x : Module.End K V) f = μ • f ∧
      (specP Q x : Module.End K V) f' = μ⁻¹ • f' := by
  set U := (bform Q).orthogonal (fixedSub x) with hUdef
  set P : Module.End K V := (specP Q x : Module.End K V) with hPdef
  have hdec := fun {u : V} (hu : u ∈ U) => eq_of_mem_hypPlane h2 hfU hf'U hf hf' hp hu
  have hff : QuadraticMap.polar Q f f = 0 := by rw [QuadraticMap.polar_self, hf, smul_zero]
  have hf'f' : QuadraticMap.polar Q f' f' = 0 := by rw [QuadraticMap.polar_self, hf', smul_zero]
  have hf'f : QuadraticMap.polar Q f' f = 1 := by rw [QuadraticMap.polar_comm, hp]
  have hQP : ∀ v, Q (P v) = Q v := fun v => (specPIso x).map_app v
  have hpolP : ∀ v w, QuadraticMap.polar Q (P v) (P w) = QuadraticMap.polar Q v w :=
    fun v w => polar_isometry (specPIso x).toIsometry v w
  -- `Q(a f + b f') = a b`
  have hQab : ∀ a b : K, Q (a • f + b • f') = a * b := fun a b => by
    rw [QuadraticMap.map_add Q (a • f) (b • f'), QuadraticMap.map_smul, QuadraticMap.map_smul,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hf, hf', hp]
    simp
  set α := QuadraticMap.polar Q f' (P f)
  set β := QuadraticMap.polar Q f (P f)
  set γ := QuadraticMap.polar Q f' (P f')
  set δ := QuadraticMap.polar Q f (P f')
  have hPf : P f = α • f + β • f' := hdec (specP_mem_orthogonal_fixedSub x hfU)
  have hPf' : P f' = γ • f + δ • f' := hdec (specP_mem_orthogonal_fixedSub x hf'U)
  have hαβ : α * β = 0 := by rw [← hQab, ← hPf, hQP, hf]
  have hγδ : γ * δ = 0 := by rw [← hQab, ← hPf', hQP, hf']
  have hpol : α * δ + β * γ = 1 := by
    have h := hpolP f f'
    rw [hPf, hPf', hp] at h
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hff, hf'f', hp, hf'f,
      smul_eq_mul] at h
    linear_combination h
  by_cases hβ : β = 0
  · have hαδ : α * δ = 1 := by rw [hβ, zero_mul, add_zero] at hpol; exact hpol
    have hα : α ≠ 0 := left_ne_zero_of_mul_eq_one hαδ
    have hδ : δ ≠ 0 := right_ne_zero_of_mul_eq_one hαδ
    have hγ : γ = 0 := (mul_eq_zero.1 hγδ).resolve_right hδ
    refine ⟨α, hα, by rw [hPf, hβ, zero_smul, add_zero], ?_⟩
    rw [hPf', hγ, zero_smul, zero_add, eq_inv_of_mul_eq_one_right hαδ]
  · exfalso
    have hα : α = 0 := (mul_eq_zero.1 hαβ).resolve_right hβ
    have hβγ : β * γ = 1 := by rw [hα, zero_mul, zero_add] at hpol; exact hpol
    have hδ : δ = 0 := (mul_eq_zero.1 hγδ).resolve_left (right_ne_zero_of_mul_eq_one hβγ)
    have hγ' : γ = β⁻¹ := eq_inv_of_mul_eq_one_right hβγ
    set r := f - β • f' with hrdef
    have hQr : Q r = -β := by
      have : r = (1 : K) • f + (-β) • f' := by rw [hrdef, one_smul, neg_smul, sub_eq_add_neg]
      rw [this, hQab]
      ring
    have hQr0 : Q r ≠ 0 := by rw [hQr]; exact neg_ne_zero.2 hβ
    have hpW : ∀ v ∈ U, ∀ a ∈ fixedSub x, QuadraticMap.polar Q v a = 0 := fun v hv a ha => by
      rw [polar_eq_two_mul_bform, QuadraticMap.associated_isSymm, hv a ha, mul_zero]
    have hPs : P = quadReflection Q r := by
      ext v
      obtain ⟨a, ha, b, hb, rfl⟩ :=
        Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
      have hPa : P a = a := (mem_fixedSub_iff x a).1 ha
      have hra : QuadraticMap.polar Q r a = 0 := by
        rw [hrdef, QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, hpW f hfU a ha,
          hpW f' hf'U a ha, smul_zero, sub_zero]
      obtain ⟨p₁, p₂, rfl⟩ : ∃ p₁ p₂ : K, b = p₁ • f + p₂ • f' := ⟨_, _, hdec hb⟩
      have hsa : quadReflection Q r a = a := by
        rw [quadReflection_apply, hra, zero_smul, smul_zero, sub_zero]
      have hrf : QuadraticMap.polar Q r f = -β := by
        rw [hrdef, QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, hff, hf'f]; simp
      have hrf' : QuadraticMap.polar Q r f' = 1 := by
        rw [hrdef, QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, hp, hf'f']; simp
      have hsf : quadReflection Q r f = β • f' := by
        rw [quadReflection_apply, hrf, hQr, hrdef, smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 hβ),
          one_smul]
        abel
      have hsf' : quadReflection Q r f' = β⁻¹ • f := by
        rw [quadReflection_apply, hrf', hQr, hrdef, one_smul, smul_sub, smul_smul,
          inv_neg, neg_mul, inv_mul_cancel₀ hβ]
        module
      rw [map_add, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, hPa, hsa, hPf,
        hPf', hsf, hsf', hα, hδ, hγ', zero_smul, zero_add, zero_smul, add_zero]
    have hdet := det_specP x
    rw [← hPdef, hPs, det_quadReflection hQr0] at hdet
    norm_num at hdet

section Gamma

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **For `x ∈ Γ(G,H)`, a plane `W''_x` is anisotropic**: otherwise, with a hyperbolic pair `f, f'`
of `W''_x`, the elements `z_s = ι(f+f') ι(f+s f')` (`P(z_s) = s` on `f`, `s⁻¹` on `f'`, `1` on
`W'_x`) commute with `x` up to a scalar `c_s` with `c_s^N = 1` (`N = dim C(W)`, apply `detChar`), so
`z_s^N ∈ T_x(F)` with `P(z_s^N) f = s^N f`; but `t ↦ polar(f', P(t) f)` is continuous on the compact
`T_x(F)/A(F)`, hence bounded. -/
theorem anisotropic_orthogonal_fixedSub_of_isGammaElt (d : GGPData F) (x : ↥(GSpin d.QW))
    (hx : d.IsGammaElt x) (h2 : finrank F ↥((bform d.QW).orthogonal (fixedSub x)) = 2) :
    (d.QW.comp ((bform d.QW).orthogonal (fixedSub x)).subtype).Anisotropic := by
  classical
  set U := (bform d.QW).orthogonal (fixedSub x) with hUdef
  have hc : IsCompl (fixedSub x) U :=
    isCompl_fixedSub_orthogonal d.nondeg x (fixedSub_inf_movedSub_of_isSS x hx.1)
  have hpW : ∀ v ∈ U, ∀ a ∈ fixedSub x, QuadraticMap.polar d.QW v a = 0 := fun v hv a ha => by
    rw [polar_eq_two_mul_bform, QuadraticMap.associated_isSymm, hv a ha, mul_zero]
  -- `U` is nondegenerate
  have hUnd : IsNondeg (d.QW.comp U.subtype) := by
    refine (isNondeg_iff _).2 fun u hu => Subtype.ext ((isNondeg_iff d.QW).1 d.nondeg u fun v => ?_)
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
    have h1 : bform d.QW u a = 0 := by rw [QuadraticMap.associated_isSymm]; exact u.2 a ha
    have h2 : bform d.QW u b = 0 := by rw [← bform_comp_subtype d.QW U u ⟨b, hb⟩]; exact hu ⟨b, hb⟩
    rw [map_add, h1, h2, add_zero]
  intro u hu0
  by_contra hne
  obtain ⟨f'', hf''0, hpol⟩ := exists_hyperbolicPair_of_isotropic hUnd hne hu0
  have hp : QuadraticMap.polar d.QW (u : Fin d.m → F) (f'' : Fin d.m → F) = 1 := by
    rw [← hpol]; rfl
  obtain ⟨μ, hμ0, hPf, hPf'⟩ := exists_eigen_hypPair x hc h2 u.2 f''.2 hu0 hf''0 hp
  set N := finrank F (CliffordAlgebra d.QW) with hNdef
  have hN : 0 < N := Module.finrank_pos
  -- elements of `T_x(F)` acting by `s^N` on `f`
  have key : ∀ s : F, s ≠ 0 → ∃ t ∈ d.torusOf x,
      specP d.QW t (u : Fin d.m → F) = s ^ N • (u : Fin d.m → F) := by
    intro s hs
    obtain ⟨ha, hb, hgf, hgf', hgv⟩ := hypPair_reflections (Q := d.QW) (f := (u : Fin d.m → F))
      (f' := (f'' : Fin d.m → F)) hu0 hf''0 hp hs
    set z := gspinPair d.QW ha hb with hzdef
    have hPz : (specP d.QW z : Module.End F (Fin d.m → F)) =
        quadReflection d.QW ((u : Fin d.m → F) + f'') *
          quadReflection d.QW ((u : Fin d.m → F) + s • (f'' : Fin d.m → F)) :=
      specP_gspinPair d.QW ha hb
    have hPzW : ∀ v ∈ fixedSub x, (specP d.QW z : Module.End F (Fin d.m → F)) v = v :=
      fun v hv => by rw [hPz]; exact hgv v (hpW _ u.2 v hv) (hpW _ f''.2 v hv)
    have hPzf : (specP d.QW z : Module.End F (Fin d.m → F)) u = s • (u : Fin d.m → F) := by
      rw [hPz]; exact hgf
    have hPzf' : (specP d.QW z : Module.End F (Fin d.m → F)) f'' = s⁻¹ • (f'' : Fin d.m → F) := by
      rw [hPz]; exact hgf'
    -- `P(z)` commutes with `P(x)`
    have hcomm : specP d.QW (z * x * z⁻¹ * x⁻¹) = 1 := by
      have hPxz : (specP d.QW z : Module.End F (Fin d.m → F)) * (specP d.QW x : Module.End F _) =
          (specP d.QW x : Module.End F _) * (specP d.QW z : Module.End F _) := by
        refine LinearMap.ext fun v => ?_
        obtain ⟨a, ha', b, hb', rfl⟩ :=
          Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
        obtain ⟨p₁, p₂, rfl⟩ : ∃ p₁ p₂ : F, b = p₁ • (u : Fin d.m → F) + p₂ • (f'' : Fin d.m → F) :=
          ⟨_, _, eq_of_mem_hypPlane h2 u.2 f''.2 hu0 hf''0 hp hb'⟩
        have hPxa : (specP d.QW x : Module.End F (Fin d.m → F)) a = a := (mem_fixedSub_iff x a).1 ha'
        simp only [Module.End.mul_apply, map_add, map_smul, hPxa, hPzW a ha', hPzf, hPzf', hPf,
          hPf', smul_smul, mul_comm]
      have hPxz' : specP d.QW z * specP d.QW x = specP d.QW x * specP d.QW z :=
        LinearEquiv.toLinearMap_injective hPxz
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hPxz']
      group
    -- `z x z⁻¹ = c x` with `c^N = 1`
    obtain ⟨c, hc'⟩ : ∃ c, scalarGSpin d.QW c = z * x * z⁻¹ * x⁻¹ := by
      have hk : z * x * z⁻¹ * x⁻¹ ∈ (specP d.QW).ker := hcomm
      rwa [ker_specP d.nondeg] at hk
    have hcN : c ^ N = 1 := by
      have h := congrArg (detChar d.QW) hc'
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (detChar d.QW z)] at h
      have h1 : detChar d.QW x * detChar d.QW z * (detChar d.QW z)⁻¹ * (detChar d.QW x)⁻¹ = 1 := by
        group
      rw [h1] at h
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, ← detChar_scalarGSpin, h, Units.val_one]
    have hzx : z * x * z⁻¹ = scalarGSpin d.QW c * x := by rw [hc']; group
    have hconj : ∀ n : ℕ, z ^ n * x * (z ^ n)⁻¹ = scalarGSpin d.QW (c ^ n) * x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hcz : scalarGSpin d.QW (c ^ n) * z = z * scalarGSpin d.QW (c ^ n) :=
          (scalarGSpin_commute d.QW (c ^ n) z).eq
        calc z ^ (n + 1) * x * (z ^ (n + 1))⁻¹ = z * (z ^ n * x * (z ^ n)⁻¹) * z⁻¹ := by group
          _ = scalarGSpin d.QW (c ^ n) * (z * x * z⁻¹) := by
            rw [ih, ← mul_assoc, ← hcz]; group
          _ = scalarGSpin d.QW (c ^ (n + 1)) * x := by
            rw [hzx, ← mul_assoc, ← map_mul, pow_succ]
    have hpow : ∀ (n : ℕ) (v : Fin d.m → F),
        (specP d.QW (z ^ n) : Module.End F (Fin d.m → F)) v =
          ((specP d.QW z : Module.End F (Fin d.m → F)) ^ n) v := fun n => by
      induction n with
      | zero => intro v; simp
      | succ n ih =>
        intro v
        rw [pow_succ, map_mul, pow_succ, Module.End.mul_apply, ← ih]
        rfl
    refine ⟨z ^ N, ⟨?_, fun v hv => ?_⟩, ?_⟩
    · change z ^ N ∈ Subgroup.centralizer {x}
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hconj N
      rw [hcN, map_one, one_mul] at h
      calc z ^ N * x = z ^ N * x * (z ^ N)⁻¹ * z ^ N := by group
        _ = x * z ^ N := by rw [h]
    · change (specP d.QW (z ^ N) : Module.End F (Fin d.m → F)) v = v
      rw [hpow]
      clear hpow hconj
      induction N with
      | zero => rfl
      | succ n ih => rw [pow_succ, Module.End.mul_apply, hPzW v hv, ih]
    · change (specP d.QW (z ^ N) : Module.End F (Fin d.m → F)) u = _
      rw [hpow]
      clear hpow hconj
      induction N with
      | zero => simp
      | succ n ih => rw [pow_succ, Module.End.mul_apply, hPzf, map_smul, ih, smul_smul,
          pow_succ, mul_comm]
  -- boundedness on the compact `T_x(F)/A(F)`
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ t ∈ d.torusOf x,
      ‖QuadraticMap.polar d.QW (f'' : Fin d.m → F) (specP d.QW t (u : Fin d.m → F))‖ ≤ R := by
    have : CompactSpace (d.TorusQuot (d.torusOf x)) := hx.2.2
    let φ : ↥(d.torusOf x) → F := fun t =>
      QuadraticMap.polar d.QW (f'' : Fin d.m → F) (specP d.QW (t : ↥(GSpin d.QW)) (u : Fin d.m → F))
    have hPc : Continuous fun t : ↥(d.torusOf x) =>
        specP d.QW (t : ↥(GSpin d.QW)) (u : Fin d.m → F) := by
      have hn : Continuous fun t : ↥(d.torusOf x) =>
          ((t : ↥(GSpin d.QW)) : (CliffordAlgebra d.QW)ˣ) :=
        continuous_subtype_val.comp continuous_subtype_val
      simp only [specP_apply_eq]
      exact (IsModuleTopology.continuous_of_linearMap (CliffordAlgebra.ιInv d.QW)).comp
        ((Units.continuous_val.comp hn).mul (continuous_const.mul (Units.continuous_coe_inv.comp hn)))
    have hφc : Continuous φ :=
      (LinearMap.continuous_of_finiteDimensional
        (QuadraticMap.polarBilin d.QW (f'' : Fin d.m → F))).comp hPc
    have hφinv : ∀ a b : ↥(d.torusOf x),
        (QuotientGroup.leftRel (d.scalarsIn (d.torusOf x))) a b → φ a = φ b := by
      intro a b hab
      obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf).1 (QuotientGroup.leftRel_apply.1 hab)
      have hb : (b : ↥(GSpin d.QW)) = (a : ↥(GSpin d.QW)) * scalarGSpin d.QW c := by
        rw [hc]; simp
      simp only [φ, hb, map_mul, specP_scalarGSpin_eq_one, mul_one]
    let ψ : d.TorusQuot (d.torusOf x) → F := Quotient.lift φ hφinv
    have hψc : Continuous ψ := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr hφc
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hψc.continuousOn
    exact ⟨C, fun t ht => hC (QuotientGroup.mk ⟨t, ht⟩) (Set.mem_univ _)⟩
  obtain ⟨s, hs⟩ := NormedField.exists_lt_norm F (max R 1)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hs
    linarith [le_max_right R 1]
  obtain ⟨t, ht, htf⟩ := key s hs0
  have hb := hR t ht
  rw [htf, QuadraticMap.polar_smul_right, QuadraticMap.polar_comm, hp, smul_eq_mul, mul_one,
    norm_pow] at hb
  have h1 : 1 < ‖s‖ := lt_of_le_of_lt (le_max_right _ _) hs
  have h3 : ‖s‖ ≤ ‖s‖ ^ N := le_self_pow₀ h1.le (Nat.pos_iff_ne_zero.1 hN)
  linarith [le_max_left R 1]

end Gamma

end GSpinGGP
