/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Basic
import GSpinGGP.Foundations.WeakCartanFrame
import GSpinGGP.Foundations.QuadraticForms

/-!
# The good minimal parabolic subgroup of Thesis Prop. 8.1.1(i)

Test file (work in progress).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Module QuadraticMap

namespace GSpinGGP

/-! ## 1. Isotropic flags of initial segments -/

section OfFamily

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- The span of a family whose vectors are isotropic and pairwise orthogonal is totally
isotropic. -/
theorem isTotallyIsotropic_span_of_polar {ι : Type*} (e : ι → V)
    (h : ∀ i j, polar Q (e i) (e j) = 0) :
    IsTotallyIsotropic Q (Submodule.span K (Set.range e)) := by
  have hall : ∀ x ∈ Submodule.span K (Set.range e), ∀ y ∈ Submodule.span K (Set.range e),
      polar Q x y = 0 := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy => obtain ⟨j, rfl⟩ := hy; exact h i j
      | zero => simp
      | add y z _ _ hy hz => rw [polar_add_right, hy, hz, add_zero]
      | smul c y _ hy => rw [polar_smul_right, hy, smul_zero]
    | zero => simp
    | add x z _ _ hx hz => rw [polar_add_left, hx, hz, add_zero]
    | smul c x _ hx => rw [polar_smul_left, hx, smul_zero]
  intro x hx
  have h2 := hall x hx x hx
  rw [polar_self, two_smul] at h2
  have : (2 : K) * Q x = 0 := by rw [two_mul]; exact h2
  exact (mul_eq_zero.mp this).resolve_left (Invertible.ne_zero 2)

namespace IsotropicFlag

theorem castLE_le_aux {k : ℕ} (i : Fin (k + 1)) : (i : ℕ) ≤ k := Nat.lt_succ_iff.mp i.2

/-- **The isotropic flag of initial segments** of a linearly independent family `v₀, …, v_{k-1}`
with totally isotropic span: `Z_i = ⟨v₀, …, v_{i-1}⟩`. -/
def ofFamily {k : ℕ} (v : Fin k → V) (hv : LinearIndependent K v)
    (hiso : IsTotallyIsotropic Q (Submodule.span K (Set.range v))) : IsotropicFlag Q where
  len := k
  sub i := Submodule.span K (Set.range (v ∘ Fin.castLE (castLE_le_aux i)))
  sub_zero := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨j, rfl⟩
    exact j.elim0
  strictMono := by
    have hfin : ∀ i : Fin (k + 1), finrank K (Submodule.span K
        (Set.range (v ∘ Fin.castLE (castLE_le_aux i)))) = (i : ℕ) := fun i => by
      rw [finrank_span_eq_card (hv.comp _ (Fin.castLE_injective _)), Fintype.card_fin]
    intro i j hij
    refine lt_of_le_of_ne (Submodule.span_mono ?_) fun h => ?_
    · rintro _ ⟨l, rfl⟩
      exact ⟨Fin.castLE (Fin.le_iff_val_le_val.mp hij.le) l, rfl⟩
    · have := congrArg (fun S : Submodule K V => finrank K S) h
      simp only [hfin] at this
      exact (Fin.val_injective this ▸ hij).false
  isotropic i u hu := hiso u (Submodule.span_mono (Set.range_comp_subset_range _ _) hu)

variable {k : ℕ} {v : Fin k → V} {hv : LinearIndependent K v}
  {hiso : IsTotallyIsotropic Q (Submodule.span K (Set.range v))}

@[simp]
theorem ofFamily_len : (ofFamily v hv hiso).len = k := rfl

theorem ofFamily_sub (i : Fin (k + 1)) :
    (ofFamily v hv hiso).sub i = Submodule.span K (Set.range (v ∘ Fin.castLE (castLE_le_aux i))) :=
  rfl

theorem finrank_ofFamily_sub (i : Fin (k + 1)) :
    finrank K ((ofFamily v hv hiso).sub i) = (i : ℕ) := by
  rw [ofFamily_sub, finrank_span_eq_card (hv.comp _ (Fin.castLE_injective _)), Fintype.card_fin]

theorem ofFamily_top : (ofFamily v hv hiso).top = Submodule.span K (Set.range v) := by
  change Submodule.span K (Set.range (v ∘ Fin.castLE _)) = _
  congr 2

theorem mem_ofFamily_sub {i : Fin (k + 1)} {j : Fin k} (hj : (j : ℕ) < i) :
    v j ∈ (ofFamily v hv hiso).sub i :=
  Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩

/-- The flag of initial segments of a family of length the Witt index is full. -/
theorem isFull_ofFamily (h : k = wittIndex Q) : (ofFamily v hv hiso).IsFull :=
  ⟨h, finrank_ofFamily_sub⟩

end IsotropicFlag

end OfFamily

/-! ## 2. The Witt index from a hyperbolic frame with anisotropic complement -/

section WittIndex

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {W : Submodule K V} {n : ℕ} {e f : Fin n → V}

/-- The isotropic half `⟨e₀, …, e_{n-1}⟩` of a hyperbolic frame is totally isotropic. -/
theorem IsHypFrame.isTotallyIsotropic_span_e (hF : IsHypFrame Q W e f) :
    IsTotallyIsotropic Q (Submodule.span K (Set.range e)) :=
  isTotallyIsotropic_span_of_polar e hF.polar_ee

/-- **The Witt index of a hyperbolic frame with anisotropic complement** is the number of its
pairs: `⟨e⟩` is then a maximal totally isotropic subspace (Tau Ceti's
`QuadraticForm.maximal_isTotallyIsotropic_iff`, Lam I.4.4). -/
theorem IsHypFrame.wittIndex_eq (hQ : IsNondeg Q) (hF : IsHypFrame Q W e f)
    (hW : ∀ w ∈ W, Q w = 0 → w = 0) : wittIndex Q = n := by
  have hQ' := (isNondeg_iff_nondegenerate Q).1 hQ
  have hli : LinearIndependent K e := hF.linearIndependent.comp Sum.inl Sum.inl_injective
  have hfin : finrank K (Submodule.span K (Set.range e)) = n := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hmax : Maximal Q.IsTotallyIsotropic (Submodule.span K (Set.range e)) := by
    refine ⟨hF.isTotallyIsotropic_span_e, fun U hU hle x hx => ?_⟩
    have hpe : ∀ j, polar Q x (e j) = 0 := fun j =>
      hU.polar_eq_zero hx (hle (Submodule.subset_span ⟨j, rfl⟩))
    have hfs : frameSum Q e f x ∈ Submodule.span K (Set.range e) := by
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [hpe j, zero_smul, add_zero]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hy0 : x - frameSum Q e f x = 0 :=
      hW _ (hF.proj_mem x) (hU _ (U.sub_mem hx (hle hfs)))
    rw [sub_eq_zero] at hy0
    rw [hy0]; exact hfs
  rw [wittIndex_eq_regularFormClass_wittIndex Q hQ', ← hfin]
  exact (QuadraticForm.finrank_eq_wittIndex_of_maximal Q hQ' hmax).symm

end WittIndex

/-! ## 3. Hyperbolic frames from their polar relations -/

section OrthFrame

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- The orthogonal complement `{e, f}^⊥` of two families of vectors. -/
def orthFrame (Q : QuadraticForm K V) {n : ℕ} (e f : Fin n → V) : Submodule K V where
  carrier := {v | ∀ i, polar Q v (e i) = 0 ∧ polar Q v (f i) = 0}
  add_mem' ha hb i := ⟨by rw [polar_add_left, (ha i).1, (hb i).1, add_zero],
    by rw [polar_add_left, (ha i).2, (hb i).2, add_zero]⟩
  zero_mem' i := ⟨by simp, by simp⟩
  smul_mem' c v hv i := ⟨by rw [polar_smul_left, (hv i).1, smul_zero],
    by rw [polar_smul_left, (hv i).2, smul_zero]⟩

theorem mem_orthFrame {Q : QuadraticForm K V} {n : ℕ} {e f : Fin n → V} {v : V} :
    v ∈ orthFrame Q e f ↔ ∀ i, polar Q v (e i) = 0 ∧ polar Q v (f i) = 0 := Iff.rfl

/-- Families with the polar relations of a hyperbolic frame form one, with complement
`orthFrame`. -/
theorem isHypFrame_orthFrame {Q : QuadraticForm K V} {n : ℕ} {e f : Fin n → V}
    (hee : ∀ i j, polar Q (e i) (e j) = 0) (hff : ∀ i j, polar Q (f i) (f j) = 0)
    (hef : ∀ i j, polar Q (e i) (f j) = if i = j then 1 else 0) :
    IsHypFrame Q (orthFrame Q e f) e f :=
  ⟨hee, hff, hef, fun _ => Iff.rfl⟩

end OrthFrame

/-! ## 4. Anisotropy past a maximal frame -/

namespace WeakCartan

variable {F : Type*} [NontriviallyNormedField F] {V : Type*} [AddCommGroup V] [Module F V]
  {n : ℕ} {b : Module.Basis (Fin n) F V} {Q : QuadraticForm F V}

/-- **Past a maximal frame the form is anisotropic.** A vector whose first `l` coordinates vanish
(so it lies in `⟨w_l⟩ ⊕ ⟨w₀, …, w_l⟩^⊥`) and which is isotropic is `0`: otherwise either its
`w_l`-coordinate is nonzero, and rescaling its component in `⟨w₀, …, w_l⟩^⊥` represents
`(-1)^{l+1} ν`, or it is a nonzero isotropic vector of `⟨w₀, …, w_l⟩^⊥`, which then contains a
hyperbolic plane and represents every value. Both contradict the maximality of the frame. -/
theorem IsFrame.eq_zero_of_isotropic [NeZero (2 : F)] (hb : IsOrthoBasis Q b) {ν : F} {l : ℕ}
    (hf : IsFrame Q b ν l) {x : V} (hx : ∀ i : Fin n, i.val < l → b.repr x i = 0)
    (hQ : Q x = 0) : x = 0 := by
  classical
  set bl := b ⟨l, hf.lt⟩
  set c := b.repr x ⟨l, hf.lt⟩
  set y := x - c • bl with hy
  have hQbl : Q bl = (-1) ^ l * ν := hf.apply_eq _ le_rfl
  have hyrepr : ∀ i : Fin n, i.val ≤ l → b.repr y i = 0 := by
    intro i hi
    rw [hy, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, b.repr_self,
      Finsupp.single_apply]
    rcases lt_or_eq_of_le hi with h | h
    · rw [hx i h, ite_eq_right (fun h' => by rw [← h'] at h; exact lt_irrefl _ h), smul_zero, sub_zero]
    · have : (⟨l, hf.lt⟩ : Fin n) = i := Fin.ext h.symm
      rw [ite_eq_left this, smul_eq_mul, mul_one, ← this, sub_self]
  have hpol : polar Q bl y = 0 := by
    rw [polar_basis_left Q b hb.isOrtho, hyrepr _ le_rfl, mul_zero]
  have hQx : Q x = Q y + c ^ 2 * ((-1) ^ l * ν) := by
    have : x = y + c • bl := by rw [hy, sub_add_cancel]
    rw [this, QuadraticMap.map_add Q, QuadraticMap.map_smul, hQbl, polar_smul_right, polar_comm,
      hpol, smul_zero, add_zero, smul_eq_mul]
    ring
  by_cases hc : c = 0
  · -- `x = y` is an isotropic vector of `⟨w₀, …, w_l⟩^⊥`
    have hxy : x = y := by rw [hy, hc, zero_smul, sub_zero]
    by_contra hx0
    have hy0 : y ≠ 0 := hxy ▸ hx0
    obtain ⟨m, hm⟩ : ∃ m, b.repr y m ≠ 0 := by
      by_contra h
      push Not at h
      exact hy0 (b.repr.injective (Finsupp.ext fun m => by simp [h m]))
    have hml : l < m.val := by
      by_contra h
      exact hm (hyrepr m (not_lt.mp h))
    have hp : polar Q (b m) y ≠ 0 := by
      rw [polar_basis_left Q b hb.isOrtho]
      exact mul_ne_zero (mul_ne_zero two_ne_zero (hb.apply_ne_zero m)) hm
    have hQy : Q y = 0 := by rw [← hxy]; exact hQ
    set t := ((-1) ^ (l + 1) * ν - Q (b m)) / polar Q (b m) y
    refine hf.maximal (b m + t • y) (fun i hi => ?_) ?_
    · rw [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, b.repr_self,
        Finsupp.single_apply, ite_eq_right (fun h => by rw [← h] at hi; omega), hyrepr i hi,
        smul_zero, add_zero]
    · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, hQy, smul_zero, add_zero,
        polar_smul_right, smul_eq_mul]
      simp only [t, div_mul_cancel₀ _ hp]
      ring
  · -- rescale: `Q (c⁻¹ y) = (-1)^{l+1} ν`
    exfalso
    refine hf.maximal (c⁻¹ • y) (fun i hi => ?_) ?_
    · rw [map_smul, Finsupp.smul_apply, hyrepr i hi, smul_zero]
    · rw [QuadraticMap.map_smul, smul_eq_mul]
      have hQy : Q y = -(c ^ 2 * ((-1) ^ l * ν)) := by
        rw [hQ] at hQx; linear_combination -hQx
      rw [hQy]
      field_simp
      ring

end WeakCartan

/-! ## 5. The space `V₀ = W ⊕ ⟨z₀⟩` and its embedding in `V` -/

section Coordinates

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- `b(x, z_j) = ν · x_{-j}` in the coordinates of `Z` (index `t` stands for `z_{t-r}`). -/
theorem bform_splitOddForm_single (r : ℕ) (ν : K) (x : Fin (2 * r + 1) → K)
    (j : Fin (2 * r + 1)) :
    bform (splitOddForm r ν) x (Pi.single j 1) = ν * x j.rev := by
  rw [bform_splitOddForm, dotProduct]
  rw [Finset.sum_eq_single j.rev]
  · simp only [Matrix.mulVec, dotProduct, splitOddMatrix]
    rw [Finset.sum_eq_single j]
    · have h : ((j.rev : ℕ) + (j : ℕ) = 2 * r) := by simp [Fin.val_rev]; omega
      simp only [h, ite_true, Pi.single_eq_same]
      ring
    · intro k _ hk; simp [Pi.single_apply, hk]
    · simp
  · intro i _ hi
    simp only [Matrix.mulVec, dotProduct, splitOddMatrix]
    rw [Finset.sum_eq_single j]
    · have h : ¬ ((i : ℕ) + (j : ℕ) = 2 * r) := by
        intro h; apply hi; ext; simp [Fin.val_rev]; omega
      simp [h]
    · intro k _ hk; simp [Pi.single_apply, hk]
    · simp
  · simp

/-- `q(z₀) = ν`. -/
theorem splitOddForm_zvec_zero (r : ℕ) (ν : K) : splitOddForm r ν (zvec r 0) = ν := by
  rw [← QuadraticMap.associated_eq_self_apply K, ← bform,
    bform_splitOddForm_zvec _ _ (by simp) (by simp)]
  simp

end Coordinates

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

/-! ## 6. The explicit full flags of a frame (Thesis Prop. 8.1.1(i)) -/

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
  rw [← h0 hn, polar_basis_left d.Q0 b hb.isOrtho, b.repr_self,
    Finsupp.single_apply, ite_eq_right (fun h => hm (by simp [h])), mul_zero]

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
/-- `W_an`, the complement of the pairs `(u′ᵢ, ·)` in `W`, is anisotropic. -/
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
      rw [polar_basis_left d.Q0 b hb.isOrtho] at hp
      exact (mul_eq_zero.mp hp).resolve_left (mul_ne_zero two_ne_zero (hb.apply_ne_zero i))
    · by_contra hne
      have := hxc (Finsupp.mem_support_iff.mpr hne)
      simp only [Set.mem_ofPred_eq, numPairs] at this
      omega
  have hx0 := hf.eq_zero_of_isotropic hb hx (by simp [x, hQ])
  exact congrArg Prod.fst hx0

/-- The full isotropic flag `⟨u′₁⟩ ⊂ ⟨u′₁, u′₂⟩ ⊂ ⋯` of `W` (Thesis Prop. 8.1.1(i)). -/
def flagW : IsotropicFlag d.QW :=
  IsotropicFlag.ofFamily (eW hf)
    ((isHypFrame_W hb hf h0).linearIndependent.comp Sum.inl Sum.inl_injective)
    (isHypFrame_W hb hf h0).isTotallyIsotropic_span_e

theorem isFull_flagW : (flagW hb hf h0).IsFull :=
  IsotropicFlag.isFull_ofFamily
    ((isHypFrame_W hb hf h0).wittIndex_eq d.nondeg (fun y hy hQ => aniso_W hb hf h0 hy hQ)).symm

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
  rw [zb, zb, d.polar_zV_zV (abs_neg_le k) (abs_neg_le k'), ite_eq_right (by have := k.2; have := k'.2; omega)]

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
    refine Prod.ext rfl (funext fun t => ?_)
    simp only [iota0_apply, pi0, LinearMap.prodMap_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul, zvec]
    by_cases ht : (t : ℕ) = d.r
    · have : t = ⟨d.r, by omega⟩ := Fin.ext ht
      rw [this]
      simp
    · have ht2 := t.2
      have habs : |(d.r : ℤ) - t| ≤ d.r := by rw [abs_le]; constructor <;> omega
      have hj := hz ((d.r : ℤ) - t) (by omega) habs
      rw [bform_zV_eq _ _ habs] at hj
      have e : (⟨((d.r : ℤ) - ((d.r : ℤ) - t)).toNat, by omega⟩ : Fin (2 * d.r + 1)) = t :=
        Fin.ext (by simp)
      rw [e] at hj
      rw [(mul_eq_zero.mp hj).resolve_left d.ν.ne_zero]
      simp [show ¬ ((t : ℤ) - d.r = 0) by omega]
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
  rw [hyi, hf.eq_zero_of_isotropic hb hx hQx, map_zero]

/-- The full isotropic flag `⟨z_{-r}⟩ ⊂ ⋯ ⊂ ⟨z_{-r}, …, z_{-1}⟩ ⊂ ⟨z_{-r}, …, z_{-1}, u₁⟩ ⊂ ⋯`
of `V` (Thesis Prop. 8.1.1(i)). -/
def flagV : IsotropicFlag d.QV :=
  IsotropicFlag.ofFamily (eV hf)
    ((isHypFrame_V hb hf h0).linearIndependent.comp Sum.inl Sum.inl_injective)
    (isHypFrame_V hb hf h0).isTotallyIsotropic_span_e

theorem isFull_flagV : (flagV hb hf h0).IsFull :=
  IsotropicFlag.isFull_ofFamily
    ((isHypFrame_V hb hf h0).wittIndex_eq d.nondeg_QV
      (fun y hy hQ => aniso_V hb hf h0 hy hQ)).symm

end Flags

end GGPData

/-! ## 7. `H ∩ Ū_min = 1` -/

section GSpinScalar

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]
  [Module.Finite K V] {Q : QuadraticForm K V}

/-- An element of `GSpin(V)` acting trivially on `V` with `g − 1` nilpotent is `1`: it is a
scalar `c` (`ker_specP`), and `c − 1` nilpotent forces `c = 1`. -/
theorem eq_one_of_specP_eq_one (hQ : IsNondeg Q) {g : GSpin Q} (h1 : specP Q g = 1)
    (hn : IsNilpotent (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1)) : g = 1 := by
  obtain ⟨c, rfl⟩ : g ∈ (scalarGSpin Q).range := by rw [← ker_specP hQ]; exact h1
  have e : (((scalarGSpin Q c : GSpin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1 =
      algebraMap K _ ((c : K) - 1) := by
    rw [map_sub, map_one]; rfl
  rw [e, IsNilpotent.map_iff (algebraMap K (CliffordAlgebra Q)).injective,
    isNilpotent_iff_eq_zero, sub_eq_zero, Units.val_eq_one] at hn
  rw [hn, map_one]

/-- `P(g)` preserves `polar`. -/
theorem polar_specP (g : GSpin Q) (x y : V) :
    polar Q (specP Q g x) (specP Q g y) = polar Q x y := by
  simp only [polar, ← map_add, specP_isometry]

end GSpinScalar

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

/-- A combination of `z_{σ(j)}` orthogonal to every `z_{-σ(j)}` is `0`. -/
theorem eq_zero_of_mem_span_zV {k : ℕ} (σ : Fin k → ℤ) (hσ : Function.Injective σ)
    (hr : ∀ j, |σ j| ≤ d.r) {x : d.V} (hx : x ∈ Submodule.span F (Set.range (d.zV ∘ σ)))
    (h : ∀ j, bform d.QV x (d.zV (-σ j)) = 0) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hx
  have hc : ∀ j, c j = 0 := by
    intro j
    have := h j
    rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single j] at this
    · rw [map_smul, LinearMap.smul_apply, Function.comp_apply, bform_QV_zV,
        bform_splitOddForm_zvec _ _ (hr j) (by rw [abs_neg]; exact hr j), ite_eq_left (by ring),
        smul_eq_mul] at this
      exact (mul_eq_zero.mp this).resolve_right d.ν.ne_zero
    · intro i _ hij
      rw [map_smul, LinearMap.smul_apply, Function.comp_apply, bform_QV_zV,
        bform_splitOddForm_zvec _ _ (hr i) (by rw [abs_neg]; exact hr j),
        ite_eq_right (fun h => hij (hσ (by linarith))), smul_zero]
    · simp
  simp [hc]

/-- `z_s ⊥ Z_r` for `s ≥ 0`. -/
theorem zV_nonneg_mem_orthogonal_top {s : ℤ} (hs : 0 ≤ s) :
    d.zV s ∈ (bform d.QV).orthogonal d.flag.top := by
  intro t ht
  change t ∈ Submodule.span F (Set.range fun j : Fin d.r => d.zV ((d.r : ℤ) - (j : ℕ))) at ht
  refine Submodule.span_induction (p := fun t _ => bform d.QV t (d.zV s) = 0)
    ?_ (by simp) (fun x y _ _ hx hy => by rw [map_add, LinearMap.add_apply, hx, hy, add_zero])
    (fun c x _ hx => by rw [map_smul, LinearMap.smul_apply, hx, smul_zero]) ht
  rintro _ ⟨j, rfl⟩
  by_cases hsr : s ≤ d.r
  · have hj : (j : ℕ) < d.r := j.2
    rw [bform_QV_zV, bform_splitOddForm_zvec _ _ (by rw [abs_le]; omega)
      (by rw [abs_le]; omega)]
    split_ifs with h
    · omega
    · rfl
  · have : zvec d.r s = (0 : Fin (2 * d.r + 1) → F) := by
      ext i; simp only [zvec, Pi.zero_apply]; rw [ite_eq_right (by omega)]
    simp [zV, this]

/-- For `n ∈ N` and `1 ≤ s ≤ r`: `P(n) z_s − z_s ∈ ⟨z_r, …, z_{s+1}⟩`. -/
theorem specP_zV_sub_mem' {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ d.r) {n : GSpin d.QV}
    (hn : n ∈ d.N) :
    specP d.QV n (d.zV (s : ℕ)) - d.zV (s : ℕ) ∈
      Submodule.span F (Set.range fun j : Fin (d.r - s) => d.zV ((d.r : ℤ) - (j : ℕ))) := by
  rcases lt_or_eq_of_le hs with h | rfl
  · exact d.specP_zV_sub_mem ⟨s, h⟩ hn
  · obtain ⟨-, hn1, -, -⟩ := hn
    have := hn1 ⟨0, by change 0 < d.r; omega⟩ (d.zV (d.r : ℕ)) (Submodule.subset_span
      ⟨⟨0, by simp⟩, by simp⟩)
    have h0 : d.flag.sub (Fin.castSucc ⟨0, by change 0 < d.r; omega⟩) = ⊥ := d.flag.sub_zero
    rw [h0, Submodule.mem_bot] at this
    rw [this]; exact zero_mem _

/-- `b(z_i, x) = 0` for `x` a combination of `z_{τ(j)}` with `i + τ(j) ≠ 0`. -/
theorem bform_zV_eq_zero_of_mem_span {k : ℕ} (τ : Fin k → ℤ) {i : ℤ} (hi : |i| ≤ d.r)
    (hτ : ∀ j, |τ j| ≤ d.r) (hne : ∀ j, i + τ j ≠ 0) {x : d.V}
    (hx : x ∈ Submodule.span F (Set.range (d.zV ∘ τ))) : bform d.QV (d.zV i) x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hx
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, Function.comp_apply, bform_QV_zV, bform_splitOddForm_zvec _ _ hi (hτ j),
    ite_eq_right (hne j), smul_zero]

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
  have hε := d.specP_zV_sub_mem' (s := s) (by omega) (by omega) (d.N.inv_mem hn)
  have hε0 : bform d.QV (zb (d := d) k) (specP d.QV nn⁻¹ (d.zV (s : ℕ)) - d.zV (s : ℕ)) = 0 :=
    d.bform_zV_eq_zero_of_mem_span (fun j' : Fin (d.r - s) => (d.r : ℤ) - (j' : ℕ))
      (abs_neg_le k) (fun j' => by have := j'.2; rw [abs_le]; constructor <;> omega)
      (fun j' => by have := j'.2; omega) hε
  rw [e, hzs, sub_zero]
  rw [map_sub, hzs, sub_zero] at hε0
  exact hε0

/-- **`N ∩ P̄ = 1` at the level of `SO(V)`.** An element of `N` fixing `z_{-r}, …, z_{-1}` acts
trivially on `V`: on `Z_r^⊥` it moves vectors into `Z_r = ⟨z_r, …, z_1⟩`, and the move is
orthogonal to the `z_{-k}`. -/
theorem specP_eq_one_of_mem_N {nn : GSpin d.QV} (hn : nn ∈ d.N)
    (hfix : ∀ k : Fin d.r, specP d.QV nn (zb (d := d) k) = zb (d := d) k) :
    specP d.QV nn = 1 := by
  have horth : ∀ v ∈ (bform d.QV).orthogonal d.flag.top, specP d.QV nn v = v := by
    intro v hv
    rw [← sub_eq_zero]
    have hmem := hn.2.2.1 v hv
    change _ ∈ Submodule.span F (Set.range fun j : Fin d.r => d.zV ((d.r : ℤ) - (j : ℕ)))
      at hmem
    refine d.eq_zero_of_mem_span_zV (fun j : Fin d.r => (d.r : ℤ) - (j : ℕ))
      (fun a c h => Fin.ext (by simp at h; omega))
      (fun j => by have := j.2; rw [abs_le]; constructor <;> omega) hmem (fun j => ?_)
    rw [map_sub, LinearMap.sub_apply, show d.zV (-((d.r : ℤ) - (j : ℕ))) = zb (d := d) j from rfl]
    have e : bform d.QV (specP d.QV nn v) (zb (d := d) j) = bform d.QV v (zb (d := d) j) := by
      conv_lhs => rw [← hfix j]
      rw [bform_specP]
    rw [e, sub_self]
  have hsingle : ∀ t : Fin (2 * d.r + 1),
      specP d.QV nn ((0, Pi.single t 1) : d.V) = (0, Pi.single t 1) := by
    intro t
    have ht := t.2
    have habs : |(t : ℤ) - d.r| ≤ d.r := by rw [abs_le]; constructor <;> omega
    have e : ((0, Pi.single t 1) : d.V) = d.zV ((t : ℤ) - d.r) := by
      rw [zV, zvec_eq_single _ habs]
      congr 2
      exact Fin.ext (by simp)
    rw [e]
    by_cases hneg : (t : ℕ) < d.r
    · have := hfix ⟨t, hneg⟩
      rw [zb, show (-((d.r : ℤ) - ((⟨t, hneg⟩ : Fin d.r) : ℕ))) = (t : ℤ) - d.r by
        simp] at this
      exact this
    · exact horth _ (d.zV_nonneg_mem_orthogonal_top (by omega))
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨w, z⟩ := v
  have hv : ((w, z) : d.V) = (w, 0) + ∑ t, z t • ((0, Pi.single t 1) : d.V) := by
    refine Prod.ext (by simp [Prod.fst_sum]) ?_
    simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, zero_add]
    ext t
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv, map_add, map_sum, horth _ (d.inl_mem_orthogonal_top w)]
  simp only [map_smul, hsingle]
  rfl

end GGPData

end GSpinGGP
