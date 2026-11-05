import Mathlib.LinearAlgebra.QuadraticForm.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Witt.Extension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# Hyperbolic frames and their split tori

A *hyperbolic frame* of a quadratic space `(V, Q)` is a family of hyperbolic pairs `eᵢ, fᵢ`
(`polar(eᵢ, eⱼ) = polar(fᵢ, fⱼ) = 0`, `polar(eᵢ, fⱼ) = δᵢⱼ`) together with its orthogonal
complement `W` (`IsHypFrame`). Every vector splits as
`v = w + Σ (polar(v, fⱼ) eⱼ + polar(v, eⱼ) fⱼ)` with `w ∈ W` (`IsHypFrame.proj_mem`).

* `hypTorus W e f`: the split torus of the frame, the automorphisms fixing `W` pointwise and
  scaling `eᵢ, fᵢ` by `tᵢ, tᵢ⁻¹` (a subgroup of `GL(V)`; when `2` is invertible the `eᵢ, fᵢ` are
  isotropic and it is the usual split torus of `SO(Q)` attached to the frame).
* `IsHypFrame.mem_hypTorus_of_commute`: an isometry fixing `W` and commuting with a regular element
  of the torus (`tᵢ ≠ 1`, `tᵢ` distinct, `tᵢ tⱼ ≠ 1`) lies in the torus.
* `hypTorus_map_conj`: an automorphism carrying one frame to another conjugates their tori.
* `IsHypFrame.exists_conj_hypTorus`: for a nondegenerate form (characteristic `≠ 2`), the tori of
  two frames of the same size are conjugate under `SO(Q)`: Witt's extension theorem (Tau Ceti's
  `QuadraticMap.IsometryEquiv.exists_extension`) gives an isometry carrying one frame to the other,
  and the reflection in `e₀ − f₀` (which swaps `e₀, f₀` and normalizes the torus) corrects its
  determinant.
* `IsHypFrame.finrank_add`: `dim W + 2n = dim V`.
-/

noncomputable section

open QuadraticMap

namespace GSpinGGP

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- `e, f : Fin n → V` is a hyperbolic frame with orthogonal complement `W`:
`polar(eᵢ, eⱼ) = polar(fᵢ, fⱼ) = 0`, `polar(eᵢ, fⱼ) = δᵢⱼ`, and `W = {e, f}^⊥`. -/
structure IsHypFrame (Q : QuadraticForm K V) (W : Submodule K V) {n : ℕ} (e f : Fin n → V) :
    Prop where
  polar_ee : ∀ i j, polar Q (e i) (e j) = 0
  polar_ff : ∀ i j, polar Q (f i) (f j) = 0
  polar_ef : ∀ i j, polar Q (e i) (f j) = if i = j then 1 else 0
  mem_iff : ∀ v, v ∈ W ↔ ∀ i, polar Q v (e i) = 0 ∧ polar Q v (f i) = 0

namespace IsHypFrame

variable {Q : QuadraticForm K V} {W : Submodule K V} {n : ℕ} {e f : Fin n → V}

theorem polar_fe (hF : IsHypFrame Q W e f) (i j : Fin n) :
    polar Q (f i) (e j) = if j = i then 1 else 0 := by
  rw [polar_comm, hF.polar_ef]

theorem polar_sum_e (hF : IsHypFrame Q W e f) (a b : Fin n → K) (i : Fin n) :
    polar Q (∑ j, (a j • e j + b j • f j)) (e i) = b i := by
  rw [← polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, polarBilin_apply_apply,
    hF.polar_ee, hF.polar_fe, smul_eq_mul, mul_zero, zero_add, mul_ite, mul_one]
  simp

theorem polar_sum_f (hF : IsHypFrame Q W e f) (a b : Fin n → K) (i : Fin n) :
    polar Q (∑ j, (a j • e j + b j • f j)) (f i) = a i := by
  rw [← polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, polarBilin_apply_apply,
    hF.polar_ff, hF.polar_ef, smul_eq_mul, mul_zero, add_zero, mul_ite, mul_one]
  simp

/-- The frame part of `v`. -/
def frameSum (Q : QuadraticForm K V) (e f : Fin n → V) (v : V) : V :=
  ∑ j, (polar Q v (f j) • e j + polar Q v (e j) • f j)

/-- **`V = W ⊕ span(e, f)`**: `v − Σ (polar(v, fⱼ) eⱼ + polar(v, eⱼ) fⱼ) ∈ W`. -/
theorem proj_mem (hF : IsHypFrame Q W e f) (v : V) : v - frameSum Q e f v ∈ W := by
  rw [hF.mem_iff]
  intro i
  simp only [frameSum, polar_sub_left, hF.polar_sum_e, hF.polar_sum_f, sub_self, and_self]


/-- Linear maps agreeing on `W` and on the frame are equal. -/
theorem linearMap_ext (hF : IsHypFrame Q W e f) {g h : V →ₗ[K] V} (hW : ∀ w ∈ W, g w = h w)
    (he : ∀ i, g (e i) = h (e i)) (hf : ∀ i, g (f i) = h (f i)) : g = h := by
  ext v
  rw [← add_sub_cancel (frameSum Q e f v) v, map_add, map_add, hW _ (hF.proj_mem v)]
  simp [frameSum, map_sum, he, hf]

end IsHypFrame

/-- The split torus of a frame, as a subgroup of `GL(V)`: automorphisms fixing `W` pointwise and
scaling `eᵢ, fᵢ` by `tᵢ, tᵢ⁻¹`. -/
def hypTorus (W : Submodule K V) {n : ℕ} (e f : Fin n → V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {h | (∀ w ∈ W, h w = w) ∧
    ∃ t : Fin n → Kˣ, ∀ i, h (e i) = (t i : K) • e i ∧ h (f i) = (((t i)⁻¹ : Kˣ) : K) • f i}
  one_mem' := ⟨fun _ _ => rfl, fun _ => 1, fun _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haW, s, hs⟩ ⟨hbW, t, ht⟩
    refine ⟨fun w hw => by rw [LinearEquiv.mul_apply, hbW w hw, haW w hw], fun i => s i * t i,
      fun i => ?_⟩
    simp only [LinearEquiv.mul_apply, (ht i).1, (ht i).2, map_smul, (hs i).1, (hs i).2, smul_smul,
      Units.val_mul, mul_inv, mul_comm, and_self]
  inv_mem' := by
    rintro a ⟨haW, s, hs⟩
    refine ⟨fun w hw => ?_, fun i => (s i)⁻¹, fun i => ⟨?_, ?_⟩⟩
    · show a.symm w = w
      rw [LinearEquiv.symm_apply_eq, haW w hw]
    · show a.symm (e i) = _
      rw [LinearEquiv.symm_apply_eq, map_smul, (hs i).1, smul_smul, Units.inv_mul, one_smul]
    · show a.symm (f i) = _
      rw [LinearEquiv.symm_apply_eq, map_smul, (hs i).2, smul_smul, inv_inv, Units.mul_inv,
        one_smul]

namespace IsHypFrame

variable {Q : QuadraticForm K V} {W : Submodule K V} {n : ℕ} {e f : Fin n → V}

section Torus

variable {k : V →ₗ[K] V} {t : Fin n → Kˣ}

theorem apply_eq_of_scale (hkW : ∀ w ∈ W, k w = w)
    (ht : ∀ i, k (e i) = (t i : K) • e i ∧ k (f i) = (((t i)⁻¹ : Kˣ) : K) • f i)
    (hF : IsHypFrame Q W e f) (v : V) :
    k v = (v - frameSum Q e f v) + ∑ j, (((t j : K) * polar Q v (f j)) • e j +
      ((((t j)⁻¹ : Kˣ) : K) * polar Q v (e j)) • f j) := by
  conv_lhs => rw [← add_sub_cancel (frameSum Q e f v) v]
  rw [map_add, hkW _ (hF.proj_mem v), add_comm]
  simp only [frameSum, map_sum, map_add, map_smul, (ht _).1, (ht _).2, smul_smul, mul_comm]

theorem polar_apply_f_of_scale (hkW : ∀ w ∈ W, k w = w)
    (ht : ∀ i, k (e i) = (t i : K) • e i ∧ k (f i) = (((t i)⁻¹ : Kˣ) : K) • f i)
    (hF : IsHypFrame Q W e f) (v : V) (j : Fin n) :
    polar Q (k v) (f j) = (t j : K) * polar Q v (f j) := by
  rw [apply_eq_of_scale hkW ht hF, polar_add_left, ((hF.mem_iff _).1 (hF.proj_mem v) j).2,
    zero_add, hF.polar_sum_f]

theorem polar_apply_e_of_scale (hkW : ∀ w ∈ W, k w = w)
    (ht : ∀ i, k (e i) = (t i : K) • e i ∧ k (f i) = (((t i)⁻¹ : Kˣ) : K) • f i)
    (hF : IsHypFrame Q W e f) (v : V) (j : Fin n) :
    polar Q (k v) (e j) = (((t j)⁻¹ : Kˣ) : K) * polar Q v (e j) := by
  rw [apply_eq_of_scale hkW ht hF, polar_add_left, ((hF.mem_iff _).1 (hF.proj_mem v) j).1,
    zero_add, hF.polar_sum_e]

/-- Eigenvectors of a torus element `k` for an eigenvalue `c ≠ 1` lie in the span of the frame, and
only meet the coordinates `fⱼ` (resp. `eⱼ`) with `tⱼ = c` (resp. `tⱼ⁻¹ = c`). -/
theorem eigen_of_scale (hkW : ∀ w ∈ W, k w = w)
    (ht : ∀ i, k (e i) = (t i : K) • e i ∧ k (f i) = (((t i)⁻¹ : Kˣ) : K) • f i)
    (hF : IsHypFrame Q W e f) {c : K} {v : V} (hv : k v = c • v) (hc : c ≠ 1) :
    v = frameSum Q e f v ∧ (∀ j, polar Q v (f j) ≠ 0 → c = t j) ∧
      (∀ j, polar Q v (e j) ≠ 0 → c = (((t j)⁻¹ : Kˣ) : K)) := by
  refine ⟨?_, fun j hj => ?_, fun j hj => ?_⟩
  · have h1 := apply_eq_of_scale hkW ht hF v
    have h2 : frameSum Q e f (k v) = ∑ j, (((t j : K) * polar Q v (f j)) • e j +
        ((((t j)⁻¹ : Kˣ) : K) * polar Q v (e j)) • f j) := by
      simp only [frameSum, polar_apply_f_of_scale hkW ht hF, polar_apply_e_of_scale hkW ht hF]
    have h3 : frameSum Q e f (c • v) = c • frameSum Q e f v := by
      simp only [frameSum, polar_smul_left, Finset.smul_sum, smul_add, smul_smul, smul_eq_mul]
    rw [hv, h3] at h2
    rw [← h2, hv] at h1
    have h4 : (c - 1) • (v - frameSum Q e f v) = 0 := by
      rw [sub_smul, one_smul, smul_sub]
      rw [h1]
      abel
    rw [← sub_eq_zero]
    exact (smul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 hc)
  · have h := polar_apply_f_of_scale hkW ht hF v j
    rw [hv, polar_smul_left, smul_eq_mul] at h
    exact mul_right_cancel₀ hj h
  · have h := polar_apply_e_of_scale hkW ht hF v j
    rw [hv, polar_smul_left, smul_eq_mul] at h
    exact mul_right_cancel₀ hj h

/-- An isometry `h` fixing `W` and commuting with a *regular* element `k` of the torus
(`tᵢ ≠ 1`, the `tᵢ` distinct, `tᵢ tⱼ ≠ 1`, in particular `tᵢ² ≠ 1`) lies in the torus. -/
theorem mem_hypTorus_of_commute (hF : IsHypFrame Q W e f) {k h : V ≃ₗ[K] V}
    (hkW : ∀ w ∈ W, k w = w)
    (ht : ∀ i, k (e i) = (t i : K) • e i ∧ k (f i) = (((t i)⁻¹ : Kˣ) : K) • f i)
    (h1 : ∀ i, (t i : K) ≠ 1) (hinj : ∀ i j, (t i : K) = t j → i = j)
    (hinv : ∀ i j, (t i : K) * t j ≠ 1)
    (hh : ∀ u v, polar Q (h u) (h v) = polar Q u v) (hW : ∀ w ∈ W, h w = w) (hc : Commute k h) :
    h ∈ hypTorus W e f := by
  have hkc : ∀ v, k (h v) = h (k v) := fun v => by
    rw [← LinearEquiv.mul_apply, hc.eq, LinearEquiv.mul_apply]
  have hinv' : ∀ i j, (((t i)⁻¹ : Kˣ) : K) = (((t j)⁻¹ : Kˣ) : K) → i = j := fun i j hij =>
    hinj i j (by simpa using congrArg (·⁻¹) hij)
  have hti : ∀ i j, (((t i)⁻¹ : Kˣ) : K) = t j → False := fun i j hij => hinv i j (by
    rw [← hij, Units.mul_inv])
  have htj : ∀ i j, (t i : K) = (((t j)⁻¹ : Kˣ) : K) → False := fun i j hij => hinv i j (by
    rw [hij, Units.inv_mul])
  -- `h eᵢ = c eᵢ`
  have hE : ∀ i, h (e i) = polar Q (h (e i)) (f i) • e i := fun i => by
    have hv : (k : V →ₗ[K] V) (h (e i)) = (t i : K) • h (e i) := by
      simp [hkc, (ht i).1]
    obtain ⟨hs, hfj, hej⟩ := eigen_of_scale (k := (k : V →ₗ[K] V)) hkW ht hF hv (h1 i)
    refine hs.trans ?_
    unfold frameSum
    rw [Finset.sum_eq_single i]
    · have : polar Q (h (e i)) (e i) = 0 := by_contra fun h0 => htj i i (hej i h0)
      rw [this, zero_smul, add_zero]
    · intro j _ hji
      have a : polar Q (h (e i)) (f j) = 0 := by_contra fun h0 => hji (hinj _ _ (hfj j h0)).symm
      have b : polar Q (h (e i)) (e j) = 0 := by_contra fun h0 => htj i j (hej j h0)
      rw [a, b, zero_smul, zero_smul, add_zero]
    · simp
  have hFf : ∀ i, h (f i) = polar Q (h (f i)) (e i) • f i := fun i => by
    have hv : (k : V →ₗ[K] V) (h (f i)) = (((t i)⁻¹ : Kˣ) : K) • h (f i) := by
      simp [hkc, (ht i).2]
    have hne : (((t i)⁻¹ : Kˣ) : K) ≠ 1 := fun h0 => h1 i (by simpa using congrArg (·⁻¹) h0)
    obtain ⟨hs, hfj, hej⟩ := eigen_of_scale (k := (k : V →ₗ[K] V)) hkW ht hF hv hne
    refine hs.trans ?_
    unfold frameSum
    rw [Finset.sum_eq_single i]
    · have : polar Q (h (f i)) (f i) = 0 := by_contra fun h0 => hti i i (hfj i h0)
      rw [this, zero_smul, zero_add]
    · intro j _ hji
      have a : polar Q (h (f i)) (f j) = 0 := by_contra fun h0 => hti i j (hfj j h0)
      have b : polar Q (h (f i)) (e j) = 0 := by_contra fun h0 => hji (hinv' _ _ (hej j h0)).symm
      rw [a, b, zero_smul, zero_smul, add_zero]
    · simp
  have hcc : ∀ i, polar Q (h (e i)) (f i) * polar Q (h (f i)) (e i) = 1 := fun i => by
    have := hh (e i) (f i)
    rw [hE i, hFf i, polar_smul_left, polar_smul_right] at this
    simp only [hF.polar_ef, ↓reduceIte] at this
    simpa [smul_eq_mul, mul_comm] using this
  refine ⟨hW, fun i => ⟨polar Q (h (e i)) (f i), polar Q (h (f i)) (e i), hcc i,
    by rw [mul_comm]; exact hcc i⟩, fun i => ⟨hE i, ?_⟩⟩
  exact hFf i

end Torus

end IsHypFrame

/-! ### Conjugating tori -/

section Conj

variable {W W₁ W₂ : Submodule K V} {n : ℕ} {e f e₁ f₁ e₂ f₂ : Fin n → V}

/-- An automorphism carrying the frame `(W₁, e₁, f₁)` to `(W₂, e₂, f₂)` conjugates their tori. -/
theorem hypTorus_map_conj (g : V ≃ₗ[K] V) (hW : ∀ v, g v ∈ W₂ ↔ v ∈ W₁)
    (he : ∀ i, g (e₁ i) = e₂ i) (hf : ∀ i, g (f₁ i) = f₂ i) :
    (hypTorus W₁ e₁ f₁).map (MulAut.conj g).toMonoidHom = hypTorus W₂ e₂ f₂ := by
  have hinv : ∀ v, (g⁻¹ : V ≃ₗ[K] V) v = g.symm v := fun _ => rfl
  have he' : ∀ i, g.symm (e₂ i) = e₁ i := fun i => by rw [LinearEquiv.symm_apply_eq, he]
  have hf' : ∀ i, g.symm (f₂ i) = f₁ i := fun i => by rw [LinearEquiv.symm_apply_eq, hf]
  ext h
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨h₁, ⟨hW₁, t, ht⟩, rfl⟩
    refine ⟨fun w hw => ?_, t, fun i => ⟨?_, ?_⟩⟩
    · have : g.symm w ∈ W₁ := (hW _).1 (by rwa [LinearEquiv.apply_symm_apply])
      simp only [LinearEquiv.mul_apply, hinv, hW₁ _ this, LinearEquiv.apply_symm_apply]
    · simp only [LinearEquiv.mul_apply, hinv, he', (ht i).1, map_smul, he]
    · simp only [LinearEquiv.mul_apply, hinv, hf', (ht i).2, map_smul, hf]
  · rintro ⟨hW₂, t, ht⟩
    refine ⟨g⁻¹ * h * g, ⟨fun w hw => ?_, t, fun i => ⟨?_, ?_⟩⟩, by group⟩
    · have : g w ∈ W₂ := (hW w).2 hw
      simp only [LinearEquiv.mul_apply, hinv, hW₂ _ this, LinearEquiv.symm_apply_apply]
    · simp only [LinearEquiv.mul_apply, hinv, he, (ht i).1, map_smul, he']
    · simp only [LinearEquiv.mul_apply, hinv, hf, (ht i).2, map_smul, hf']

/-- Swapping `e_{i₀}` and `f_{i₀}` does not change the torus. -/
theorem hypTorus_swap (i₀ : Fin n) :
    hypTorus W (Function.update e i₀ (f i₀)) (Function.update f i₀ (e i₀)) = hypTorus W e f := by
  have key : ∀ {e f : Fin n → V} {h : V ≃ₗ[K] V},
      h ∈ hypTorus W e f → h ∈ hypTorus W (Function.update e i₀ (f i₀))
        (Function.update f i₀ (e i₀)) := by
    rintro e f h ⟨hW, t, ht⟩
    refine ⟨hW, Function.update t i₀ (t i₀)⁻¹, fun i => ?_⟩
    by_cases hi : i = i₀
    · subst hi
      simp only [Function.update_self, inv_inv]
      exact ⟨(ht i).2, (ht i).1⟩
    · simp only [Function.update_of_ne hi]
      exact ht i
  ext h
  refine ⟨fun hh => ?_, key⟩
  have := key hh
  simpa [Function.update_idem] using this

end Conj

namespace IsHypFrame

variable {Q : QuadraticForm K V} {W W₁ W₂ : Submodule K V} {n : ℕ} {e f e₁ f₁ e₂ f₂ : Fin n → V}

variable (K) in
/-- The span of a frame. -/
abbrev span (e f : Fin n → V) : Submodule K V := Submodule.span K (Set.range (Sum.elim e f))

theorem linearIndependent (hF : IsHypFrame Q W e f) : LinearIndependent K (Sum.elim e f) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hs : ∑ j, (g (Sum.inl j) • e j + g (Sum.inr j) • f j) = 0 := by
    rw [Finset.sum_add_distrib, ← hg, Fintype.sum_sum_type]; rfl
  rintro (i | i)
  · have := hF.polar_sum_f (fun j => g (Sum.inl j)) (fun j => g (Sum.inr j)) i
    rwa [hs, polar_zero_left, eq_comm] at this
  · have := hF.polar_sum_e (fun j => g (Sum.inl j)) (fun j => g (Sum.inr j)) i
    rwa [hs, polar_zero_left, eq_comm] at this

theorem frameSum_mem_span (v : V) : frameSum Q e f v ∈ span K e f :=
  Submodule.sum_mem _ fun j _ => Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl j, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩))

/-- Vectors of the span are their own frame part. -/
theorem eq_frameSum_of_mem_span (hF : IsHypFrame Q W e f) {v : V} (hv : v ∈ span K e f) :
    v = frameSum Q e f v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i | i, rfl⟩ := hx
    · simp [frameSum, hF.polar_ef, hF.polar_ee]
    · simp [frameSum, hF.polar_fe, hF.polar_ff]
  | zero => simp [frameSum]
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [frameSum, polar_add_left, add_smul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by abel
  | smul a x _ hx =>
    conv_lhs => rw [hx]
    simp only [frameSum, polar_smul_left, Finset.smul_sum, smul_add, smul_smul, smul_eq_mul]

theorem isCompl (hF : IsHypFrame Q W e f) : IsCompl W (span K e f) := by
  refine ⟨Submodule.disjoint_def.2 fun v hW hs => ?_, Submodule.codisjoint_iff_exists_add_eq.2
    fun v => ⟨_, _, hF.proj_mem v, frameSum_mem_span v, sub_add_cancel _ _⟩⟩
  rw [hF.eq_frameSum_of_mem_span hs, frameSum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [((hF.mem_iff v).1 hW j).1, ((hF.mem_iff v).1 hW j).2, zero_smul, zero_smul, add_zero]

/-- **`dim W + 2n = dim V`.** -/
theorem finrank_add [FiniteDimensional K V] (hF : IsHypFrame Q W e f) :
    Module.finrank K W + 2 * n = Module.finrank K V := by
  rw [← Submodule.finrank_add_eq_of_isCompl hF.isCompl, finrank_span_eq_card hF.linearIndependent]
  simp [two_mul]

/-! ### Witt's extension theorem and the conjugacy of the tori -/

section Witt

theorem nondegenerate_restrict_span (hF : IsHypFrame Q W e f) :
    (Q.restrict (span K e f)).Nondegenerate := by
  refine QuadraticMap.nondegenerate_of_ker_polarBilin_eq_bot ?_
  rw [Submodule.eq_bot_iff]
  intro x hx
  have h0 : ∀ y : span K e f, polar Q x y = 0 := fun y => LinearMap.congr_fun hx y
  ext
  rw [Submodule.coe_zero, hF.eq_frameSum_of_mem_span x.2, frameSum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [h0 ⟨f j, Submodule.subset_span ⟨Sum.inr j, rfl⟩⟩,
    h0 ⟨e j, Submodule.subset_span ⟨Sum.inl j, rfl⟩⟩, zero_smul, zero_smul, add_zero]

variable [Invertible (2 : K)] [FiniteDimensional K V]

/-- Two frames of the same size are related by an isometry (Witt's extension theorem, Tau Ceti's
`QuadraticMap.IsometryEquiv.exists_extension`, applied to the spans of the frames). -/
theorem exists_isometryEquiv (hF₁ : IsHypFrame Q W₁ e₁ f₁) (hF₂ : IsHypFrame Q W₂ e₂ f₂) :
    ∃ g : Q.IsometryEquiv Q, (∀ i, g (e₁ i) = e₂ i) ∧ ∀ i, g (f₁ i) = f₂ i := by
  set b₁ := Module.Basis.span hF₁.linearIndependent
  set b₂ := Module.Basis.span hF₂.linearIndependent
  let φ : span K e₁ f₁ ≃ₗ[K] span K e₂ f₂ := b₁.equiv b₂ (Equiv.refl _)
  have hφ : ∀ i, (φ (b₁ i) : V) = Sum.elim e₂ f₂ i := fun i => by
    simp [φ, b₂, Module.Basis.span_apply]
  have hb₁ : ∀ i, (b₁ i : V) = Sum.elim e₁ f₁ i := fun i => by
    simp [b₁, Module.Basis.span_apply]
  have hpol : ∀ x y, polar Q (φ x) (φ y) = polar Q x y := by
    have : (polarBilin (Q.restrict (span K e₂ f₂))).compl₁₂ (φ : _ →ₗ[K] _) (φ : _ →ₗ[K] _) =
        polarBilin (Q.restrict (span K e₁ f₁)) := by
      refine LinearMap.BilinForm.ext_basis b₁ fun i j => ?_
      change polar Q (φ (b₁ i) : V) (φ (b₁ j)) = polar Q (b₁ i : V) (b₁ j)
      rw [hφ, hφ, hb₁, hb₁]
      rcases i with i | i <;> rcases j with j | j <;>
        simp [hF₁.polar_ee, hF₁.polar_ff, hF₁.polar_ef, hF₁.polar_fe, hF₂.polar_ee, hF₂.polar_ff,
          hF₂.polar_ef, hF₂.polar_fe]
    intro x y
    exact LinearMap.congr_fun₂ this x y
  have hQ : ∀ x, Q.restrict (span K e₂ f₂) (φ x) = Q.restrict (span K e₁ f₁) x := fun x => by
    have h := hpol x x
    rw [polar_self, polar_self, nsmul_eq_mul, nsmul_eq_mul] at h
    exact mul_left_cancel₀ (two_ne_zero' K) h
  let ψ : (Q.restrict (span K e₁ f₁)).IsometryEquiv (Q.restrict (span K e₂ f₂)) := ⟨φ, hQ⟩
  have hext := ψ.extension_apply hF₁.nondegenerate_restrict_span
  refine ⟨ψ.extension hF₁.nondegenerate_restrict_span, fun i => ?_, fun i => ?_⟩
  · have := hext (b₁ (Sum.inl i))
    rw [hb₁] at this
    exact this.trans (hφ (Sum.inl i))
  · have := hext (b₁ (Sum.inr i))
    rw [hb₁] at this
    exact this.trans (hφ (Sum.inr i))

omit [Invertible (2 : K)] [FiniteDimensional K V] in
/-- Swapping `e_{i₀}` and `f_{i₀}` gives a frame. -/
theorem swap (hF : IsHypFrame Q W e f) (i₀ : Fin n) :
    IsHypFrame Q W (Function.update e i₀ (f i₀)) (Function.update f i₀ (e i₀)) where
  polar_ee i j := by
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [hF.polar_ff, hF.polar_ef, hF.polar_fe, hF.polar_ee]
  polar_ff i j := by
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [hF.polar_ff, hF.polar_ef, hF.polar_fe, hF.polar_ee] <;>
      exact Ne.symm ‹_›
  polar_ef i j := by
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [hF.polar_ff, hF.polar_ef, hF.polar_fe, hF.polar_ee]
  mem_iff v := by
    rw [hF.mem_iff]
    refine forall_congr' fun i => ?_
    by_cases hi : i = i₀
    · subst hi; simp only [Function.update_self]; exact And.comm
    · simp only [Function.update_of_ne hi]

omit [Invertible (2 : K)] [FiniteDimensional K V] in
/-- An isometry carrying one frame to another carries the orthogonal complements. -/
theorem mem_iff_of_polar (hF₁ : IsHypFrame Q W₁ e₁ f₁) (hF₂ : IsHypFrame Q W₂ e₂ f₂)
    (g : V →ₗ[K] V) (hpol : ∀ x y, polar Q (g x) (g y) = polar Q x y)
    (he : ∀ i, g (e₁ i) = e₂ i) (hf : ∀ i, g (f₁ i) = f₂ i) (v : V) : g v ∈ W₂ ↔ v ∈ W₁ := by
  simp only [hF₁.mem_iff, hF₂.mem_iff, ← he, ← hf, hpol]

omit [Invertible (2 : K)] [FiniteDimensional K V] in
theorem polar_isometryEquiv (g : Q.IsometryEquiv Q) (x y : V) :
    polar Q (g x) (g y) = polar Q x y := by
  simp only [polar, ← map_add, g.map_app]

/-- **Frames of the same size have conjugate tori under `SO(Q)`**: an isometry of determinant `1`
carries one frame to the other (Witt's extension theorem, corrected by the reflection in
`e₀ − f₀`, which swaps `e₀` and `f₀`), so it conjugates their tori. -/
theorem exists_conj_hypTorus (hQ : (polarBilin Q).SeparatingLeft) (hF₁ : IsHypFrame Q W₁ e₁ f₁)
    (hF₂ : IsHypFrame Q W₂ e₂ f₂) :
    ∃ g : V ≃ₗ[K] V, (∀ v, Q (g v) = Q v) ∧ LinearMap.det (g : V →ₗ[K] V) = 1 ∧
      (hypTorus W₁ e₁ f₁).map (MulAut.conj g).toMonoidHom = hypTorus W₂ e₂ f₂ := by
  rcases n with _ | n
  · have hW : W₁ = W₂ := by
      ext v; rw [hF₁.mem_iff, hF₂.mem_iff]; simp
    have he : e₁ = e₂ := Subsingleton.elim _ _
    have hf : f₁ = f₂ := Subsingleton.elim _ _
    subst hW he hf
    refine ⟨1, fun _ => rfl, LinearMap.det_id, ?_⟩
    have : MulAut.conj (1 : V ≃ₗ[K] V) = 1 := map_one _
    rw [this]
    exact Subgroup.map_id _
  obtain ⟨g, hge, hgf⟩ := exists_isometryEquiv hF₁ hF₂
  have hdet : LinearMap.det (g.toLinearEquiv : V →ₗ[K] V) = 1 ∨
      LinearMap.det (g.toLinearEquiv : V →ₗ[K] V) = -1 := by
    have h := TauCeti.QuadraticMap.orthogonalDet_sq hQ ⟨g.toLinearEquiv, g.map_app⟩
    rw [QuadraticMap.orthogonalDet_apply] at h
    have h' := congrArg Units.val h
    rw [Units.val_pow_eq_pow_val, LinearEquiv.coe_det, Units.val_one] at h'
    exact sq_eq_one_iff.1 h'
  have hpolg := polar_isometryEquiv g
  rcases hdet with hdet | hdet
  · exact ⟨g.toLinearEquiv, g.map_app, hdet, hypTorus_map_conj _
      (mem_iff_of_polar hF₁ hF₂ (g.toLinearEquiv : V →ₗ[K] V) hpolg hge hgf) hge hgf⟩
  -- correct the determinant by the reflection in `e₀ − f₀`
  set a := e₂ 0 - f₂ 0 with ha
  have h2 : (2 : K) ≠ 0 := two_ne_zero' K
  have hpe : polar Q a (e₂ 0) = -1 := by
    rw [ha, polar_sub_left, hF₂.polar_ee, hF₂.polar_fe]; simp
  have hpf : polar Q a (f₂ 0) = 1 := by
    rw [ha, polar_sub_left, hF₂.polar_ff, hF₂.polar_ef]; simp
  have hQa : Q a = -1 := by
    have h := polar_self Q a
    rw [nsmul_eq_mul, Nat.cast_ofNat] at h
    have : polar Q a a = -2 := by
      rw [show polar Q a a = polar Q a (e₂ 0) - polar Q a (f₂ 0) by rw [ha, polar_sub_right], hpe,
        hpf]; ring
    rw [this] at h
    exact (mul_left_cancel₀ h2 (by linear_combination h.symm) : Q a = -1)
  have : Invertible (Q a) := invertibleOfNonzero (by rw [hQa]; exact neg_ne_zero.2 one_ne_zero)
  have hinv : ⅟(Q a) = -1 := by rw [invOf_eq_inv, hQa, inv_neg, inv_one]
  set r := TauCeti.QuadraticMap.reflection Q a
  have hr : ∀ y, r y = y - (⅟(Q a) * polar Q a y) • a := TauCeti.QuadraticMap.reflection_apply Q a
  have hrQ : ∀ y, Q (r y) = Q y :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup (Q := Q) (v := a)
  set g' : V ≃ₗ[K] V := g.toLinearEquiv.trans r
  have hg'Q : ∀ v, Q (g' v) = Q v := fun v => (hrQ _).trans (g.map_app v)
  have hg'pol : ∀ x y, polar Q (g' x) (g' y) = polar Q x y := fun x y => by
    simp only [polar, ← map_add, hg'Q]
  have hF₂' : IsHypFrame Q W₂ (Function.update e₂ 0 (f₂ 0)) (Function.update f₂ 0 (e₂ 0)) :=
    hF₂.swap 0
  have hge' : ∀ i, g' (e₁ i) = Function.update e₂ 0 (f₂ 0) i := fun i => by
    change r (g (e₁ i)) = _
    rw [hge, hr]
    by_cases hi : i = 0
    · subst hi
      rw [hpe, hinv, Function.update_self, ha]; module
    · have : polar Q a (e₂ i) = 0 := by
        rw [ha, polar_sub_left, hF₂.polar_ee, hF₂.polar_fe]; simp [hi]
      rw [this, mul_zero, zero_smul, sub_zero, Function.update_of_ne hi]
  have hgf' : ∀ i, g' (f₁ i) = Function.update f₂ 0 (e₂ 0) i := fun i => by
    change r (g (f₁ i)) = _
    rw [hgf, hr]
    by_cases hi : i = 0
    · subst hi
      rw [hpf, hinv, Function.update_self, ha]; module
    · have : polar Q a (f₂ i) = 0 := by
        rw [ha, polar_sub_left, hF₂.polar_ff, hF₂.polar_ef]; simp [Ne.symm hi]
      rw [this, mul_zero, zero_smul, sub_zero, Function.update_of_ne hi]
  refine ⟨g', hg'Q, ?_, ?_⟩
  · have hdr : LinearMap.det (r : V →ₗ[K] V) = -1 := by
      rw [← LinearEquiv.coe_det, TauCeti.QuadraticMap.det_reflection, Units.val_neg, Units.val_one]
    change LinearMap.det ((r : V →ₗ[K] V) ∘ₗ (g.toLinearEquiv : V →ₗ[K] V)) = 1
    rw [LinearMap.det_comp, hdr, hdet]; ring
  · rw [hypTorus_map_conj g' (mem_iff_of_polar hF₁ hF₂' _ hg'pol hge' hgf') hge' hgf']
    exact hypTorus_swap 0

end Witt

end IsHypFrame

end GSpinGGP
