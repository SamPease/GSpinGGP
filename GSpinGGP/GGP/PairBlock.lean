import GSpinGGP.GGP.CentralizerSign
import GSpinGGP.Foundations.IsometryDet

/-!
# Pair blocks of the centralizer of a semisimple element of `GSpin`

For `x ∈ GSpin(V)` with `P(x)` semisimple and `μ ≠ ±1`, the eigenspaces `E_μ`, `E_{μ⁻¹}` of `P(x)`
are totally isotropic and in duality. For isotropic `u, w`, the element `1 + s ι(u) ι(w)` lies in
`GSpin(V)` and acts as an explicit rank-one perturbation of the identity
(`exists_rankOne_lift`); for `u ∈ E_μ`, `w ∈ E_{μ⁻¹}` it commutes with `x`. These elements realize
every invertible endomorphism of `E_μ` (`realizes_of_det_ne_zero`), by the generation of `GL_n` by
transvections and diagonal matrices. Hence an element `g` whose image commutes with `P(x)` and is
the identity on `E₁ ⊕ E₋₁` commutes with `x` (`commute_of_fix`): this is the pair-block step of
the description of centralizers of semisimple elements (Steinberg, *Endomorphisms of linear
algebraic groups*, Thm. 8.1).
-/

namespace GSpinGGP
namespace Steinberg

open CliffordAlgebra

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem isIsom_specP (g : GSpin Q) : IsomCent.IsIsom (bform Q) (specP Q g : V →ₗ[K] V) :=
  fun u v => bform_specP g u v

theorem commute_toLinearMap {g x : GSpin Q} (h : Commute (specP Q g) (specP Q x)) :
    Commute (specP Q x : V →ₗ[K] V) (specP Q g : V →ₗ[K] V) :=
  LinearMap.ext fun v => congrArg (fun e : V ≃ₗ[K] V => e v) h.eq.symm

theorem polar_specP (g : GSpin Q) (u v : V) :
    QuadraticMap.polar Q (specP Q g u) (specP Q g v) = QuadraticMap.polar Q u v := by
  simp only [QuadraticMap.polar, ← map_add, specP_isometry]

end Steinberg

namespace PairBlock

section Alg

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]

/-- The conjugation identity behind the rank-one lifts. -/
theorem conj_identity (a b c : A) (β γ δ : K) (haa : a * a = 0) (hbb : b * b = 0)
    (hab : a * b + b * a = β • 1) (hac : a * c + c * a = γ • 1) (hbc : b * c + c * b = δ • 1)
    (s t : K) (hst : s = t + s * t * β) :
    (1 + s • (a * b)) * c * (1 + (-t) • (a * b)) = c + (s * δ) • a - (t * γ) • b := by
  have hba : b * a = β • 1 - a * b := by rw [← hab]; abel
  have hca : c * a = γ • 1 - a * c := by rw [← hac]; abel
  have hcb : c * b = δ • 1 - b * c := by rw [← hbc]; abel
  have E1 : a * b * c = δ • a - γ • b + c * (a * b) := by
    rw [mul_assoc, show b * c = δ • 1 - c * b by rw [hcb]; abel, mul_sub, mul_smul_comm, mul_one,
      ← mul_assoc, show a * c = γ • 1 - c * a by rw [hca]; abel, sub_mul, smul_mul_assoc, one_mul,
      mul_assoc]
    abel
  have E2 : a * (a * b) = 0 := by rw [← mul_assoc, haa, zero_mul]
  have E3 : b * (a * b) = β • b := by
    rw [← mul_assoc, hba, sub_mul, smul_mul_assoc, one_mul, mul_assoc, hbb, mul_zero, sub_zero]
  have E4 : a * b * (a * b) = β • (a * b) := by
    rw [mul_assoc, E3, mul_smul_comm]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, E1]
  simp only [smul_add, smul_sub, sub_mul, smul_mul_assoc, mul_assoc, E2, E3, smul_zero,
    zero_add, add_zero]
  simp only [mul_smul_comm, smul_smul]
  match_scalars
  · ring
  · ring
  · linear_combination -γ * hst
  · linear_combination hst

end Alg

open CliffordAlgebra Module

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem smul_one_eq_algebraMap (c : K) :
    c • (1 : CliffordAlgebra Q) = algebraMap K (CliffordAlgebra Q) c :=
  (Algebra.algebraMap_eq_smul_one c).symm

/-- `ι(u) ι(w) ι(v)`-identities for isotropic `u, w`, in the form used by `conj_identity`. -/
theorem conj_ι (u w v : V) (hu : Q u = 0) (hw : Q w = 0) (s t : K)
    (hst : s = t + s * t * QuadraticMap.polar Q u w) :
    (1 + s • (ι Q u * ι Q w)) * ι Q v * (1 + (-t) • (ι Q u * ι Q w)) =
      ι Q (v + (s * QuadraticMap.polar Q w v) • u - (t * QuadraticMap.polar Q u v) • w) := by
  rw [map_sub, map_add, map_smul, map_smul]
  refine conj_identity _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ s t hst
  · rw [ι_sq_scalar, hu, map_zero]
  · rw [ι_sq_scalar, hw, map_zero]
  · rw [ι_mul_ι_add_swap, smul_one_eq_algebraMap]
  · rw [ι_mul_ι_add_swap, smul_one_eq_algebraMap]
  · rw [ι_mul_ι_add_swap, smul_one_eq_algebraMap]

theorem one_add_mul_one_add (u w : V) (hu : Q u = 0) (hw : Q w = 0) (s t : K)
    (hst : s = t + s * t * QuadraticMap.polar Q u w) :
    (1 + s • (ι Q u * ι Q w)) * (1 + (-t) • (ι Q u * ι Q w)) = 1 := by
  have E4 : ι Q u * ι Q w * (ι Q u * ι Q w) =
      QuadraticMap.polar Q u w • (ι Q u * ι Q w) := by
    have hba : ι Q w * ι Q u = QuadraticMap.polar Q u w • 1 - ι Q u * ι Q w := by
      rw [smul_one_eq_algebraMap, ← ι_mul_ι_add_swap]; abel
    rw [mul_assoc, ← mul_assoc (ι Q w), hba, sub_mul, smul_mul_assoc, one_mul, mul_assoc,
      ι_sq_scalar Q w, hw, map_zero, mul_zero, sub_zero, mul_smul_comm]
  simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, E4, smul_smul]
  rw [add_assoc, add_eq_left]
  match_scalars
  linear_combination hst

/-- **Rank-one lifts**: for isotropic `u, w` and `s` with `1 + s·polar(u, w) ≠ 0`, the element
`1 + s ι(u) ι(w)` lies in `GSpin(V)`, and its image is
`v ↦ v + s polar(w, v) u − t polar(u, v) w`, where `t = s / (1 + s polar(u, w))`. -/
theorem exists_rankOne_lift (u w : V) (hu : Q u = 0) (hw : Q w = 0) (s : K)
    (hs : 1 + s * QuadraticMap.polar Q u w ≠ 0) :
    ∃ ℓ : GSpin Q, ((ℓ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = 1 + s • (ι Q u * ι Q w) ∧
      ∀ v, specP Q ℓ v = v + (s * QuadraticMap.polar Q w v) • u -
        (s / (1 + s * QuadraticMap.polar Q u w) * QuadraticMap.polar Q u v) • w := by
  set β := QuadraticMap.polar Q u w
  set t := s / (1 + s * β) with ht
  have hst : s = t + s * t * β := by rw [ht]; field_simp
  clear_value t
  have hts : -t = -s + -t * -s * β := by linear_combination hst
  let U : (CliffordAlgebra Q)ˣ := ⟨1 + s • (ι Q u * ι Q w), 1 + (-t) • (ι Q u * ι Q w),
    one_add_mul_one_add u w hu hw s t hst, by
      have := one_add_mul_one_add u w hu hw (-t) (-s) hts
      rwa [neg_neg] at this⟩
  have hp : ι Q u * ι Q w ∈ even Q := by
    rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
    exact ι_mul_ι_mem_evenOdd_zero Q u w
  have hmem : U ∈ GSpin Q := by
    refine ⟨Subalgebra.add_mem _ (Subalgebra.one_mem _) (Subalgebra.smul_mem _ hp s),
      fun v => ⟨v + (s * QuadraticMap.polar Q w v) • u - (t * QuadraticMap.polar Q u v) • w,
        (conj_ι u w v hu hw s t hst).symm⟩,
      fun v => ⟨v + (-t * QuadraticMap.polar Q w v) • u - (-s * QuadraticMap.polar Q u v) • w, ?_⟩⟩
    have := conj_ι u w v hu hw (-t) (-s) hts
    rw [neg_neg] at this
    exact this.symm
  refine ⟨⟨U, hmem⟩, rfl, fun v => ?_⟩
  apply ι_injective Q
  rw [ι_specP]
  exact conj_ι u w v hu hw s t hst

section Eigen

variable [FiniteDimensional K V] (x : GSpin Q)

theorem polar_eq_zero_of_eigen {μ ν : K} (h : μ * ν ≠ 1) {u v : V}
    (hu : u ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) μ)
    (hv : v ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) ν) :
    QuadraticMap.polar Q u v = 0 := by
  rw [polar_eq_two_mul_bform, IsomCent.bform_eigen_eq_zero (Steinberg.isIsom_specP x) h hu hv,
    mul_zero]

theorem eq_zero_of_eigen {μ : K} (h : μ * μ ≠ 1) {u : V}
    (hu : u ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) μ) : Q u = 0 := by
  rw [← QuadraticMap.associated_eq_self_apply K Q u]
  exact IsomCent.bform_eigen_eq_zero (Steinberg.isIsom_specP x) h hu hu

/-- `x` commutes with `ι(u) ι(w)` for `u ∈ E_μ`, `w ∈ E_ν`, `μ ν = 1`. -/
theorem commute_ι_mul_ι {μ ν : K} (h : μ * ν = 1) {u w : V}
    (hu : u ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) μ)
    (hw : w ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) ν) :
    ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * (ι Q u * ι Q w) =
      ι Q u * ι Q w * ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  have h1 := CentralizerSign.mul_ι_of_specP_eq_smul x (Module.End.mem_eigenspace_iff.mp hu)
  have h2 := CentralizerSign.mul_ι_of_specP_eq_smul x (Module.End.mem_eigenspace_iff.mp hw)
  rw [← mul_assoc, h1, ← Algebra.smul_def, smul_mul_assoc, mul_assoc, h2, ← Algebra.smul_def,
    mul_smul_comm, smul_smul, h, one_smul]
  simp only [mul_assoc]

/-- **Rank-one generators of a pair block.** For `u ∈ E_μ`, `w ∈ E_{μ⁻¹}` (`μ² ≠ 1`) and
`1 + s polar(u, w) ≠ 0`, some `γ ∈ GSpin(V)` commuting with `x` acts on `E_μ` as
`v ↦ v + s polar(w, v) u` and trivially on every `E_ν` with `ν ≠ μ, μ⁻¹`. -/
theorem exists_gen {μ : K} (hμ : μ * μ ≠ 1) (hμ0 : μ ≠ 0) {u w : V}
    (hu : u ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) μ)
    (hw : w ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) μ⁻¹) (s : K)
    (hs : 1 + s * QuadraticMap.polar Q u w ≠ 0) :
    ∃ γ : GSpin Q, Commute γ x ∧
      (∀ v ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) μ,
        specP Q γ v = v + (s * QuadraticMap.polar Q w v) • u) ∧
      (∀ ν, ν ≠ μ → ν ≠ μ⁻¹ → ∀ v ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) ν,
        specP Q γ v = v) := by
  have hμ' : μ⁻¹ * μ⁻¹ ≠ 1 := by
    rw [← mul_inv]; intro h; exact hμ (inv_eq_one.mp h)
  obtain ⟨γ, hγ, hP⟩ := exists_rankOne_lift u w (eq_zero_of_eigen x hμ hu)
    (eq_zero_of_eigen x hμ' hw) s hs
  refine ⟨γ, ?_, fun v hv => ?_, fun ν h1 h2 v hv => ?_⟩
  · apply Subtype.ext; apply Units.ext
    show ((γ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ((γ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
    rw [hγ, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      commute_ι_mul_ι x (mul_inv_cancel₀ hμ0) hu hw]
  · rw [hP, polar_eq_zero_of_eigen x hμ hu hv, mul_zero, zero_smul, sub_zero]
  · have e1 : μ⁻¹ * ν ≠ 1 := by
      intro h; apply h1; field_simp at h; first | exact h | exact h.symm
    have e2 : μ * ν ≠ 1 := by
      intro h; apply h2; exact (eq_inv_of_mul_eq_one_right h)
    rw [hP, polar_eq_zero_of_eigen x e1 hw hv, polar_eq_zero_of_eigen x e2 hu hv, mul_zero,
      mul_zero, zero_smul, zero_smul, add_zero, sub_zero]

/-- The eigenspace `E_μ` of `P(x)`. -/
abbrev Eig (μ : K) : Submodule K V := Module.End.eigenspace (specP Q x : V →ₗ[K] V) μ

variable [IsAlgClosed K] {x}

theorem pairing_left (hQ : IsNondeg Q) (hss : Module.End.IsSemisimple (specP Q x : V →ₗ[K] V))
    (μ : K) (w : V) (hw : w ∈ Eig x μ⁻¹) (h : ∀ v ∈ Eig x μ, QuadraticMap.polar Q w v = 0) :
    w = 0 := by
  refine (IsomCent.pairing_eigenspace ⟨fun u v => bform_comm Q u v⟩ hQ
    (Steinberg.isIsom_specP x) hss μ).1 w hw fun u hu => ?_
  have := h u hu
  rw [polar_eq_two_mul_bform, bform_comm] at this
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

theorem pairing_right (hQ : IsNondeg Q) (hss : Module.End.IsSemisimple (specP Q x : V →ₗ[K] V))
    (μ : K) (u : V) (hu : u ∈ Eig x μ) (h : ∀ w ∈ Eig x μ⁻¹, QuadraticMap.polar Q u w = 0) :
    u = 0 := by
  refine (IsomCent.pairing_eigenspace ⟨fun u v => bform_comm Q u v⟩ hQ
    (Steinberg.isIsom_specP x) hss μ).2 u hu fun w hw => ?_
  have := h w hw
  rw [polar_eq_two_mul_bform] at this
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

/-- **A dual basis of `E_{μ⁻¹}`** for a basis of `E_μ` under `polar`. -/
theorem exists_dual (hQ : IsNondeg Q) (hss : Module.End.IsSemisimple (specP Q x : V →ₗ[K] V))
    (μ : K) : ∃ w : Fin (finrank K (Eig x μ)) → V, (∀ j, w j ∈ Eig x μ⁻¹) ∧
      ∀ (v : Eig x μ) (j : Fin (finrank K (Eig x μ))),
        QuadraticMap.polar Q (w j) v = (Module.finBasis K (Eig x μ)).repr v j := by
  let Φ : Eig x μ⁻¹ →ₗ[K] Module.Dual K (Eig x μ) :=
    (QuadraticMap.polarBilin Q).compl₁₂ (Eig x μ⁻¹).subtype (Eig x μ).subtype
  let Ψ : Eig x μ →ₗ[K] Module.Dual K (Eig x μ⁻¹) :=
    (QuadraticMap.polarBilin Q).compl₁₂ (Eig x μ).subtype (Eig x μ⁻¹).subtype
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (pairing_left hQ hss μ w w.2 fun v hv => LinearMap.congr_fun hw ⟨v, hv⟩)
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    exact Subtype.ext (pairing_right hQ hss μ u u.2 fun w hw => LinearMap.congr_fun hu ⟨w, hw⟩)
  have h1 := LinearMap.finrank_le_finrank_of_injective hΦ
  have h2 := LinearMap.finrank_le_finrank_of_injective hΨ
  rw [Subspace.dual_finrank_eq] at h1 h2
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [Subspace.dual_finrank_eq]; omega)).mp hΦ
  choose w' hw' using fun j => hsurj ((Module.finBasis K (Eig x μ)).coord j)
  refine ⟨fun j => (w' j : V), fun j => (w' j).2, fun v j => ?_⟩
  have := LinearMap.congr_fun (hw' j) v
  simpa [Φ] using this

/-- `γ` realizes `L` on `E_μ` and is trivial on the other eigenspaces except `E_{μ⁻¹}`. -/
def Realizes (x : GSpin Q) (μ : K) (L : Eig x μ →ₗ[K] Eig x μ) : Prop :=
  ∃ γ : GSpin Q, Commute γ x ∧ (∀ v : Eig x μ, specP Q γ v = (L v : V)) ∧
    (∀ ν, ν ≠ μ → ν ≠ μ⁻¹ → ∀ v ∈ Eig x ν, specP Q γ v = v)

theorem realizes_id (μ : K) : Realizes x μ LinearMap.id :=
  ⟨1, Commute.one_left x, fun v => by simp, fun _ _ _ v _ => by simp⟩

theorem Realizes.comp {μ : K} {L₁ L₂ : Eig x μ →ₗ[K] Eig x μ} (h₁ : Realizes x μ L₁)
    (h₂ : Realizes x μ L₂) : Realizes x μ (L₁ ∘ₗ L₂) := by
  obtain ⟨γ₁, c₁, e₁, o₁⟩ := h₁
  obtain ⟨γ₂, c₂, e₂, o₂⟩ := h₂
  refine ⟨γ₁ * γ₂, c₁.mul_left c₂, fun v => ?_, fun ν h1 h2 v hv => ?_⟩
  · rw [map_mul, LinearEquiv.mul_apply, e₂, e₁]; rfl
  · rw [map_mul, LinearEquiv.mul_apply, o₂ ν h1 h2 v hv, o₁ ν h1 h2 v hv]

/-- The rank-one maps `v ↦ v + s polar(w, v) u` on `E_μ` are realized. -/
theorem realizes_rankOne {μ : K} (hμ : μ * μ ≠ 1) (hμ0 : μ ≠ 0) (u : Eig x μ) {w : V}
    (hw : w ∈ Eig x μ⁻¹) (s : K) (hs : 1 + s * QuadraticMap.polar Q u w ≠ 0)
    (L : Eig x μ →ₗ[K] Eig x μ)
    (hL : ∀ v : Eig x μ, (L v : V) = v + (s * QuadraticMap.polar Q w v) • (u : V)) :
    Realizes x μ L := by
  obtain ⟨γ, hc, he, ho⟩ := exists_gen x hμ hμ0 u.2 hw s hs
  exact ⟨γ, hc, fun v => by rw [he v v.2, hL], ho⟩

variable [DecidableEq K]

/-- **Every invertible endomorphism of `E_μ` is realized** (`μ² ≠ 1`): by
`Matrix.diagonal_transvection_induction_of_det_ne_zero`, from transvections and diagonal matrices,
each a rank-one map. -/
theorem realizes_of_det_ne_zero (hQ : IsNondeg Q)
    (hss : Module.End.IsSemisimple (specP Q x : V →ₗ[K] V)) {μ : K} (hμ : μ * μ ≠ 1) (hμ0 : μ ≠ 0)
    (A : Eig x μ →ₗ[K] Eig x μ) (hA : LinearMap.det A ≠ 0) : Realizes x μ A := by
  classical
  set b := Module.finBasis K (Eig x μ)
  obtain ⟨w, hw, hwb⟩ := exists_dual hQ hss μ
  have hpol : ∀ i j, QuadraticMap.polar Q (b i : V) (w j) = if i = j then 1 else 0 := by
    intro i j
    rw [QuadraticMap.polar_comm, hwb, Module.Basis.repr_self, Finsupp.single_apply]
  rw [← Matrix.toLin_toMatrix b b A]
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => Realizes x μ (Matrix.toLin b b M)) _ (by rwa [LinearMap.det_toMatrix]) ?_ ?_ ?_
  · intro D hD
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hD
    have key : ∀ S : Finset (Fin (finrank K (Eig x μ))),
        Realizes x μ (Matrix.toLin b b (Matrix.diagonal fun k => if k ∈ S then D k else 1)) := by
      intro S
      induction S using Finset.induction_on with
      | empty => simpa [Matrix.toLin_one] using realizes_id (x := x) μ
      | insert k S hk ih =>
        have hsplit : (Matrix.diagonal fun l => if l ∈ insert k S then D l else 1) =
            (Matrix.diagonal fun l => if l ∈ S then D l else 1) *
              Matrix.diagonal fun l => if l = k then D k else 1 := by
          rw [Matrix.diagonal_mul_diagonal]
          congr 1; funext l
          by_cases hl : l = k
          · subst hl; simp [hk]
          · simp [hl]
        rw [hsplit, Matrix.toLin_mul b b b]
        refine ih.comp (realizes_rankOne hμ hμ0 (b k) (hw k) (D k - 1) ?_ _ fun v => ?_)
        · rw [hpol, if_pos rfl]; have := hD k (Finset.mem_univ _); ring_nf; exact this
        · rw [hwb]
          have e : Matrix.toLin b b (Matrix.diagonal fun l => if l = k then D k else 1) =
              LinearMap.id + ((D k - 1) • b.coord k).smulRight (b k) := by
            refine b.ext fun m => ?_
            rw [Matrix.toLin_self]
            by_cases hm : m = k
            · subst hm; simp [Matrix.diagonal_apply, sub_smul]
            · simp [Matrix.diagonal_apply, hm, Finsupp.single_apply, Ne.symm hm]
          rw [e]
          simp [mul_smul]
          rfl
    simpa using key Finset.univ
  · intro t
    refine realizes_rankOne hμ hμ0 (t.c • b t.i) (hw t.j) 1 ?_ _ fun v => ?_
    · rw [Submodule.coe_smul, QuadraticMap.polar_smul_left, hpol, if_neg t.hij]; simp
    · rw [hwb]
      have e : Matrix.toLin b b t.toMatrix =
          LinearMap.id + (b.coord t.j).smulRight (t.c • b t.i) := by
        refine b.ext fun m => ?_
        rw [Matrix.toLin_self]
        by_cases hm : m = t.j
        · subst hm
          simp [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_apply,
            Matrix.one_apply, Matrix.single_apply, add_smul, Finset.sum_add_distrib]
        · simp [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_apply,
            Matrix.one_apply, Matrix.single_apply, add_smul, Finset.sum_add_distrib, hm,
            Finsupp.single_apply, Ne.symm hm]
      rw [e]
      simp [mul_smul]
      rfl
  · intro A B _ _ hA hB
    rw [Matrix.toLin_mul b b b]
    exact hA.comp hB

theorem specP_inv_fix {γ : GSpin Q} {v : V} (h : specP Q γ v = v) : specP Q γ⁻¹ v = v := by
  conv_lhs => rw [← h]
  rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

/-- **Pair blocks are sign-trivial**: if `P(g)` commutes with the semisimple `P(x)` and is the
identity on `E₁` and `E₋₁`, then `g` commutes with `x` (over an algebraically closed field). -/
theorem commute_of_fix [CharZero K] (hQ : IsNondeg Q)
    (hss : Module.End.IsSemisimple (specP Q x : V →ₗ[K] V)) (g : GSpin Q)
    (hc : Commute (specP Q g) (specP Q x))
    (h1 : ∀ v ∈ Eig x 1, specP Q g v = v) (h2 : ∀ v ∈ Eig x (-1), specP Q g v = v) :
    Commute g x := by
  classical
  have key : ∀ T : Finset K, ∀ g : GSpin Q, Commute (specP Q g) (specP Q x) →
      (∀ v ∈ Eig x 1, specP Q g v = v) → (∀ v ∈ Eig x (-1), specP Q g v = v) →
      (∀ ν, ν ∉ T → ∀ v ∈ Eig x ν, specP Q g v = v) → Commute g x := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro g _ _ _ hT
      have hall : ∀ v, specP Q g v = v := by
        intro v
        have hv : v ∈ ⨆ ν : K, Eig x ν := by rw [hss.iSup_eigenspace_eq_top]; trivial
        induction hv using Submodule.iSup_induction' with
        | mem ν y hy => exact hT ν (Finset.notMem_empty ν) y hy
        | zero => simp
        | add a b _ _ ha hb => rw [map_add, ha, hb]
      have hker : g ∈ (specP Q).ker := by
        rw [MonoidHom.mem_ker]; ext v; exact hall v
      rw [ker_specP hQ] at hker
      obtain ⟨c, rfl⟩ := hker
      apply Subtype.ext; apply Units.ext
      show algebraMap K (CliffordAlgebra Q) (c : K) * ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
        ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * algebraMap K (CliffordAlgebra Q) (c : K)
      exact Algebra.commutes _ _
    | insert μ T hμT ih =>
      intro g hc h1 h2 hT
      by_cases hμ : μ * μ = 1 ∨ μ = 0
      · refine ih g hc h1 h2 fun ν hν v hv => ?_
        by_cases hνμ : ν = μ
        · subst hνμ
          rcases hμ with hμ | rfl
          · rcases mul_self_eq_one_iff.mp hμ with rfl | rfl
            · exact h1 v hv
            · exact h2 v hv
          · rw [Module.End.mem_eigenspace_iff, zero_smul] at hv
            have : v = 0 := (specP Q x).injective (by rw [map_zero]; exact hv)
            rw [this, map_zero]
        · exact hT ν (by simp [hνμ, hν]) v hv
      push_neg at hμ
      obtain ⟨hμ1, hμ0⟩ := hμ
      have hXg := Steinberg.commute_toLinearMap hc
      have hmaps := IsomCent.mapsTo_eigenspace_of_commute hXg μ
      let A : Eig x μ →ₗ[K] Eig x μ := (specP Q g : V →ₗ[K] V).restrict hmaps
      have hA : LinearMap.det A ≠ 0 := by
        have hinj : Function.Injective A := fun a b hab => Subtype.ext
          ((specP Q g).injective (congrArg Subtype.val hab))
        have := LinearMap.isUnit_det A ((LinearMap.isUnit_iff_ker_eq_bot A).mpr
          (LinearMap.ker_eq_bot.mpr hinj))
        exact this.ne_zero
      obtain ⟨γ, hγx, hγe, hγo⟩ := realizes_of_det_ne_zero hQ hss hμ1 hμ0 A hA
      have hμ1' : (1 : K) ≠ μ := by rintro rfl; simp at hμ1
      have hμm1 : (-1 : K) ≠ μ := by rintro rfl; simp at hμ1
      have hμ1'' : (1 : K) ≠ μ⁻¹ := by intro h; exact hμ1' (inv_eq_one.mp h.symm).symm
      have hμm1' : (-1 : K) ≠ μ⁻¹ := by
        intro h; apply hμm1; rw [← inv_inv μ, ← h, inv_neg, inv_one]
      obtain ⟨g', hg'⟩ : ∃ g' : GSpin Q, g' = γ⁻¹ * g := ⟨_, rfl⟩
      have hgg : g = γ * g' := by rw [hg', mul_inv_cancel_left]
      have hfixμ : ∀ v ∈ Eig x μ, specP Q g' v = v := by
        intro v hv
        rw [hg']
        rw [map_mul, LinearEquiv.mul_apply]
        have : specP Q g v = specP Q γ v := (hγe ⟨v, hv⟩).symm
        rw [this, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
      have hc' : Commute (specP Q g') (specP Q x) := by
        rw [hg', map_mul, map_inv]
        exact (hγx.map (specP Q)).inv_left.mul_left hc
      have hfix : ∀ ν, ν ≠ μ → ν ≠ μ⁻¹ → ∀ v ∈ Eig x ν, specP Q g v = v →
          specP Q g' v = v := by
        intro ν h1ν h2ν v hv hgv
        rw [hg']
        rw [map_mul, LinearEquiv.mul_apply, hgv]
        exact specP_inv_fix (hγo ν h1ν h2ν v hv)
      have hcom : Commute g' x := by
        refine ih g' hc' (fun v hv => hfix 1 hμ1' hμ1'' v hv (h1 v hv))
          (fun v hv => hfix (-1) hμm1 hμm1' v hv (h2 v hv)) fun ν hν v hv => ?_
        by_cases h1ν : ν = μ
        · subst h1ν; exact hfixμ v hv
        by_cases h2ν : ν = μ⁻¹
        · subst h2ν
          have hmaps' := IsomCent.mapsTo_eigenspace_of_commute
            (Steinberg.commute_toLinearMap hc') μ⁻¹
          have hmem : specP Q g' v - v ∈ Eig x μ⁻¹ := sub_mem (hmaps' v hv) hv
          refine sub_eq_zero.mp (pairing_left hQ hss μ _ hmem fun u hu => ?_)
          rw [QuadraticMap.polar_sub_left, ← hfixμ u hu, Steinberg.polar_specP, hfixμ u hu,
            sub_self]
        · exact hfix ν h1ν h2ν v hv (hT ν (by simp [h1ν, hν]) v hv)
      rw [hgg]
      exact hγx.mul_left hcom
  let T : Finset K := Finset.univ.image fun μ : Module.End.Eigenvalues (specP Q x : V →ₗ[K] V) =>
    (μ : K)
  refine key T g hc h1 h2 fun ν hν v hv => ?_
  have hne : ¬ Module.End.HasEigenvalue (specP Q x : V →ₗ[K] V) ν := by
    intro h; apply hν
    exact Finset.mem_image.mpr ⟨⟨ν, h⟩, Finset.mem_univ _, rfl⟩
  rw [Module.End.hasEigenvalue_iff, not_not] at hne
  have : v = 0 := by rw [← Submodule.mem_bot K, ← hne]; exact hv
  rw [this, map_zero]

end Eigen

end PairBlock
end GSpinGGP
