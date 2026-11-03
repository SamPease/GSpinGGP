/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.GSpin

/-!
# `G(F) = GSpin(W) × GSpin(V)` is unimodular

The modular character `Δ : G → ℝ_{>0}` (Mathlib's `Measure.modularCharacter`) is a homomorphism
that is trivial on the centre (`modularCharacter_eq_one_of_mem_center`), and a group with trivial
modular character is unimodular (`isMulRightInvariant_haar_of_modularCharacter`).  For
`G = GSpin(W) × GSpin(V)` every positive character trivial on the centre is trivial
(`GGPData.monoidHom_G_eq_one`), by an elementary argument instead of `Δ = |det Ad|⁻¹`:

* for `dim U ≤ 2`, `GSpin(U)` is commutative, so `GSpin(U) × 1` is central;
* for `dim U ≥ 3`, by Cartan–Dieudonné every element of `GSpin(U)` is a scalar times a product of
  elements `u w` with `u, w` anisotropic. If `u ⊥ w`, `(u w)² = −Q(u)Q(w)` is central, so
  `Δ(u w)² = 1`. In general `Q(z) u w = (u z)(z w)`, and a suitable `z` reduces to the orthogonal
  case (`exists_anisotropic_orth_two`, `exists_anisotropic_orth_gram_ne_zero`).
-/

noncomputable section

open CliffordAlgebra Module

namespace GSpinGGP

section Modular

open MeasureTheory Measure
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- The modular character is `1` on the centre: right translation by a central element is left
translation. -/
theorem modularCharacter_eq_one_of_mem_center {z : G} (hz : z ∈ Subgroup.center G) :
    modularCharacter z = 1 := by
  borelize G
  change modularCharacterFun z = 1
  rw [modularCharacterFun_eq_haarScalarFactor haar z]
  have h : map (· * z) (haar : Measure G) = haar := by
    rw [show (· * z) = (z * ·) from funext fun g => Subgroup.mem_center_iff.1 hz g,
      map_mul_left_eq_self]
  convert haarScalarFactor_self (haar : Measure G)

/-- A group with trivial modular character is unimodular: the left Haar measure is right
invariant. -/
theorem isMulRightInvariant_haar_of_modularCharacter [MeasurableSpace G] [BorelSpace G]
    (h : ∀ g : G, modularCharacter g = 1) : (haar : Measure G).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have hreg : (map (· * g) (haar : Measure G)).Regular :=
    Regular.map (Homeomorph.mulRight g)
  rw [isMulLeftInvariant_eq_smul_of_regular (map (· * g) haar) haar,
    ← modularCharacterFun_eq_haarScalarFactor]
  have := h g
  change modularCharacterFun g = 1 at this
  rw [this, one_smul]
end Modular

section Geometry

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
/-- `b(x, x) = Q(x)`. -/
theorem bform_self_eq (x : V) : bform Q x x = Q x := QuadraticMap.associated_eq_self_apply K Q x

/-- If `P` meets its orthogonal trivially and `dim P < dim V`, then `Pᗮ` contains an anisotropic
vector. -/
theorem exists_anisotropic_mem_orthogonal (hQ : IsNondeg Q) {P : Submodule K V}
    (hP : ∀ p ∈ P, (∀ q ∈ P, bform Q q p = 0) → p = 0) (hdim : finrank K P < finrank K V) :
    ∃ y ∈ (bform Q).orthogonal P, Q y ≠ 0 := by
  have hrefl : (bform Q).IsRefl := fun x y h => by rw [bform_comm]; exact h
  have hnd : ((bform Q).restrict P).Nondegenerate := by
    refine ⟨fun p hp => Subtype.ext (hP p p.2 fun q hq => ?_), fun p hp => ?_⟩
    · have := hp ⟨q, hq⟩
      simpa [bform_comm Q q] using this
    · exact Subtype.ext (hP p p.2 fun q hq => by simpa using hp ⟨q, hq⟩)
  have hc := (bform Q).isCompl_orthogonal_of_restrict_nondegenerate hrefl hnd
  by_contra hall
  push Not at hall
  -- `Pᗮ` is totally isotropic, hence orthogonal to everything, hence `0`
  have hiso : ∀ s ∈ (bform Q).orthogonal P, ∀ s' ∈ (bform Q).orthogonal P, bform Q s s' = 0 := by
    intro s hs s' hs'
    have h := QuadraticMap.associated_apply K Q s s'
    simp only [bform] at hall ⊢
    rw [h, hall _ (add_mem hs hs'), hall s hs, hall s' hs']
    simp
  have hbot : (bform Q).orthogonal P = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    refine (isNondeg_iff Q).mp hQ s fun v => ?_
    obtain ⟨p, hp, s', hs', rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
    rw [map_add, bform_comm Q s p, (bform Q).mem_orthogonal_iff.1 hs p hp, hiso s hs s' hs',
      zero_add]
  have := Submodule.finrank_add_eq_of_isCompl hc
  rw [hbot, finrank_bot, add_zero] at this
  omega

/-- An anisotropic vector has an anisotropic orthogonal vector when `dim V ≥ 2`. -/
theorem exists_anisotropic_orth_one (hQ : IsNondeg Q) {u : V} (hu : Q u ≠ 0)
    (hn : 2 ≤ finrank K V) : ∃ y, bform Q u y = 0 ∧ Q y ≠ 0 := by
  obtain ⟨y, hy, hQy⟩ := exists_anisotropic_mem_orthogonal hQ (P := K ∙ u) (fun p hp hpp => by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hp
      have h := hpp u (Submodule.mem_span_singleton_self u)
      rw [map_smul, smul_eq_mul, bform_self_eq] at h
      rw [(mul_eq_zero.1 h).resolve_right hu, zero_smul])
    (by
      classical
      have := finrank_span_le_card (R := K) ({u} : Set V)
      simp only [Set.toFinset_singleton, Finset.card_singleton] at this
      omega)
  exact ⟨y, (bform Q).mem_orthogonal_iff.1 hy u (Submodule.mem_span_singleton_self u), hQy⟩

/-- Two vectors spanning a nondegenerate plane (`Q(u)Q(w) ≠ b(u,w)²`) have a common anisotropic
orthogonal vector when `dim V ≥ 3`. -/
theorem exists_anisotropic_orth_two (hQ : IsNondeg Q) {u w : V}
    (hG : Q u * Q w - bform Q u w ^ 2 ≠ 0) (hn : 3 ≤ finrank K V) :
    ∃ y, bform Q u y = 0 ∧ bform Q w y = 0 ∧ Q y ≠ 0 := by
  classical
  have hsymm : bform Q w u = bform Q u w := bform_comm Q w u
  obtain ⟨y, hy, hQy⟩ := exists_anisotropic_mem_orthogonal hQ (P := Submodule.span K {u, w})
    (fun p hp hpp => by
      obtain ⟨a, c, rfl⟩ := Submodule.mem_span_pair.1 hp
      have h1 := hpp u (Submodule.subset_span (by simp))
      have h2 := hpp w (Submodule.subset_span (by simp))
      simp only [map_add, map_smul, smul_eq_mul, bform_self_eq, hsymm] at h1 h2
      -- the Gram system `[[Qu, b],[b, Qw]] (a, c) = 0` is nonsingular
      have ha : a * (Q u * Q w - bform Q u w ^ 2) = 0 := by
        linear_combination Q w * h1 - bform Q u w * h2
      have hc : c * (Q u * Q w - bform Q u w ^ 2) = 0 := by
        linear_combination Q u * h2 - bform Q u w * h1
      rw [(mul_eq_zero.1 ha).resolve_right hG, (mul_eq_zero.1 hc).resolve_right hG, zero_smul,
        zero_smul, add_zero])
    (by
      have := finrank_span_le_card (R := K) ({u, w} : Set V)
      rw [Set.toFinset_insert, Set.toFinset_singleton] at this
      have := Finset.card_insert_le u {w}
      simp only [Finset.card_singleton] at this
      omega)
  exact ⟨y, (bform Q).mem_orthogonal_iff.1 hy u (Submodule.subset_span (by simp)),
    (bform Q).mem_orthogonal_iff.1 hy w (Submodule.subset_span (by simp)), hQy⟩


/-- Given anisotropic `u`, `w` and `dim V ≥ 3`, some anisotropic `z ⊥ u` spans a nondegenerate plane
with `w`. -/
theorem exists_anisotropic_orth_gram_ne_zero [CharZero K] (hQ : IsNondeg Q) {u w : V}
    (hu : Q u ≠ 0) (hw : Q w ≠ 0) (hn : 3 ≤ finrank K V) :
    ∃ z, bform Q u z = 0 ∧ Q z ≠ 0 ∧ Q z * Q w - bform Q z w ^ 2 ≠ 0 := by
  obtain ⟨e₁, hue₁, he₁⟩ := exists_anisotropic_orth_one hQ hu (by omega)
  obtain ⟨e₂, hue₂, he₁e₂, he₂⟩ := exists_anisotropic_orth_two hQ (u := u) (w := e₁)
    (by rw [hue₁]; simpa using mul_ne_zero hu he₁) hn
  -- `z = e₁ + t e₂`
  have hQz : ∀ t : K, Q (e₁ + t • e₂) = Q e₁ + t ^ 2 * Q e₂ := fun t => by
    rw [← bform_self_eq, ← bform_self_eq e₁, ← bform_self_eq e₂]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, he₁e₂,
      bform_comm Q e₂ e₁]
    ring
  have hbz : ∀ t : K, bform Q (e₁ + t • e₂) w = bform Q e₁ w + t * bform Q e₂ w := fun t => by
    simp [map_add, map_smul]
  have hbu : ∀ t : K, bform Q u (e₁ + t • e₂) = 0 := fun t => by
    simp [map_add, map_smul, hue₁, hue₂]
  by_cases h₁ : Q e₁ * Q w - bform Q e₁ w ^ 2 = 0
  · by_cases h₂ : Q e₂ * Q w - bform Q e₂ w ^ 2 = 0
    · have hb₁ : bform Q e₁ w ≠ 0 := fun h => by
        rw [h] at h₁; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          sub_zero, mul_eq_zero, he₁, hw, or_self] at h₁
      have hb₂ : bform Q e₂ w ≠ 0 := fun h => by
        rw [h] at h₂; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          sub_zero, mul_eq_zero, he₂, hw, or_self] at h₂
      by_cases h₃ : Q e₁ + Q e₂ = 0
      · refine ⟨e₁ + (2 : K) • e₂, hbu 2, ?_, ?_⟩
        · rw [hQz]
          have : Q e₁ + 2 ^ 2 * Q e₂ = 3 * Q e₂ := by linear_combination h₃
          rw [this]
          exact mul_ne_zero (by norm_num) he₂
        · rw [hQz, hbz]
          have : (Q e₁ + 2 ^ 2 * Q e₂) * Q w - (bform Q e₁ w + 2 * bform Q e₂ w) ^ 2 =
              -4 * (bform Q e₁ w * bform Q e₂ w) := by
            linear_combination h₁ + 4 * h₂
          rw [this]
          exact mul_ne_zero (by norm_num) (mul_ne_zero hb₁ hb₂)
      · refine ⟨e₁ + (1 : K) • e₂, hbu 1, ?_, ?_⟩
        · rw [hQz]; simpa using h₃
        · rw [hQz, hbz]
          have : (Q e₁ + 1 ^ 2 * Q e₂) * Q w - (bform Q e₁ w + 1 * bform Q e₂ w) ^ 2 =
              -2 * (bform Q e₁ w * bform Q e₂ w) := by
            linear_combination h₁ + h₂
          rw [this]
          exact mul_ne_zero (by norm_num) (mul_ne_zero hb₁ hb₂)
    · exact ⟨e₂, hue₂, he₂, h₂⟩
  · exact ⟨e₁, hue₁, he₁, h₁⟩

end Geometry


section Hom

open scoped NNReal

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem nnreal_eq_one_of_sq_eq_one {x : ℝ≥0} (h : x ^ 2 = 1) : x = 1 :=
  NNReal.eq ((pow_eq_one_iff_of_nonneg x.2 two_ne_zero).1 (by
    have := congrArg NNReal.toReal h
    simpa using this))

omit [Invertible (2 : K)] [FiniteDimensional K V] in
/-- The value of `scalarGSpin`. -/
theorem coe_scalarGSpin (c : Kˣ) :
    (((scalarGSpin Q c : GSpin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap K (CliffordAlgebra Q) c := rfl

omit [FiniteDimensional K V] in
/-- `b(u, w) = 0` implies `polar Q u w = 0`. -/
theorem polar_eq_zero_of_bform {u w : V} (h : bform Q u w = 0) :
    QuadraticMap.polar Q u w = 0 := by
  have := congr($(QuadraticMap.two_nsmul_associated K Q) u w)
  rw [← QuadraticMap.polarBilin_apply_apply, ← this]
  simp only [LinearMap.smul_apply, bform] at h ⊢
  rw [show (QuadraticMap.associatedHom K) Q = QuadraticMap.associated Q from rfl, h, smul_zero]

variable (f : GSpin Q →* ℝ≥0) (hf : ∀ c, f (scalarGSpin Q c) = 1)
include hf

omit [FiniteDimensional K V] in
/-- For `u ⊥ w`, `(u w)² = −Q(u)Q(w)` is a scalar, so a positive character kills `u w`. -/
theorem monoidHom_gspinPair_of_orth {u w : V} (hu : Q u ≠ 0) (hw : Q w ≠ 0)
    (huw : bform Q u w = 0) : f (gspinPair Q hu hw) = 1 := by
  have hsq : gspinPair Q hu hw * gspinPair Q hu hw =
      scalarGSpin Q (Units.mk0 (-(Q u * Q w)) (neg_ne_zero.2 (mul_ne_zero hu hw))) := by
    apply Subtype.ext; apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_gspinPair, coe_scalarGSpin, Units.val_mk0]
    have hc : ι Q w * ι Q u = -(ι Q u * ι Q w) := by
      rw [ι_mul_ι_comm, bform_comm] at *
      rw [polar_eq_zero_of_bform (bform_comm Q u w ▸ huw), map_zero, zero_sub]
    calc ι Q u * ι Q w * (ι Q u * ι Q w) = ι Q u * (ι Q w * ι Q u) * ι Q w := by
          simp only [mul_assoc]
      _ = -(ι Q u * ι Q u * (ι Q w * ι Q w)) := by rw [hc]; noncomm_ring
      _ = _ := by rw [ι_sq_scalar, ι_sq_scalar, ← map_mul, ← map_neg]
  apply nnreal_eq_one_of_sq_eq_one
  rw [sq, ← map_mul, hsq, hf]

omit [Invertible (2 : K)] [FiniteDimensional K V] in
/-- `Q(z) u w = (u z)(z w)`. -/
theorem monoidHom_gspinPair_split {u w z : V} (hu : Q u ≠ 0) (hw : Q w ≠ 0) (hz : Q z ≠ 0) :
    f (gspinPair Q hu hw) = f (gspinPair Q hu hz) * f (gspinPair Q hz hw) := by
  have h : scalarGSpin Q (Units.mk0 (Q z) hz) * gspinPair Q hu hw =
      gspinPair Q hu hz * gspinPair Q hz hw := by
    apply Subtype.ext; apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_gspinPair, coe_scalarGSpin, Units.val_mk0]
    rw [show ι Q u * ι Q z * (ι Q z * ι Q w) = ι Q u * (ι Q z * ι Q z) * ι Q w by
      simp only [mul_assoc], ι_sq_scalar, ← Algebra.commutes, mul_assoc]
  rw [← map_mul, ← h, map_mul, hf, one_mul]


/-- A positive character of `GSpin(V)` trivial on the scalars kills every `u w` (`dim V ≥ 3`). -/
theorem monoidHom_gspinPair_eq_one [CharZero K] (hQ : IsNondeg Q) (hn : 3 ≤ finrank K V)
    {u w : V} (hu : Q u ≠ 0) (hw : Q w ≠ 0) : f (gspinPair Q hu hw) = 1 := by
  have hnd : ∀ {a b : V} (ha : Q a ≠ 0) (hb : Q b ≠ 0), Q a * Q b - bform Q a b ^ 2 ≠ 0 →
      f (gspinPair Q ha hb) = 1 := by
    intro a b ha hb hG
    obtain ⟨y, hay, hby, hy⟩ := exists_anisotropic_orth_two hQ hG hn
    rw [monoidHom_gspinPair_split f hf ha hb hy, monoidHom_gspinPair_of_orth f hf ha hy hay,
      monoidHom_gspinPair_of_orth f hf hy hb (by rw [bform_comm]; exact hby), one_mul]
  obtain ⟨z, huz, hz, hG⟩ := exists_anisotropic_orth_gram_ne_zero hQ hu hw hn
  rw [monoidHom_gspinPair_split f hf hu hw hz, monoidHom_gspinPair_of_orth f hf hu hz huz,
    hnd hz hw hG, one_mul]

/-- **A positive character of `GSpin(V)` trivial on the scalars is trivial** (`dim V ≥ 3`): by
Cartan–Dieudonné every element is a scalar times a product of elements `u w`. -/
theorem monoidHom_gspin_eq_one [CharZero K] (hQ : IsNondeg Q) (hn : 3 ≤ finrank K V)
    (g : GSpin Q) : f g = 1 := by
  have key : ∀ l : List (V × V), (∀ p ∈ l, Q p.1 ≠ 0 ∧ Q p.2 ≠ 0) →
      ∃ x : GSpin Q, f x = 1 ∧ (specP Q x : V →ₗ[K] V) =
        (l.map fun p => quadReflection Q p.1 * quadReflection Q p.2).prod := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨1, map_one f, by simp; rfl⟩
    | cons p l ih =>
      intro h
      obtain ⟨x, hx1, hx⟩ := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
      obtain ⟨h1, h2⟩ := h p List.mem_cons_self
      refine ⟨gspinPair Q h1 h2 * x, by
        rw [map_mul, monoidHom_gspinPair_eq_one f hf hQ hn, hx1, one_mul], ?_⟩
      rw [List.map_cons, List.prod_cons, ← hx, ← specP_gspinPair Q h1 h2, map_mul]
      rfl
  obtain ⟨l, hl, hgl⟩ := cartan_dieudonne_even Q hQ (specP Q g) (specP_isometry g) (det_specP g)
  obtain ⟨x, hx1, hx⟩ := key l hl
  have hk : g * x⁻¹ ∈ (specP Q).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv,
      LinearEquiv.toLinearMap_injective (hgl.trans hx.symm), mul_inv_cancel]
  rw [ker_specP hQ] at hk
  obtain ⟨c, hc⟩ := hk
  rw [show g = scalarGSpin Q c * x by rw [hc, inv_mul_cancel_right], map_mul, hf, hx1, one_mul]

end Hom


section Small

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [Invertible (2 : K)] in
/-- Even elements of the Clifford algebra of a space of dimension `≤ 1` are scalars. -/
theorem even_eq_algebraMap_of_finrank_le_one (hV : finrank K V ≤ 1) {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q 0) : ∃ c, x = algebraMap K _ c := by
  obtain ⟨e, he⟩ := finrank_le_one_iff.1 hV
  choose co hco using he
  have hι : ∀ u : V, ι Q u = co u • ι Q e := fun u => by rw [← map_smul, hco]
  induction x, hx using even_induction with
  | algebraMap r => exact ⟨r, rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, (map_add _ _ _).symm⟩
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
    obtain ⟨c, rfl⟩ := hx
    refine ⟨co m₁ * co m₂ * Q e * c, ?_⟩
    rw [hι m₁, hι m₂, smul_mul_smul_comm, ι_sq_scalar, smul_mul_assoc, ← map_mul,
      Algebra.smul_def, ← map_mul]
    congr 1
    ring

/-- `GSpin(V)` is commutative when `dim V ≤ 2`. -/
theorem GSpin_mul_comm_of_finrank_le_two (hV : finrank K V ≤ 2) (g h : GSpin Q) :
    g * h = h * g := by
  rcases Nat.lt_or_ge (finrank K V) 2 with h1 | h2
  · obtain ⟨a, ha⟩ :=
      even_eq_algebraMap_of_finrank_le_one (by omega) (mem_evenOdd_zero_of_mem_GSpin g)
    apply Subtype.ext; apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, ha]
    exact Algebra.commutes a _
  · exact isComm_GSpin_of_finrank_eq_two (by omega) g h

end Small


section GGP

variable {K : Type*} [Field K] [Invertible (2 : K)] [CharZero K]

/-- A positive character of `GSpin(U)` trivial on its central elements is trivial (for `dim U ≤ 2`
the group is commutative; otherwise `monoidHom_gspin_eq_one`). -/
theorem monoidHom_gspin_eq_one_of_central {U : Type*} [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] {QU : QuadraticForm K U} (hQ : IsNondeg QU) (φ : GSpin QU →* NNReal)
    (h : ∀ x : GSpin QU, (∀ y, x * y = y * x) → φ x = 1) (x : GSpin QU) : φ x = 1 := by
  rcases le_or_gt (finrank K U) 2 with h2 | h3
  · exact h x fun y => GSpin_mul_comm_of_finrank_le_two h2 x y
  · exact monoidHom_gspin_eq_one φ (fun c => h _ fun y =>
      (Subgroup.mem_center_iff.1 (scalarGSpin_mem_center QU c) y).symm) hQ h3 x

/-- **A positive character of `G(K) = GSpin(W) × GSpin(V)` trivial on the centre is trivial.** -/
theorem GGPData.monoidHom_G_eq_one (d : GGPData K) (f : d.G →* NNReal)
    (hf : ∀ z ∈ Subgroup.center d.G, f z = 1) (g : d.G) : f g = 1 := by
  have hg : g = d.pair (d.fst g, 1) * d.pair (1, d.snd g) := by
    refine d.G_ext ?_ ?_ <;> simp [map_mul, d.fst_pair, d.snd_pair]
  rw [hg, map_mul]
  have hW := monoidHom_gspin_eq_one_of_central d.nondeg
    (f.comp (d.pair.comp (MonoidHom.inl _ _))) (fun x hx => hf _ (Subgroup.mem_center_iff.2
      fun y => d.G_ext (by simp [map_mul, d.fst_pair, hx]) (by simp [map_mul, d.snd_pair])))
    (d.fst g)
  have hV := monoidHom_gspin_eq_one_of_central d.nondeg_QV
    (f.comp (d.pair.comp (MonoidHom.inr _ _))) (fun x hx => hf _ (Subgroup.mem_center_iff.2
      fun y => d.G_ext (by simp [map_mul, d.fst_pair]) (by simp [map_mul, d.snd_pair, hx])))
    (d.snd g)
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply] at hW hV
  rw [hW, hV, one_mul]

end GGP

end GSpinGGP
