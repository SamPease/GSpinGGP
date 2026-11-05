import GSpinGGP.Foundations.GSpin
import TauCeti.LinearAlgebra.QuadraticForm.Witt.Cancellation
import TauCeti.LinearAlgebra.QuadraticForm.Representation
import TauCeti.LinearAlgebra.Matrix.ToQuadraticForm
import TauCeti.LinearAlgebra.QuadraticForm.Witt.TotallyIsotropic
import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.SpecialOrthogonal

/-!
# Witt cancellation and Cartan–Dieudonné, from Tau Ceti

Two classical facts about quadratic forms over a field `K` with `2` invertible, derived from
their proofs in the Tau Ceti library (`TauCeti.equivalent_of_equivalent_prod`,
`TauCeti.QuadraticMap.exists_even_reflectionOrthogonal_list_prod_eq`):

* `witt_cancellation`: `U ⊥ X ≅ U ⊥ Y` implies `X ≅ Y`, for arbitrary (possibly degenerate)
  finite-dimensional forms (Lam, *Introduction to Quadratic Forms over Fields*, Ch. I §4).
  Tau Ceti proves it for a nondegenerate `U`; the general case follows by splitting off radicals.
* `cartan_dieudonne_even`: an element of `SO(Q)` is a product of pairs of reflections in
  anisotropic vectors (E. Artin, *Geometric Algebra*, Ch. III).

Also `isNondeg_iff_nondegenerate`: `IsNondeg` is Mathlib's `QuadraticMap.Nondegenerate`.
-/

noncomputable section

open QuadraticMap Module

namespace GSpinGGP

/-! ## Hyperbolic spaces -/

section Hyperbolic

variable {K : Type*} [Field K]

/-- Gram matrix of the hyperbolic space `H^n` of dimension `2n`: `b(e_i, e_j) = [i + j = 2n-1]`
(an orthogonal sum of `n` hyperbolic planes, written with an antidiagonal Gram matrix). -/
def hypMatrix (K : Type*) [Field K] (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) K :=
  fun i j => if (i : ℕ) + (j : ℕ) + 1 = 2 * n then 1 else 0

/-- The hyperbolic quadratic space `H^n` on `K^{2n}` (Lam Ch. I §3), `q(v) = vᵀ (hypMatrix n) v`. -/
def hypForm (K : Type*) [Field K] (n : ℕ) : QuadraticForm K (Fin (2 * n) → K) :=
  Matrix.toQuadraticForm' (hypMatrix K n)

namespace LeviAux

theorem hypForm_apply (n : ℕ) (v : Fin (2 * n) → K) :
    hypForm K n v = ∑ i, v i * v i.rev := by
  unfold hypForm Matrix.toQuadraticForm'
  simp only [LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply', dotProduct,
    Matrix.mulVec, hypMatrix]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single i.rev]
  · have h : (i : ℕ) + (i.rev : ℕ) + 1 = 2 * n := by simp [Fin.val_rev]; omega
    simp only [h, ↓reduceIte, one_mul]
  · intro j _ hj
    have h : ¬ ((i : ℕ) + (j : ℕ) + 1 = 2 * n) := by
      intro h; apply hj; ext; simp [Fin.val_rev]; omega
    simp only [h, ↓reduceIte, zero_mul, mul_zero]
  · simp

/-- The block permutation `Fin (2a) ⊕ Fin (2b) → Fin (2(a+b))`: the outer block carries `H^a`,
the middle block `H^b`. -/
def hypBlock (a b : ℕ) : Fin (2 * a) ⊕ Fin (2 * b) → Fin (2 * (a + b))
  | Sum.inl i => ⟨if (i : ℕ) < a then i else i + 2 * b, by split_ifs <;> omega⟩
  | Sum.inr j => ⟨a + j, by omega⟩

theorem hypBlock_injective (a b : ℕ) : Function.Injective (hypBlock a b) := by
  rintro (i | i) (j | j) h <;> simp only [hypBlock, Fin.mk.injEq] at h
  · congr 1; ext; split_ifs at h <;> omega
  · split_ifs at h <;> omega
  · split_ifs at h <;> omega
  · congr 1; ext; omega

def hypBlockEquiv (a b : ℕ) : Fin (2 * a) ⊕ Fin (2 * b) ≃ Fin (2 * (a + b)) :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).2
    ⟨hypBlock_injective a b, by simp; ring⟩)

theorem hypBlock_rev (a b : ℕ) (s : Fin (2 * a) ⊕ Fin (2 * b)) :
    (hypBlock a b s).rev = hypBlock a b (Sum.map Fin.rev Fin.rev s) := by
  rcases s with i | j
  · ext; simp only [hypBlock, Fin.val_rev, Sum.map_inl]; split_ifs <;> omega
  · ext; simp only [hypBlock, Fin.val_rev, Sum.map_inr]; omega

/-- `H^{a+b} ≅ H^a ⊥ H^b`. -/
def hypAddEquiv (a b : ℕ) :
    ((hypForm K a).prod (hypForm K b)).IsometryEquiv (hypForm K (a + b)) where
  toLinearEquiv := (LinearEquiv.sumArrowLequivProdArrow _ _ K K).symm.trans
    (LinearEquiv.funCongrLeft K K (hypBlockEquiv a b).symm)
  map_app' v := by
    obtain ⟨v₁, v₂⟩ := v
    rw [hypForm_apply]
    simp only [QuadraticMap.prod_apply, hypForm_apply]
    rw [← (hypBlockEquiv a b).sum_comp, Fintype.sum_sum_type]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;>
      simp [LinearMap.funLeft, hypBlockEquiv, hypBlock_rev, LinearEquiv.sumArrowLequivProdArrow,
        Equiv.sumArrowEquivProdArrow_symm_apply_inl, Equiv.sumArrowEquivProdArrow_symm_apply_inr]

end LeviAux

end Hyperbolic

variable {K : Type*} [Field K] [Invertible (2 : K)]

theorem isNondeg_iff_nondegenerate {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) :
    IsNondeg Q ↔ Q.Nondegenerate :=
  QuadraticMap.nondegenerate_associated_iff (Q := Q)

/-- The bilinear form of `H^n` on the standard basis: `b(e_i, e_j) = [i + j + 1 = 2n]`. -/
theorem bform_hypForm_single (n : ℕ) (i j : Fin (2 * n)) :
    bform (hypForm K n) (Pi.single i 1) (Pi.single j 1) =
      if (i : ℕ) + (j : ℕ) + 1 = 2 * n then 1 else 0 := by
  have hT : (hypMatrix K n).transpose = hypMatrix K n := by
    ext a b; simp only [Matrix.transpose_apply, hypMatrix]; congr 1; apply propext; omega
  unfold hypForm Matrix.toQuadraticForm'
  dsimp only [bform, QuadraticMap.associated]
  rw [QuadraticMap.associated_left_inverse]
  · simp [Matrix.toLinearMap₂'_apply', Matrix.mulVec_single, hypMatrix]
  · intro x y
    simp only [Matrix.toLinearMap₂'_apply']
    rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hT]

section Witt

/-- The `N`-component `n ↦ e(0, n).2` of an isometry `Z₁ ⊥ N₁ ≅ Z₂ ⊥ N₂` between orthogonal sums
with zero forms `Z₁, Z₂` is an isometry `N₁ → N₂`. -/
def sndIsometryOfZeroProd {A₁ A₂ N₁ N₂ : Type*}
    [AddCommGroup A₁] [Module K A₁] [AddCommGroup A₂] [Module K A₂]
    [AddCommGroup N₁] [Module K N₁] [AddCommGroup N₂] [Module K N₂]
    {Z₁ : QuadraticForm K A₁} {Z₂ : QuadraticForm K A₂} (hZ₁ : ∀ a, Z₁ a = 0)
    (hZ₂ : ∀ a, Z₂ a = 0) {Q₁ : QuadraticForm K N₁} {Q₂ : QuadraticForm K N₂}
    (e : (Z₁.prod Q₁).IsometryEquiv (Z₂.prod Q₂)) : Q₁.Isometry Q₂ where
  toLinearMap := LinearMap.snd K A₂ N₂ ∘ₗ (e : A₁ × N₁ →ₗ[K] A₂ × N₂) ∘ₗ LinearMap.inr K A₁ N₁
  map_app' n := by
    have := e.map_app (0, n)
    simp only [QuadraticMap.prod_apply, hZ₁, hZ₂, zero_add] at this
    simpa using this

omit [Invertible (2 : K)] in
/-- If `Z₁ ⊥ N₁ ≅ Z₂ ⊥ N₂` with `Z₁, Z₂` zero forms and `N₁, N₂` nondegenerate and
finite-dimensional, then `N₁ ≅ N₂`: the component `n ↦ e(0, n).2` is an isometry with trivial
kernel in both directions. -/
theorem equivalent_of_zero_prod_equivalent {A₁ A₂ N₁ N₂ : Type*}
    [AddCommGroup A₁] [Module K A₁] [AddCommGroup A₂] [Module K A₂]
    [AddCommGroup N₁] [Module K N₁] [FiniteDimensional K N₁]
    [AddCommGroup N₂] [Module K N₂] [FiniteDimensional K N₂]
    {Z₁ : QuadraticForm K A₁} {Z₂ : QuadraticForm K A₂} (hZ₁ : ∀ a, Z₁ a = 0)
    (hZ₂ : ∀ a, Z₂ a = 0) {Q₁ : QuadraticForm K N₁} {Q₂ : QuadraticForm K N₂}
    (h₁ : Q₁.Nondegenerate) (h₂ : Q₂.Nondegenerate)
    (e : (Z₁.prod Q₁).Equivalent (Z₂.prod Q₂)) : Q₁.Equivalent Q₂ := by
  obtain ⟨e⟩ := e
  set f := sndIsometryOfZeroProd hZ₁ hZ₂ e
  set g := sndIsometryOfZeroProd hZ₂ hZ₁ e.symm
  have hf : Function.Injective f :=
    Isometry.injective_of_radical_eq_bot f h₁.radical_eq_bot
  have hg : Function.Injective g :=
    Isometry.injective_of_radical_eq_bot g h₂.radical_eq_bot
  have hdim : finrank K N₁ = finrank K N₂ :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) hf)
      (LinearMap.finrank_le_finrank_of_injective (f := g.toLinearMap) hg)
  exact ⟨{ LinearEquiv.ofInjectiveOfFinrankEq f.toLinearMap hf hdim with
    map_app' := f.map_app }⟩

/-- **Witt cancellation** for arbitrary finite-dimensional forms: `U ⊥ X ≅ U ⊥ Y ⇒ X ≅ Y`
(Lam, *Introduction to Quadratic Forms over Fields*, Ch. I §4). Splitting each form as the zero
form on its radical plus its nondegenerate quotient (`QuadraticMap.IsometryEquiv.prodRadicalLift`)
reduces it to the nondegenerate case `TauCeti.equivalent_of_equivalent_prod`. -/
theorem witt_cancellation {U X Y : Type*} [AddCommGroup U] [Module K U]
    [FiniteDimensional K U]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    (QU : QuadraticForm K U) (QX : QuadraticForm K X) (QY : QuadraticForm K Y)
    (h : Nonempty ((QU.prod QX).IsometryEquiv (QU.prod QY))) :
    Nonempty (QX.IsometryEquiv QY) := by
  classical
  obtain ⟨e⟩ := h
  set QU' := QU.lift QU.radical le_rfl
  set QX' := QX.lift QX.radical le_rfl
  set QY' := QY.lift QY.radical le_rfl
  have hU' : QU'.Nondegenerate := nondegenerate_lift_radical QU
  have hX' : QX'.Nondegenerate := nondegenerate_lift_radical QX
  have hY' : QY'.Nondegenerate := nondegenerate_lift_radical QY
  let sU := IsometryEquiv.prodRadicalLift QU
  let sX := IsometryEquiv.prodRadicalLift QX
  let sY := IsometryEquiv.prodRadicalLift QY
  have key : (((0 : QuadraticForm K QU.radical).prod (0 : QuadraticForm K QX.radical)).prod
      (QU'.prod QX')).Equivalent
      (((0 : QuadraticForm K QU.radical).prod (0 : QuadraticForm K QY.radical)).prod
      (QU'.prod QY')) :=
    ⟨(IsometryEquiv.prodProdProdComm _ _ _ _).symm.trans ((sU.prod sX).trans
      (e.trans ((sU.prod sY).symm.trans (IsometryEquiv.prodProdProdComm _ _ _ _))))⟩
  have hUX : (QU'.prod QX').Equivalent (QU'.prod QY') :=
    equivalent_of_zero_prod_equivalent (by simp) (by simp) (hU'.prod hX') (hU'.prod hY') key
  obtain ⟨eXY⟩ := TauCeti.equivalent_of_equivalent_prod hU' hUX
  have hXdim := sX.toLinearEquiv.finrank_eq
  have hYdim := sY.toLinearEquiv.finrank_eq
  have hUXY := e.toLinearEquiv.finrank_eq
  have hq := eXY.toLinearEquiv.finrank_eq
  simp only [Module.finrank_prod] at hXdim hYdim hUXY
  have hr : finrank K QX.radical = finrank K QY.radical := by omega
  let r : QX.radical ≃ₗ[K] QY.radical := LinearEquiv.ofFinrankEq _ _ hr
  let z : (0 : QuadraticForm K QX.radical).IsometryEquiv (0 : QuadraticForm K QY.radical) :=
    { r with map_app' := fun _ => rfl }
  exact ⟨sX.symm.trans ((z.prod eXY).trans sY)⟩

end Witt

section WittDecomposition

open TauCeti

/-- `H¹ ≅ ⟨1, -1⟩`: `2 u₀ u₁ = (u₀ + u₁/2)² - (u₀ - u₁/2)²`. -/
def hypOneIso : (hypForm K 1).IsometryEquiv
    (presentedForm (⟨2, ![1, -1]⟩ : RegularFormPresentation K)) where
  toLinearEquiv := LinearEquiv.ofLinearMap
    (Matrix.toLin' !![1, (2 : K)⁻¹; 1, -(2 : K)⁻¹])
    (Matrix.toLin' !![(2 : K)⁻¹, (2 : K)⁻¹; 1, -1])
    (by
      rw [← Matrix.toLin'_mul, ← Matrix.toLin'_one]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
        ring)
    (by
      rw [← Matrix.toLin'_mul, ← Matrix.toLin'_one]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
        ring)
  map_app' u := by
    rw [presentedForm_apply, LeviAux.hypForm_apply]
    simp [Fin.sum_univ_two, Matrix.mulVec, dotProduct, Fin.rev]
    field_simp
    ring

/-- Our hyperbolic space `Hᵐ` is Tau Ceti's presentation of `m` hyperbolic planes. -/
theorem hypForm_equivalent_hyperbolicPresentation (m : ℕ) :
    (hypForm K m).Equivalent (presentedForm (hyperbolicPresentation K m)) := by
  induction m with
  | zero =>
    have h₁ := (QuadraticForm.equivalent_zero_iff_finrank_eq_zero (hypForm K 0)).2 (by simp)
    have h₂ := (QuadraticForm.equivalent_zero_iff_finrank_eq_zero
      (presentedForm (hyperbolicPresentation K 0))).2
      (by
        have : IsEmpty (Fin (hyperbolicPresentation K 0).1) := by
          change IsEmpty (Fin 0); infer_instance
        exact Module.finrank_zero_of_subsingleton)
    exact h₁.trans h₂.symm
  | succ m ih =>
    have h : (hypForm K (m + 1)).Equivalent ((hypForm K 1).prod (hypForm K m)) := by
      rw [Nat.add_comm m 1]
      exact ⟨(LeviAux.hypAddEquiv 1 m).symm⟩
    obtain ⟨e⟩ := ih
    obtain ⟨h⟩ := h
    exact ⟨h.trans ((hypOneIso.prod e).trans
      (equivalent_presentedForm_append_prod (⟨2, ![1, -1]⟩ : RegularFormPresentation K)
        (hyperbolicPresentation K m)).some.symm)⟩

/-- For a nondegenerate form, `wittIndex` (the largest dimension of a totally isotropic
subspace) is Tau Ceti's Witt index of the isometry class. -/
theorem wittIndex_eq_regularFormClass_wittIndex {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    wittIndex Q = RegularFormClass.wittIndex (formClass Q hQ) := by
  apply IsGreatest.csSup_eq
  refine ⟨?_, ?_⟩
  · obtain ⟨W, -, hW, hdim⟩ :=
      QuadraticMap.IsTotallyIsotropic.exists_le_finrank_eq_wittIndex (W := ⊥) hQ
        (fun v hv => by simp_all)
    exact ⟨W, hW, hdim⟩
  · rintro n ⟨U, hU, rfl⟩
    exact QuadraticMap.IsTotallyIsotropic.finrank_le_wittIndex hQ hU

/-- **Witt decomposition** (Lam, *Introduction to Quadratic Forms over Fields*, Ch. I §4;
Thesis §5.1.4): a nondegenerate finite-dimensional quadratic space is `H^w ⊥ V_an` with `V_an`
anisotropic, where `w = wittIndex Q`. From Tau Ceti's
`QuadraticForm.exists_equivalent_hyperbolicPresentation_prod`. -/
theorem witt_decomposition {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : IsNondeg Q) :
    ∃ (k : ℕ) (Qa : QuadraticForm K (Fin k → K)), Qa.Anisotropic ∧
      Nonempty (Q.IsometryEquiv ((hypForm K (wittIndex Q)).prod Qa)) ∧
      finrank K V = 2 * wittIndex Q + k := by
  have hQ' := (isNondeg_iff_nondegenerate Q).1 hQ
  obtain ⟨p, hani, hdim, ⟨e⟩⟩ := QuadraticForm.exists_equivalent_hyperbolicPresentation_prod Q hQ'
  rw [← wittIndex_eq_regularFormClass_wittIndex Q hQ'] at hdim e
  obtain ⟨h⟩ := hypForm_equivalent_hyperbolicPresentation (K := K) (wittIndex Q)
  exact ⟨p.1, presentedForm p, hani, ⟨e.trans (h.symm.prod (QuadraticMap.IsometryEquiv.refl _))⟩, hdim⟩

end WittDecomposition

section CartanDieudonne

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The reflection `s_w(v) = v − q(w)⁻¹ polar(w, v) w` of `V` in the vector `w` (E. Artin,
*Geometric Algebra*, Ch. III §3, "symmetry"; with `polar(w, v) = 2 b(w, v)` this is the usual
`v − 2 b(v,w)/q(w) · w`).  For `q(w) = 0` the formula degenerates to the identity; it is only used
for anisotropic `w`. -/
def quadReflection (Q : QuadraticForm K V) (w : V) : V →ₗ[K] V :=
  LinearMap.id - (Q w)⁻¹ • (QuadraticMap.polarBilin Q w).smulRight w

omit [Invertible (2 : K)] in
theorem quadReflection_apply (Q : QuadraticForm K V) (w v : V) :
    quadReflection Q w v = v - (Q w)⁻¹ • QuadraticMap.polar Q w v • w := by
  simp [quadReflection, smul_smul]

omit [Invertible (2 : K)] in
/-- Tau Ceti's reflection in a vector of invertible norm is `quadReflection`. -/
theorem quadReflection_eq (Q : QuadraticForm K V) (v : V) [Invertible (Q v)] :
    ((TauCeti.QuadraticMap.reflection Q v : V ≃ₗ[K] V) : V →ₗ[K] V) = quadReflection Q v := by
  ext y
  simp [quadReflection, TauCeti.QuadraticMap.reflection_apply, invOf_eq_inv, smul_smul]

/-- A totally isotropic nondegenerate space is zero. -/
theorem eq_zero_of_isNondeg_of_forall_eq_zero {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (h : ∀ v, Q v = 0) (v : V) : v = 0 :=
  hQ.1 v fun w => by
    have h2 := polar_eq_two_mul_bform Q v w
    rw [QuadraticMap.polar, h, h, h, sub_zero, sub_zero] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left (Invertible.ne_zero 2)

omit [Invertible (2 : K)] in
theorem quadReflection_mem {Q : QuadraticForm K V} {p : Submodule K V} {u v : V} (hu : u ∈ p)
    (hv : v ∈ p) : quadReflection Q u v ∈ p := by
  rw [quadReflection_apply]
  exact p.sub_mem hv (p.smul_mem _ (p.smul_mem _ hu))

omit [Invertible (2 : K)] in
theorem quadReflection_isometry {Q : QuadraticForm K V} {u : V} (hQu : Q u ≠ 0) (v : V) :
    Q (quadReflection Q u v) = Q v := by
  have := invertibleOfNonzero hQu
  rw [← quadReflection_eq]
  exact TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q u v

omit [Invertible (2 : K)] in
theorem det_quadReflection [FiniteDimensional K V] {Q : QuadraticForm K V} {u : V} (hQu : Q u ≠ 0) :
    LinearMap.det (quadReflection Q u) = -1 := by
  have := invertibleOfNonzero hQu
  rw [← quadReflection_eq, ← LinearEquiv.coe_det, TauCeti.QuadraticMap.det_reflection]
  rfl

/-- Group an even-length product into consecutive pairs. -/
theorem exists_pairs_prod {M W : Type*} [Monoid M] (f : W → M) :
    ∀ (l : List M), Even l.length → (∀ x ∈ l, ∃ w, f w = x) →
    ∃ m : List (W × W), l.prod = (m.map fun p => f p.1 * f p.2).prod
  | [], _, _ => ⟨[], by simp⟩
  | [a], h, _ => by simp at h
  | a :: b :: t, h, hw => by
    obtain ⟨wa, rfl⟩ := hw a (by simp)
    obtain ⟨wb, rfl⟩ := hw b (by simp)
    obtain ⟨m, hm⟩ := exists_pairs_prod f t (by simpa [Nat.even_add_one] using h)
      (fun x hx => hw x (by simp [hx]))
    exact ⟨(wa, wb) :: m, by simp [hm, mul_assoc]⟩

/-- **Cartan–Dieudonné, `SO` form** (E. Artin, *Geometric Algebra*, Interscience 1957, Ch. III;
Lam, *Introduction to Quadratic Forms over Fields*, Ch. I §7): for a nondegenerate `Q`, every
isometry of determinant `1` is a product `σ = ∏ᵢ s_{uᵢ} s_{wᵢ}` of pairs of reflections in
anisotropic vectors. From Tau Ceti's even reflection factorization, grouped in pairs. -/
theorem cartan_dieudonne_even [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : IsNondeg Q) (σ : V ≃ₗ[K] V) (hσ : ∀ v, Q (σ v) = Q v)
    (hdet : LinearMap.det (σ : V →ₗ[K] V) = 1) :
    ∃ l : List (V × V), (∀ p ∈ l, Q p.1 ≠ 0 ∧ Q p.2 ≠ 0) ∧
      (σ : V →ₗ[K] V) = (l.map fun p => quadReflection Q p.1 * quadReflection Q p.2).prod := by
  classical
  have hQ' : Q.Nondegenerate := (isNondeg_iff_nondegenerate Q).1 hQ
  have hS : σ ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q := by
    refine TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff.2 ⟨fun v => hσ v, ?_⟩
    ext
    simpa [LinearEquiv.coe_det] using hdet
  obtain ⟨l, hl, -, heven, hprod⟩ :=
    TauCeti.QuadraticMap.exists_even_reflectionOrthogonal_list_prod_eq Q hQ' ⟨σ, hS⟩
  let φ : TauCeti.QuadraticMap.orthogonalGroup Q →* Module.End K V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Subgroup.subtype _)
  have hσφ : (σ : V →ₗ[K] V) = (l.map φ).prod := by
    rw [← map_list_prod, hprod]; rfl
  obtain ⟨m, hm⟩ := exists_pairs_prod (fun w : {v : V // Q v ≠ 0} => quadReflection Q w)
    (l.map φ) (by simpa using heven) (by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
      obtain ⟨v, _, rfl⟩ := hl r hr
      exact ⟨⟨v, (isUnit_of_invertible (Q v)).ne_zero⟩, (quadReflection_eq Q v).symm⟩)
  refine ⟨m.map fun p => (p.1.1, p.2.1), ?_, ?_⟩
  · simp only [List.mem_map]
    rintro _ ⟨p, -, rfl⟩
    exact ⟨p.1.2, p.2.2⟩
  · rw [hσφ, hm, List.map_map]
    rfl

end CartanDieudonne


section MatrixForm

/-! ### Quadratic forms of matrices

Round trip between a form `Q` on `R^n` and its Gram matrix `Q.toMatrix'`, through Mathlib's
`Matrix.toQuadraticForm'` (`x ↦ xᵀ M x`). -/

variable {R : Type*} [CommRing R] [Invertible (2 : R)] {n : Type*} [Fintype n] [DecidableEq n]

/-- The form of the Gram matrix of `Q` is `Q`. -/
theorem _root_.QuadraticForm.toMatrix'_toQuadraticForm' (Q : QuadraticForm R (n → R)) :
    Q.toMatrix'.toQuadraticForm' = Q := by
  rw [Matrix.toQuadraticForm', QuadraticForm.toMatrix', Matrix.toLinearMap₂'_toMatrix',
    QuadraticMap.toQuadraticMap_associated]

/-- A quadratic form on `R^n` is determined by its Gram matrix. -/
theorem _root_.QuadraticForm.toMatrix'_injective :
    Function.Injective (QuadraticForm.toMatrix' : QuadraticForm R (n → R) → Matrix n n R) :=
  fun Q₁ Q₂ h => by
    rw [← QuadraticForm.toMatrix'_toQuadraticForm' Q₁, h, QuadraticForm.toMatrix'_toQuadraticForm']

/-- The Gram matrix of the form of a symmetric matrix is the matrix. -/
theorem _root_.Matrix.toMatrix'_toQuadraticForm' {N : Matrix n n R} (hN : N.IsSymm) :
    N.toQuadraticForm'.toMatrix' = N := by
  have hsym : ∀ x y : n → R, Matrix.toLinearMap₂' R N x y = Matrix.toLinearMap₂' R N y x := by
    intro x y
    rw [Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_apply', Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hN.eq, dotProduct_comm]
  rw [Matrix.toQuadraticForm', QuadraticForm.toMatrix', QuadraticMap.associated_left_inverse R hsym]
  exact (LinearMap.toMatrix₂' R).apply_symm_apply N

end MatrixForm

section HyperbolicPair

/-! ### Hyperbolic pairs and `SO` of a hyperbolic plane -/

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- A nondegenerate form with an isotropic vector `f ≠ 0` has a hyperbolic pair `f, f'` (Tau Ceti's
`QuadraticMap.exists_isotropic_polar_eq_one_of_radical_eq_bot`). -/
theorem exists_hyperbolicPair_of_isotropic (hQ : IsNondeg Q) {f : V} (hf0 : f ≠ 0) (hf : Q f = 0) :
    ∃ f', Q f' = 0 ∧ QuadraticMap.polar Q f f' = 1 :=
  QuadraticMap.exists_isotropic_polar_eq_one_of_radical_eq_bot
    (QuadraticMap.nondegenerate_iff_radical_eq_bot.1 ((isNondeg_iff_nondegenerate Q).1 hQ)) hf0 hf

omit [Invertible (2 : K)] in
/-- A hyperbolic pair is linearly independent. -/
theorem linearIndependent_hyperbolicPair {f f' : V} (hf : Q f = 0) (hf' : Q f' = 0)
    (hp : QuadraticMap.polar Q f f' = 1) : LinearIndependent K ![f, f'] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hff : QuadraticMap.polar Q f f = 0 := by rw [QuadraticMap.polar_self, hf, smul_zero]
  have hff' : QuadraticMap.polar Q f' f' = 0 := by rw [QuadraticMap.polar_self, hf', smul_zero]
  have hp' : QuadraticMap.polar Q f' f = 1 := by rw [QuadraticMap.polar_comm]; exact hp
  have h1 := congrArg (QuadraticMap.polar Q f) hab
  have h2 := congrArg (QuadraticMap.polar Q f') hab
  simp only [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, hff, hp, hff', hp',
    smul_eq_mul, QuadraticMap.polar_zero_right] at h1 h2
  exact ⟨by simpa using h2, by simpa using h1⟩

/-- **`SO` of a hyperbolic plane is a split torus**: an isometry of determinant `1` of a plane with
hyperbolic pair `f, f'` scales `f` and `f'` by inverse scalars (Tau Ceti's
`TauCeti.hyperbolicTorus_surjective` is the coordinate version). -/
theorem exists_smul_of_isometry_det_one [FiniteDimensional K V] (hdim : Module.finrank K V = 2)
    {f f' : V} (hf : Q f = 0) (hf' : Q f' = 0) (hp : QuadraticMap.polar Q f f' = 1)
    (R : V →ₗ[K] V) (hR : ∀ v, Q (R v) = Q v) (hdet : LinearMap.det R = 1) :
    ∃ t : Kˣ, R f = ((t⁻¹ : Kˣ) : K) • f ∧ R f' = (t : K) • f' := by
  have hli := linearIndependent_hyperbolicPair hf hf' hp
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb0 : b 0 = f := by simp [b]
  have hb1 : b 1 = f' := by simp [b]
  -- coordinates of `R f`, `R f'`
  set a := b.repr (R f) 0; set c := b.repr (R f) 1
  set a' := b.repr (R f') 0; set d := b.repr (R f') 1
  have hRf : R f = a • f + c • f' := by
    have := b.sum_repr (R f)
    rw [Fin.sum_univ_two, hb0, hb1] at this
    exact this.symm
  have hRf' : R f' = a' • f + d • f' := by
    have := b.sum_repr (R f')
    rw [Fin.sum_univ_two, hb0, hb1] at this
    exact this.symm
  have hff : QuadraticMap.polar Q f f = 0 := by rw [QuadraticMap.polar_self, hf, smul_zero]
  have hff' : QuadraticMap.polar Q f' f' = 0 := by rw [QuadraticMap.polar_self, hf', smul_zero]
  have hp' : QuadraticMap.polar Q f' f = 1 := by rw [QuadraticMap.polar_comm]; exact hp
  -- `Q(a f + c f') = a c`
  have hQ2 : ∀ x y : K, Q (x • f + y • f') = x * y := fun x y => by
    have h := QuadraticMap.polar Q (x • f) (y • f')
    have hpol : QuadraticMap.polar Q (x • f) (y • f') =
        Q (x • f + y • f') - Q (x • f) - Q (y • f') := rfl
    rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hp, QuadraticMap.map_smul,
      QuadraticMap.map_smul, hf, hf'] at hpol
    simp only [smul_eq_mul, mul_one, mul_zero, sub_zero] at hpol
    linear_combination -hpol
  have e1 : a * c = 0 := by rw [← hQ2, ← hRf, hR, hf]
  have e2 : a' * d = 0 := by rw [← hQ2, ← hRf', hR, hf']
  have e3 : a * d + c * a' = 1 := by
    have hpR : QuadraticMap.polar Q (R f) (R f') = QuadraticMap.polar Q f f' := by
      simp only [QuadraticMap.polar, ← map_add, hR]
    rw [hRf, hRf', hp] at hpR
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hff, hff', hp, hp',
      smul_eq_mul] at hpR
    linear_combination hpR
  have e4 : a * d - c * a' = 1 := by
    rw [← hdet, ← LinearMap.det_toMatrix b, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, hb0, hb1, a, c, a', d]
    ring
  have h2ne : (2 : K) ≠ 0 := Invertible.ne_zero 2
  have had : a * d = 1 := mul_left_cancel₀ h2ne (by linear_combination e3 + e4)
  have hc : c = 0 := by
    have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one had
    exact (mul_eq_zero.1 e1).resolve_left ha
  have ha' : a' = 0 := by
    have hd : d ≠ 0 := right_ne_zero_of_mul_eq_one had
    exact (mul_eq_zero.1 e2).resolve_right hd
  refine ⟨Units.mk0 d (right_ne_zero_of_mul_eq_one had), ?_, ?_⟩
  · rw [hRf, hc, zero_smul, add_zero, Units.val_inv_eq_inv_val, Units.val_mk0,
      eq_inv_of_mul_eq_one_left had]
  · rw [hRf', ha', zero_smul, zero_add, Units.val_mk0]

omit [Invertible (2 : K)] in
/-- On a plane with hyperbolic pair `f, f'`, a map scaling `f, f'` by `t⁻¹, t` is
`v ↦ v + (t⁻¹ − 1) polar(f', v) f + (t − 1) polar(f, v) f'`. -/
theorem apply_eq_of_smul_hyperbolicPair [FiniteDimensional K V] (hdim : Module.finrank K V = 2)
    {f f' : V} (hf : Q f = 0) (hf' : Q f' = 0) (hp : QuadraticMap.polar Q f f' = 1)
    (R : V →ₗ[K] V) {t : Kˣ} (hRf : R f = ((t⁻¹ : Kˣ) : K) • f) (hRf' : R f' = (t : K) • f')
    (v : V) : R v = v + (((t⁻¹ : Kˣ) : K) - 1) • (QuadraticMap.polar Q f' v • f) +
      ((t : K) - 1) • (QuadraticMap.polar Q f v • f') := by
  have hli := linearIndependent_hyperbolicPair hf hf' hp
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb0 : b 0 = f := by simp [b]
  have hb1 : b 1 = f' := by simp [b]
  have hff : QuadraticMap.polar Q f f = 0 := by rw [QuadraticMap.polar_self, hf, smul_zero]
  have hff' : QuadraticMap.polar Q f' f' = 0 := by rw [QuadraticMap.polar_self, hf', smul_zero]
  have hp' : QuadraticMap.polar Q f' f = 1 := by rw [QuadraticMap.polar_comm]; exact hp
  let L : V →ₗ[K] V := LinearMap.id + (((t⁻¹ : Kˣ) : K) - 1) •
      ((QuadraticMap.polarBilin Q f').smulRight f) +
    ((t : K) - 1) • ((QuadraticMap.polarBilin Q f).smulRight f')
  have hL : R = L := b.ext fun i => by
    fin_cases i
    · simp [L, hb0, hRf, hff, hp']; module
    · simp [L, hb1, hRf', hff', hp]; module
  rw [hL]
  simp [L, smul_smul]

end HyperbolicPair

/-- `A.toQuadraticForm' (P v) = (Pᵀ A P).toQuadraticForm' v` (pointwise
`QuadraticForm.toMatrix'_comp`). -/
theorem _root_.Matrix.toQuadraticForm'_mulVec {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] (A P : Matrix n n R) (v : n → R) :
    A.toQuadraticForm' (P.mulVec v) = (P.transpose * A * P).toQuadraticForm' v := by
  rw [Matrix.toQuadraticForm'_apply, Matrix.toQuadraticForm'_apply, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v P.transpose, Matrix.vecMul_transpose]

end GSpinGGP
