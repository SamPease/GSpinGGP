import GSpinGGP.Foundations.GSpin
import TauCeti.LinearAlgebra.QuadraticForm.Witt.Cancellation
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

end GSpinGGP
