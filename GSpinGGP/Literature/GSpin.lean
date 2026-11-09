import GSpinGGP.Foundations.LocalGroups
import GSpinGGP.Foundations.Representations
import GSpinGGP.Foundations.GSpin
import GSpinGGP.Foundations.QuadraticForms
import GSpinGGP.Foundations.PAdicQuadraticForms
import GSpinGGP.GGP.Triple

/-!
# Cited facts about quadratic forms and general spin groups

Layer-2 *Literature* file for the formalization of *The Local Gan–Gross–Prasad Conjecture for
General Spin Groups* (S. Pease, PhD thesis, Rutgers–Newark 2026, doi 10.7282/t3-qb3s-s249; the
"Thesis").

Each `axiom` below is a result cited from the literature, stated in the weakest form we believe
correct, using only layer-1 notions (`Foundations/LocalGroups`, `Representations`, `GSpin`).
Galois cohomology `H¹` is **not** modelled.

## Contents
* (a) Witt cancellation and the Witt decomposition are theorems now
  (`Foundations/QuadraticForms`, from Tau Ceti).
* (b) Classification over `p`-adic fields (Lam Ch. VI; O'Meara §63) —
  `padic_quadratic_classes` (a theorem, `Foundations/PAdicQuadraticForms`, from Tau Ceti);
  existence of inner-twist data `exists_innerTwist_of_sameDisc`
  (a *theorem*, from Mathlib's algebraically closed classification); the derived theorem
  `exists_innerFormIndex`.
* (c) `GSpin(Q)(K) → SO(Q)(K)` is onto (`gspin_specP_surjective_SO`, a theorem, from
  Cartan–Dieudonné `cartan_dieudonne_even` in `Foundations/QuadraticForms`).
* (d) Steinberg's connectedness of centralizers, in concrete form —
  `steinberg_centralizer_connected` (`IsSS`-version `steinberg_centralizer_connected'`).
* (e) Regular nilpotent orbits exist iff quasi-split (Waldspurger) — now theorems in
  `GGP/RegularNilpotent` and `GGP/RegularNilpotentConverse` (from Jantzen's results in
  `Literature/NilpotentOrbits`): `nilReg_nonempty_iff_quasiSplit`, and the GGP-centralizer versions
  `nilReg_centralizer_nonempty_imp` (unconditional, one direction; proved) and
  `nilReg_centralizer_nonempty_iff` (both directions, under a torus hypothesis on the moved part:
  the statement without that hypothesis is false, see the docstring).
  Existence of Luo's orbit `O_ν` for a GGP datum — `exists_regularNil_inOrbitNu`, also a theorem
  (`GGP/RegularNilpotent`).
* (f) Multiplicity at most one (Emory–Takeda + reduction; Yan) — `emoryTakeda_mult_le_one`.
-/

noncomputable section

open CliffordAlgebra Module
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

/-! ## (b) Quadratic forms over `p`-adic fields; inner-twist data -/

section Classification

/-! ### Inner-twist data (proved; formerly an axiom) -/

namespace InnerTwistAux

theorem isNondeg_iff_discr'_ne_zero {R : Type*} [Field R] [Invertible (2 : R)] {m : ℕ}
    (q : QuadraticForm R (Fin m → R)) : IsNondeg q ↔ q.discr' ≠ 0 := by
  rw [IsNondeg, LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Pi.basisFun R (Fin m)),
    LinearMap.BilinForm.toMatrix_basisFun]
  rfl

variable {K : Type*} [Field K] [Invertible (2 : K)]

local notation "Kb" => AlgebraicClosure K

/-- coordinates on `Kb ⊗ K^m` -/
noncomputable abbrev bcE (m : ℕ) : (Kb ⊗[K] (Fin m → K)) ≃ₗ[Kb] (Fin m → Kb) :=
  (bcBasis K m).equivFun

/-- the base-changed form in coordinates -/
noncomputable abbrev qbar {m : ℕ} (Q : QuadraticForm K (Fin m → K)) :
    QuadraticForm Kb (Fin m → Kb) :=
  (Q.baseChange Kb).comp (bcE (K := K) m).symm.toLinearMap

theorem toMatrix'_qbar {m : ℕ} (Q : QuadraticForm K (Fin m → K)) :
    (qbar Q).toMatrix' = Q.toMatrix'.map (algebraMap K Kb) := by
  ext i j
  simp only [QuadraticForm.toMatrix', LinearMap.toMatrix₂'_apply, Matrix.map_apply]
  rw [QuadraticMap.associated_comp, LinearMap.compl₁₂_apply, QuadraticForm.associated_baseChange]
  have h : ∀ k, (bcE (K := K) m).symm (Pi.single k 1) = (1 : Kb) ⊗ₜ Pi.single k 1 := by
    intro k
    rw [Basis.equivFun_symm_single]
    simp [bcBasis]
  simp only [LinearEquiv.coe_coe, h, LinearMap.BilinForm.baseChange_tmul, one_mul]
  rw [Algebra.algebraMap_eq_smul_one]

theorem discr'_qbar {m : ℕ} (Q : QuadraticForm K (Fin m → K)) :
    (qbar Q).discr' = algebraMap K Kb Q.discr' := by
  simp only [QuadraticForm.discr', toMatrix'_qbar]
  exact (RingHom.map_det _ _).symm

end InnerTwistAux

open InnerTwistAux in
/-- **Existence of inner-twist data** (Thesis §6.2).  If `Q, Q'` on `K^m` are
nondegenerate with the same discriminant, there is a `K̄`-isometry `φ : Q_{K̄} ≃ Q'_{K̄}` with
`det(φ⁻¹ ∘ σφ) = 1` for all `σ ∈ Aut(K̄/K)`.

Proof: over the algebraically closed
`K̄` nondegenerate forms of equal dimension are isometric (Mathlib
`QuadraticForm.equivalent_of_isAlgClosed`); comparing Gram determinants in the rational basis gives
`det(φ)² · c² = 1` (`SameDisc`: `disc Q' = c² disc Q`), so `det φ = ±c⁻¹ ∈ K` is fixed by every
`σ`, and `det(φ⁻¹ ∘ σφ) = det(φ)⁻¹ σ(det φ) = 1`. -/
theorem exists_innerTwist_of_sameDisc {K : Type*} [Field K] [Invertible (2 : K)] {m : ℕ}
    {Q Q' : QuadraticForm K (Fin m → K)} (hQ : IsNondeg Q) (hQ' : IsNondeg Q')
    (h : SameDisc Q Q') : ∃ τ : InnerTwist Q, τ.Q' = Q' := by
  classical
  obtain ⟨c, hc0, hc⟩ := h
  have hd : Q.discr' ≠ 0 := (isNondeg_iff_discr'_ne_zero Q).1 hQ
  have hd' : Q'.discr' ≠ 0 := (isNondeg_iff_discr'_ne_zero Q').1 hQ'
  have n1 : IsNondeg (qbar Q) := by
    rw [isNondeg_iff_discr'_ne_zero, discr'_qbar]; simpa using hd
  have n2 : IsNondeg (qbar Q') := by
    rw [isNondeg_iff_discr'_ne_zero, discr'_qbar]; simpa using hd'
  obtain ⟨ψ⟩ := QuadraticForm.equivalent_of_isAlgClosed (qbar Q) (qbar Q') n1.1 n2.1
  let φ : (Q.baseChange (AlgebraicClosure K)).IsometryEquiv (Q'.baseChange (AlgebraicClosure K)) :=
    { toLinearEquiv := ((bcE m).trans ψ.toLinearEquiv).trans (bcE m).symm
      map_app' := by
        intro v
        have := ψ.map_app ((bcE m) v)
        simp only [qbar, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.symm_apply_apply] at this
        simpa using this }
  -- matrix of φ in the rational basis is the matrix of ψ
  have hM : LinearMap.toMatrix (bcBasis K m) (bcBasis K m) φ.toLinearEquiv.toLinearMap =
      LinearMap.toMatrix' ψ.toLinearEquiv.toLinearMap := by
    ext i j
    simp [LinearMap.toMatrix_apply, LinearMap.toMatrix'_apply, φ,
      Finsupp.single_eq_pi_single]
  -- det relation
  have hdisc : (qbar Q).discr' = (LinearMap.det ψ.toLinearEquiv.toLinearMap) ^ 2 *
      (qbar Q').discr' := by
    have hcomp : qbar Q = (qbar Q').comp ψ.toLinearEquiv.toLinearMap := by
      ext v; simp
    have h2 := QuadraticForm.discr'_comp (Q := qbar Q') ψ.toLinearEquiv.toLinearMap
    rw [← hcomp] at h2
    rw [h2, LinearMap.det_toMatrix']; ring
  set δ := LinearMap.det ψ.toLinearEquiv.toLinearMap
  have hδ : δ = algebraMap K (AlgebraicClosure K) c⁻¹ ∨ δ = -algebraMap K (AlgebraicClosure K) c⁻¹ := by
    rw [discr'_qbar, discr'_qbar, hc, map_mul, map_pow] at hdisc
    have hdK : algebraMap K (AlgebraicClosure K) Q.discr' ≠ 0 := by simpa using hd
    have : (δ * algebraMap K (AlgebraicClosure K) c) ^ 2 = 1 := by
      have := hdisc.symm
      field_simp at this ⊢
      linear_combination this
    rw [sq] at this
    have hc' : algebraMap K (AlgebraicClosure K) c ≠ 0 := by simpa using hc0
    rcases mul_self_eq_one_iff.mp this with h1 | h1
    · left; rw [map_inv₀]; field_simp; linear_combination h1
    · right; rw [map_inv₀]; field_simp; linear_combination h1
  refine ⟨{ Q' := Q', nondeg' := hQ', sameDisc := ⟨c, hc0, hc⟩, φ := φ, cocycle := ?_ }, rfl⟩
  intro σ
  have hφdet : LinearMap.det φ.toLinearEquiv.toLinearMap = δ := by
    rw [← LinearMap.det_toMatrix (bcBasis K m), hM, LinearMap.det_toMatrix']
  have hσ : σ δ = δ := by
    rcases hδ with h1 | h1 <;> simp only [h1, map_neg, AlgEquiv.commutes]
  rw [LinearMap.det_comp, galoisConj, LinearMap.det_toLin]
  have hmap : ((LinearMap.toMatrix (bcBasis K m) (bcBasis K m)
      φ.toLinearEquiv.toLinearMap).map σ).det = σ δ := by
    have hdetM : (LinearMap.toMatrix (bcBasis K m) (bcBasis K m)
        φ.toLinearEquiv.toLinearMap).det = δ := by
      rw [LinearMap.det_toMatrix]; exact hφdet
    rw [← hdetM]
    exact (RingHom.map_det (σ : (AlgebraicClosure K) →+* (AlgebraicClosure K)) _).symm
  rw [hmap, hσ]
  have : LinearMap.det φ.toLinearEquiv.symm.toLinearMap * δ = 1 := by
    rw [← hφdet, ← LinearMap.det_comp]
    have : (φ.toLinearEquiv.symm.toLinearMap ∘ₗ φ.toLinearEquiv.toLinearMap) = LinearMap.id := by
      ext v; simp
    rw [this, LinearMap.det_id]
  exact this

/-- **A system of inner forms with twist data** (Thesis §6.2): for `p`-adic
`F` and nondegenerate `Q` on `F^m`, a finite family `τ : Fin n → InnerTwist Q` whose targets
represent each isometry class of nondegenerate forms of the same dimension and discriminant
exactly once (i.e. `Fin n ≃ H¹(F, SO(W))`), with the trivial twist at `i₀`, and `n = 2` when
`m ≥ 3`.  Derived from `padic_quadratic_classes` and `exists_innerTwist_of_sameDisc`.
(`InnerFormSystem` itself lives in `GGP/Triple`; this is its existence.) -/
theorem exists_innerFormIndex {F : Type*} [NontriviallyNormedField F] [PAdicField F] {m : ℕ}
    (Q : QuadraticForm F (Fin m → F)) (hQ : IsNondeg Q) :
    ∃ (n : ℕ) (τ : Fin n → InnerTwist Q) (i₀ : Fin n),
      τ i₀ = InnerTwist.refl Q hQ ∧
      (∀ Q' : QuadraticForm F (Fin m → F), IsNondeg Q' → SameDisc Q Q' →
        ∃! i, Nonempty (Q'.IsometryEquiv (τ i).Q')) ∧
      (3 ≤ m → n = 2) := by
  classical
  obtain ⟨n, R, i₀, hR0, hR, huniq, h3, -, -, -⟩ := padic_quadratic_classes Q hQ
  have hex : ∀ i, ∃ σ : InnerTwist Q, σ.Q' = R i := fun i =>
    exists_innerTwist_of_sameDisc hQ (hR i).1 (hR i).2
  let τ : Fin n → InnerTwist Q := fun i =>
    if i = i₀ then InnerTwist.refl Q hQ else (hex i).choose
  have hτ : ∀ i, (τ i).Q' = R i := by
    intro i
    by_cases hi : i = i₀
    · subst hi; simp only [τ, ite_true]; exact hR0.symm
    · simp only [τ, hi, ite_false]; exact (hex i).choose_spec
  refine ⟨n, τ, i₀, by simp [τ], fun Q' h1 h2 => ?_, h3⟩
  simpa only [hτ] using huniq Q' h1 h2

end Classification

/-! ## (c) Surjectivity of `GSpin → SO` -/

section Surjective

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- `P(u w) = s_u s_w` for anisotropic `u, w` (Thesis §5.1.2: `w v w⁻¹ = −s_w(v)`). -/
theorem specP_gspinPair (Q : QuadraticForm K V) {u w : V} (hu : Q u ≠ 0) (hw : Q w ≠ 0) :
    (specP Q (gspinPair Q hu hw) : V →ₗ[K] V) = quadReflection Q u * quadReflection Q w := by
  ext v
  apply ι_injective Q
  change ι Q (specP Q (gspinPair Q hu hw) v) = _
  rw [ι_specP]
  have hinv : ((((gspinPair Q hu hw : GSpin Q) : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q) = (Q u * Q w)⁻¹ • (ι Q w * ι Q u) := rfl
  rw [hinv, coe_gspinPair, mul_smul_comm,
    show ι Q u * ι Q w * ι Q v * (ι Q w * ι Q u) = ι Q u * (ι Q w * ι Q v * ι Q w) * ι Q u by
      simp only [mul_assoc], ι_mul_ι_mul_ι, ι_mul_ι_mul_ι, ← map_smul]
  congr 1
  simp only [Module.End.mul_apply, quadReflection_apply, QuadraticMap.polar_sub_right,
    QuadraticMap.polar_smul_right, smul_eq_mul]
  match_scalars <;> (field_simp; try ring)

/-- Cartan–Dieudonné implies the surjectivity of `P : GSpin(V) → SO(V)`: a lift of
`∏ s_{uᵢ} s_{wᵢ}` is `∏ uᵢ wᵢ` (`specP_gspinPair`). -/
theorem gspin_specP_surjective_SO_of_cartanDieudonne [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : IsNondeg Q)
    (g : V ≃ₗ[K] V) (hg : ∀ v, Q (g v) = Q v) (hdet : LinearMap.det (g : V →ₗ[K] V) = 1) :
    ∃ x : GSpin Q, specP Q x = g := by
  obtain ⟨l, hl, hgl⟩ := cartan_dieudonne_even Q hQ g hg hdet
  have key : ∀ l : List (V × V), (∀ p ∈ l, Q p.1 ≠ 0 ∧ Q p.2 ≠ 0) →
      ∃ x : GSpin Q, (specP Q x : V →ₗ[K] V) =
        (l.map fun p => quadReflection Q p.1 * quadReflection Q p.2).prod := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨1, by simp; rfl⟩
    | cons p l ih =>
      intro h
      obtain ⟨x, hx⟩ := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
      obtain ⟨h1, h2⟩ := h p List.mem_cons_self
      refine ⟨gspinPair Q h1 h2 * x, ?_⟩
      rw [List.map_cons, List.prod_cons, ← hx, ← specP_gspinPair Q h1 h2, map_mul]
      rfl
  obtain ⟨x, hx⟩ := key l hl
  exact ⟨x, LinearEquiv.toLinearMap_injective (hx.trans hgl.symm)⟩

/-- **`P : GSpin(V)(K) → SO(V)(K)` is surjective** (Thesis §5.1.2).
Source: the exact sequence `1 → G_m → GSpin(V) → SO(V) → 1` and Hilbert's Theorem 90,
`H¹(K, G_m) = 1` (Serre, *Local Fields*, Ch. X); equivalently Cartan–Dieudonné (every
element of `SO(V)` is a product of an even number of reflections `s_v`, and `P(v₁ v₂) = s_{v₁} s_{v₂}`).
Valid over any field with `2` invertible; not only `p`-adic.
Proved from `cartan_dieudonne_even`
(`gspin_specP_surjective_SO_of_cartanDieudonne`). -/
theorem gspin_specP_surjective_SO [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : IsNondeg Q)
    (g : V ≃ₗ[K] V) (hg : ∀ v, Q (g v) = Q v) (hdet : LinearMap.det (g : V →ₗ[K] V) = 1) :
    ∃ x : GSpin Q, specP Q x = g :=
  gspin_specP_surjective_SO_of_cartanDieudonne Q hQ g hg hdet

end Surjective

/-! ## (d) Connectedness of centralizers (Steinberg) -/

section Steinberg

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- `W_{-1} = ker(P(x) + 1)`, the `(-1)`-eigenspace of `P(x)` (it is where the
centralizer of `P(x)` in `O(V)` has its second orthogonal factor). -/
def negFixedSub [Invertible (2 : K)] {Q : QuadraticForm K V} (x : GSpin Q) : Submodule K V :=
  LinearMap.ker ((specP Q x : V →ₗ[K] V) + LinearMap.id)

variable [Invertible (2 : K)]

/-- An endomorphism commuting with `P(x)` preserves `W'_x = ker(P(x) - 1)`. -/
theorem mapsTo_fixedSub_of_commute {Q : QuadraticForm K V} {x g : GSpin Q}
    (h : Commute (specP Q g) (specP Q x)) :
    ∀ v ∈ fixedSub x, (specP Q g : V →ₗ[K] V) v ∈ fixedSub x := by
  intro v hv
  simp only [fixedSub, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hv ⊢
  have := congrArg (fun e : V ≃ₗ[K] V => e v) h.eq
  simp only [LinearEquiv.mul_apply] at this
  simp only [LinearEquiv.coe_coe] at hv ⊢
  rw [← this, hv]

/-- An endomorphism commuting with `P(x)` preserves `W_{-1} = ker(P(x) + 1)`. -/
theorem mapsTo_negFixedSub_of_commute {Q : QuadraticForm K V} {x g : GSpin Q}
    (h : Commute (specP Q g) (specP Q x)) :
    ∀ v ∈ negFixedSub x, (specP Q g : V →ₗ[K] V) v ∈ negFixedSub x := by
  intro v hv
  simp only [negFixedSub, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
    add_eq_zero_iff_eq_neg] at hv ⊢
  have := congrArg (fun e : V ≃ₗ[K] V => e v) h.eq
  simp only [LinearEquiv.mul_apply] at this
  simp only [LinearEquiv.coe_coe] at hv ⊢
  rw [← this, hv, map_neg]

end Steinberg

/-! ## (e) Regular nilpotent orbits and quasi-splitness -/

section NilReg

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- The *moved part* of the Lie centralizer of `x ∈ GSpin(W)` is abelian: elements of
`gspin(W)_x` acting trivially (under `ad`) on `W'_x = ker(P x - 1)` commute.  Such elements are
`so(W''_x)_{x̄} ⊕ F`, so this says `Z_{SO(W''_x)}(x̄)⁰` is a torus, i.e. `G''_x` (the factor of `G_x` on
`W''_x`) is a torus — true for every `x ∈ T_♮`, the only `x` that enter `Γ(G, H)`. -/
def MovedPartAbelian {m : ℕ} (Q : QuadraticForm F (Fin m → F)) (x : GSpin Q) : Prop :=
  ∀ X ∈ lieCentralizer (gspin Q) ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q),
  ∀ Y ∈ lieCentralizer (gspin Q) ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q),
    (∀ v ∈ fixedSub x, ⁅X, ι Q v⁆ = 0) → (∀ v ∈ fixedSub x, ⁅Y, ι Q v⁆ = 0) → ⁅X, Y⁆ = 0

namespace GGPData

variable (d : GGPData F)

/-- The quadratic space `W'_x = ker(P x - 1) ⊆ W`. -/
abbrev QWfix (x : GSpin d.QW) : QuadraticForm F ↥(fixedSub x) :=
  d.QW.comp (fixedSub x).subtype

/-- The quadratic space `V'_x = W'_x ⊕^⊥ Z`. -/
abbrev QVfix (x : GSpin d.QW) : QuadraticForm F (↥(fixedSub x) × d.Z) :=
  (d.QWfix x).prod d.QZ

end GGPData

end NilReg

/-! ## (f) Multiplicity one -/

section MultOne

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- **Multiplicity at most one** (Thesis Thm. 5.5.1).
For every GGP datum `d`, nontrivial additive character `ψ`, and irreducible tempered unitary
representation `π` of `G(F)`, `m(π) = dim Hom_{H(F)}(π^∞, ξ) ≤ 1`.

Source: Pan Yan, *Uniqueness of Bessel models for GSpin groups*, Nagoya Math. J. (2026),
arXiv:2503.20116, Thm 1.1, p. 2: for a nondegenerate quadratic space `V` over a local field of
characteristic `0`, a nondegenerate `V₀ ⊂ V` with `V₀^⊥` split of dimension `2r + 1`, the Bessel
subgroup `H = N_{Q_r} ⋊ GSpin(V₀)` of `GSpin(V) × GSpin(V₀)` and a generic character `ξ` of `H`,
`dim Hom_H(π ⊗ π₀, ξ) ≤ 1` for all irreducible admissible `π`, `π₀`.  There is no quasi-split
hypothesis, so inner forms are covered.  Here `(V₀, V) = (W, V)`.  The case `r = 0` is
Emory–Takeda, *Contragredients and a multiplicity one theorem for general spin groups*, Math. Z. 303
(2023), Thm 1.1 (arXiv:2104.04814v4, p. 2).
Dictionary: an irreducible unitary representation of the `p`-adic group `G(F)` has irreducible
admissible smooth part (Bernstein 1974), of the form `π ⊗ π₀`; all linear forms on it are
continuous.  The instances on `↥d.G` are the layer-1 theorems of
`Foundations/LocalGroups` (closedness of `G` is `GGPData.isClosed_G`). -/
axiom emoryTakeda_mult_le_one (d : GGPData F) (ψ : NontrivialAddChar F) (π : UnitaryRep ↥d.G) :
    haveI := subgroup_isTopologicalGroup F d.ambient d.G
    haveI := subgroup_t2Space F d.ambient d.G
    haveI := subgroup_locallyCompactSpace_of_isClosed F d.ambient d.G d.isClosed_G
    IsTempered π → multiplicity π d.H (d.xi ψ.toAddChar) ≤ 1

end MultOne

end GSpinGGP
