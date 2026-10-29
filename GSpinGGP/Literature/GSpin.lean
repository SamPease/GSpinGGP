import GSpinGGP.Foundations.LocalGroups
import GSpinGGP.Foundations.Representations
import GSpinGGP.Foundations.GSpin
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
* (a) Witt cancellation and the Witt decomposition (Lam, Ch. I) — `witt_cancellation`,
  `hypForm`, `witt_decomposition`.
* (b) Classification over `p`-adic fields (Lam Ch. VI; O'Meara §63) —
  `padic_quadratic_classes`; existence of inner-twist data `exists_innerTwist_of_sameDisc`
  (a *theorem*, from Mathlib's algebraically closed classification); the derived theorem
  `exists_innerFormIndex`.
* (c) Cartan–Dieudonné — `cartan_dieudonne_even`; hence `GSpin(Q)(K) → SO(Q)(K)` is onto
  (`gspin_specP_surjective_SO`, now a theorem).
* (d) Steinberg's connectedness of centralizers, in concrete form —
  `steinberg_centralizer_connected` (`IsSS`-version `steinberg_centralizer_connected'`).
* (e) Regular nilpotent orbits exist iff quasi-split (Waldspurger) —
  `nilReg_nonempty_iff_quasiSplit`, and the GGP-centralizer versions
  `nilReg_centralizer_nonempty_imp` (unconditional, one direction) and
  `nilReg_centralizer_nonempty_iff` (both directions, under a torus hypothesis on the moved part:
  the statement without that hypothesis is false, see the docstring).
  Existence of Luo's orbit `O_ν` for a GGP datum — `exists_regularNil_inOrbitNu` (this axiom
  reads `adV` and `IsInOrbitNu` from `GGP/Triple`, hence that import).
* (f) Multiplicity at most one (Emory–Takeda + reduction; Yan) — `emoryTakeda_mult_le_one`.
-/

noncomputable section

open CliffordAlgebra Module
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

/-! ## (a) Witt's theorems -/

section Witt

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- **Witt cancellation** (Lam, *Introduction to Quadratic Forms over Fields*, Ch. I,
§4 (Witt cancellation; theorem number unverified); used for the injectivity of `[U] ↦ [U ⊕ Z]`).
Over a field of characteristic `≠ 2`, `U ⊥ X ≅ U ⊥ Y` implies `X ≅ Y`.
Lam proves this for arbitrary (possibly singular) forms; we only assume finite-dimensionality.
Mathlib (v4.35) has no Witt cancellation.

**Characteristic `≠ 2` is essential and is an explicit binder here** (a section variable not
mentioned in the statement would be dropped by Lean).  Over `ZMod 2` the statement is false:
`⟨1⟩ ⊥ H ≅ ⟨1⟩ ⊥ [1,1]` via `(u,x,y) ↦ (u+x+y,x,y)` but `H ≇ [1,1]`. -/
axiom witt_cancellation [Invertible (2 : K)] {U X Y : Type*} [AddCommGroup U] [Module K U]
    [FiniteDimensional K U]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    (QU : QuadraticForm K U) (QX : QuadraticForm K X) (QY : QuadraticForm K Y)
    (h : Nonempty ((QU.prod QX).IsometryEquiv (QU.prod QY))) :
    Nonempty (QX.IsometryEquiv QY)

/-- Gram matrix of the hyperbolic space `H^n` of dimension `2n`: `b(e_i, e_j) = [i + j = 2n-1]`
(an orthogonal sum of `n` hyperbolic planes, written with an antidiagonal Gram matrix). -/
def hypMatrix (K : Type*) [Field K] (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) K :=
  fun i j => if (i : ℕ) + (j : ℕ) + 1 = 2 * n then 1 else 0

/-- The hyperbolic quadratic space `H^n` on `K^{2n}` (Lam Ch. I §3), `q(v) = vᵀ (hypMatrix n) v`. -/
def hypForm (K : Type*) [Field K] (n : ℕ) : QuadraticForm K (Fin (2 * n) → K) :=
  Matrix.toQuadraticForm' (hypMatrix K n)

/-- **Witt decomposition** (Lam Ch. I §4, theorem number unverified; Thesis §5.1.4):
a nondegenerate finite-dimensional quadratic space is `H^w ⊥ V_an` with `V_an` anisotropic, and
`w` is the Witt index (the maximal dimension of a totally isotropic subspace, `wittIndex`).
In particular the `sSup` defining `wittIndex` is attained and
`dim V_an = dim V - 2 w(V)`, so `IsQuasiSplitQF Q ↔ dim V_an ≤ 2`. -/
axiom witt_decomposition {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : IsNondeg Q) :
    ∃ (k : ℕ) (Qa : QuadraticForm K (Fin k → K)), Qa.Anisotropic ∧
      Nonempty (Q.IsometryEquiv ((hypForm K (wittIndex Q)).prod Qa)) ∧
      finrank K V = 2 * wittIndex Q + k

end Witt

/-! ## (b) Quadratic forms over `p`-adic fields; inner-twist data -/

section Classification

/-- **Classification of quadratic forms over a `p`-adic field** (Lam, Ch. VI §2; O'Meara §63
(theorem numbers unverified); used for: `H¹(F, SO(W))` classifies the quadratic spaces of the
same dimension and discriminant, and has exactly two elements when `dim W ≥ 3`).

For a nondegenerate `Q` on `F^m`, the isometry classes of nondegenerate `Q'` on `F^m` with the
same discriminant are finite in number; we give a system of representatives `R : Fin n → _`
containing `Q` itself (at `i₀`), each class met exactly once.  The count is:
`n = 2` if `m ≥ 3` (the Hasse invariant takes both values); `n = 1` if `m ≤ 1`;
for `m = 2`, `n = 1` iff `-det Q` is a square (`Q` hyperbolic), and `n = 2` otherwise
(planes `⟨a, a·det⟩` classified by `a` modulo the norms of `F(√-det)`).
`discr'` is the Gram determinant (Mathlib `QuadraticForm.discr'`). -/
axiom padic_quadratic_classes {F : Type*} [NontriviallyNormedField F] [PAdicField F] {m : ℕ}
    (Q : QuadraticForm F (Fin m → F)) (hQ : IsNondeg Q) :
    ∃ (n : ℕ) (R : Fin n → QuadraticForm F (Fin m → F)) (i₀ : Fin n),
      R i₀ = Q ∧ (∀ i, IsNondeg (R i) ∧ SameDisc Q (R i)) ∧
      (∀ Q' : QuadraticForm F (Fin m → F), IsNondeg Q' → SameDisc Q Q' →
        ∃! i, Nonempty (Q'.IsometryEquiv (R i))) ∧
      (3 ≤ m → n = 2) ∧ (m ≤ 1 → n = 1) ∧ (m = 2 → (n = 1 ↔ IsSquare (-Q.discr'))) ∧ n ≤ 2

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

/-- **Cartan–Dieudonné, `SO` form** (E. Artin, *Geometric Algebra*, Interscience 1957, Ch. III,
Thm. 3.20: in a nonsingular space of dimension `n` over a field of characteristic `≠ 2`, every
isometry is a product of at most `n` symmetries; also Lam, *Introduction to Quadratic Forms over
Fields*, Ch. I, Thm. 7.1; theorem numbers not checked against the books).  A symmetry has
determinant `−1`, so an isometry of determinant `1` is a product of an *even* number of them,
which we group in consecutive pairs: `σ = ∏ᵢ s_{uᵢ} s_{wᵢ}` with all `uᵢ, wᵢ` anisotropic.

Used for `closure_scalarGSpin_gspinPair` (the products `uw` and the scalars generate `GSpin(V)`),
and it implies `gspin_specP_surjective_SO`
(`gspin_specP_surjective_SO_of_cartanDieudonne`).  Characteristic `≠ 2` is an explicit binder
(as for `witt_cancellation`); nondegeneracy is necessary (for a degenerate form the radical
is fixed by every symmetry, but not by every isometry).  Degenerate instances: `V = 0` and
`dim V = 1`, where `SO(V) = 1` and the empty product works. -/
axiom cartan_dieudonne_even [Invertible (2 : K)] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : IsNondeg Q) (σ : V ≃ₗ[K] V) (hσ : ∀ v, Q (σ v) = Q v)
    (hdet : LinearMap.det (σ : V →ₗ[K] V) = 1) :
    ∃ l : List (V × V), (∀ p ∈ l, Q p.1 ≠ 0 ∧ Q p.2 ≠ 0) ∧
      (σ : V →ₗ[K] V) = (l.map fun p => quadReflection Q p.1 * quadReflection Q p.2).prod

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

/-- Cartan–Dieudonné implies the surjectivity of `P : GSpin(V) → SO(V)`, i.e. the axiom
`gspin_specP_surjective_SO` is a consequence of `cartan_dieudonne_even` (consistency check; a lift
of `∏ s_{uᵢ} s_{wᵢ}` is `∏ uᵢ wᵢ`, `specP_gspinPair`). -/
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

/-- **Centralizers of semisimple elements of `GSpin`** (Steinberg,
*Endomorphisms of linear algebraic groups* (1968), Thm. 8.1, since the derived group `Spin(V)` is
simply connected): for semisimple `x`, `Z_{GSpin(V)}(x) = P⁻¹(Z_{SO(V)}(P x)⁰)`.

The identity component is not a layer-1 notion, so we use its classical description for a
semisimple `x̄ = P(x)`: `Z_{O(V)}(x̄) = O(W₊₁) × O(W₋₁) × ∏ GL/unitary factors` (the latter
connected, with determinant one), so
`Z_{SO(V)}(x̄)⁰ = {h ∈ Z_{SO(V)}(x̄) | det h|_{W₊₁} = 1 ∧ det h|_{W₋₁} = 1}`, with
`W_{±1} = ker(x̄ ∓ 1)`.  Hence for `g ∈ GSpin(V)(K)`:
`g x = x g ↔ P(g) commutes with P(x) ∧ det P(g)|_{W'_x} = 1 ∧ det P(g)|_{W_{-1}} = 1`.
(The determinant conditions are stated as `∃` over the — unique — invariance proofs; see
`mapsTo_fixedSub_of_commute`.)  Valid over any field of characteristic `0` (in particular `F̄`,
via `Q.baseChange`); semisimplicity is that of left multiplication on `C(V)` (definitionally
`IsSS`, which needs a normed field — see `steinberg_centralizer_connected'`). -/
axiom steinberg_centralizer_connected {K : Type*} [Field K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : IsNondeg Q) (x : GSpin Q)
    (hx : Module.End.IsSemisimple
      (LinearMap.mulLeft K ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))
    (g : GSpin Q) :
    Commute (g : (CliffordAlgebra Q)ˣ) (x : (CliffordAlgebra Q)ˣ) ↔
      Commute (specP Q g) (specP Q x) ∧
      (∃ h : ∀ v ∈ fixedSub x, (specP Q g : V →ₗ[K] V) v ∈ fixedSub x,
        LinearMap.det ((specP Q g : V →ₗ[K] V).restrict h) = 1) ∧
      (∃ h : ∀ v ∈ negFixedSub x, (specP Q g : V →ₗ[K] V) v ∈ negFixedSub x,
        LinearMap.det ((specP Q g : V →ₗ[K] V).restrict h) = 1)

/-- `steinberg_centralizer_connected` for a normed field (e.g. `p`-adic `F`), with the hypothesis
phrased by `IsSS` (Foundations/LocalGroups), and the conclusion in terms of `grpCentralizer`. -/
theorem steinberg_centralizer_connected' {F : Type*} [NontriviallyNormedField F] [CharZero F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) (hQ : IsNondeg Q) (x : GSpin Q)
    (hx : IsSS F ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) (g : GSpin Q) :
    (g : (CliffordAlgebra Q)ˣ) ∈ grpCentralizer (GSpin Q) (x : (CliffordAlgebra Q)ˣ) ↔
      Commute (specP Q g) (specP Q x) ∧
      (∃ h : ∀ v ∈ fixedSub x, (specP Q g : V →ₗ[F] V) v ∈ fixedSub x,
        LinearMap.det ((specP Q g : V →ₗ[F] V).restrict h) = 1) ∧
      (∃ h : ∀ v ∈ negFixedSub x, (specP Q g : V →ₗ[F] V) v ∈ negFixedSub x,
        LinearMap.det ((specP Q g : V →ₗ[F] V).restrict h) = 1) := by
  rw [← steinberg_centralizer_connected Q hQ x hx g]
  simp only [grpCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩

end Steinberg

/-! ## (e) Regular nilpotent orbits and quasi-splitness -/

section NilReg

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- **Regular nilpotent orbits exist iff `GSpin(V)` is quasi-split** (Thesis §5.1.4
"Regular Nilpotent Orbits"; Waldspurger, *Astérisque* 269 (2001), Ch. I; Waldspurger, *Compositio* 146
(2010), §7.1; Luo §2.1).  Since `P` is onto `SO(V)` with central kernel, the `GSpin(V)(F)`-orbits of nilpotents
in `gspin(V)` are the `SO(V)(F)`-orbits of nilpotents in `so(V)`; `Nil_reg(so(V))` is nonempty
iff the anisotropic kernel of `V` has dimension `≤ 2` (`IsQuasiSplitQF`). -/
axiom nilReg_nonempty_iff_quasiSplit {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (hQ : IsNondeg Q) :
    (NilReg (GSpin Q) (gspin Q)).Nonempty ↔ IsQuasiSplitQF Q

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

/-- **Germs vanish off quasi-split centralizers, GGP form; necessary condition**
(Waldspurger 2001 Ch. I applied to the factors of `G_x`; BP Prop. 4.5.1(i)).  For semisimple
`x ∈ GSpin(W)(F)` embedded diagonally, `G_x` is covered by `G'_x × G''_x` with central split
kernel, `G'_x = GSpin(W'_x) × GSpin(V'_x)`.  If `𝔤_x` has a regular nilpotent
orbit then `G_x`, hence `G'_x`, is quasi-split, i.e. `W'_x` and `V'_x = W'_x ⊕ Z` are (this
direction holds for every semisimple `x`; the converse needs `MovedPartAbelian`).
Combined with `germ = 0` off `NilReg`, this gives BP Prop. 4.5.1(i) for the germs `c_{θ,O}(x)`. -/
axiom nilReg_centralizer_nonempty_imp (d : GGPData F) (x : GSpin d.QW)
    (hx : IsSS F ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) :
    (NilReg (grpCentralizer d.G ((d.diag x : d.G) : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag x : d.G) : d.ambientˣ) : d.ambient))).Nonempty →
    IsQuasiSplitQF (d.QWfix x) ∧ IsQuasiSplitQF (d.QVfix x)

/-- **Regular nilpotent orbits of GGP centralizers** (Waldspurger 2001
Ch. I, 2010 §7.1).  For semisimple `x ∈ GSpin(W)(F)` whose moved part `G''_x` is a torus
(`MovedPartAbelian`, true for all `x` contributing to `Γ(G,H)`), `Nil_reg(𝔤_x) ≠ ∅` iff `W'_x`
and `V'_x = W'_x ⊕ Z` are quasi-split.

NB: without the torus hypothesis the "if" direction is **false**, because
`G_x` is quasi-split iff both `G'_x` and `G''_x` are, and `G''_x` need not be.  For non-quasi-split
`G`: `P(x) = -1` on an anisotropic `W''_x` of dimension 4.  Even for quasi-split `G` (where that
example cannot occur, by a Witt-group computation): `F = Q_3`, `W = N_D ⊥ ⟨1,-2⟩`, `Z = ⟨-3⟩`,
`P(x) = -1` on the quaternion norm form `N_D` and `-(3+2√2) ∈ E¹` on `⟨1,-2⟩`; then
`G'_x = G_m × G_m` but `G''_x ⊇ SL₁(D)⁴`.  So "`G_x` quasi-split iff `G'_x` quasi-split" holds
only for `x` with `Z_{SO(W''_x)}(x̄)⁰` a torus, which is this hypothesis.  It holds on `Γ(G,H)` (`movedPartAbelian_of_isGammaElt` in `Main`).  See
`nilReg_centralizer_nonempty_imp` for the unconditional direction. -/
axiom nilReg_centralizer_nonempty_iff (d : GGPData F) (x : GSpin d.QW)
    (hx : IsSS F ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
    (hmoved : MovedPartAbelian d.QW x) :
    (NilReg (grpCentralizer d.G ((d.diag x : d.G) : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag x : d.G) : d.ambientˣ) : d.ambient))).Nonempty ↔
    IsQuasiSplitQF (d.QWfix x) ∧ IsQuasiSplitQF (d.QVfix x)

/-- **Luo's orbit `O_ν` exists in the GGP situation** (Waldspurger, *Compositio* 146 (2010),
§7.1; Luo, *A local trace formula for the local Gan–Gross–Prasad conjecture for special
orthogonal groups*, §2.1 and §7.1; classification of regular nilpotent orbits: Waldspurger,
*Astérisque* 269 (2001), Ch. I; Thesis §5.1.4 "Regular Nilpotent Orbits").

For a quasi-split GGP datum (`V = W ⊕^⊥ Z`, `Z = ⟨ν⟩ ⊕ H^r` with `q(z₀) = ν`):
* if `dim V` is even and `≥ 4`, some regular nilpotent `X ∈ gspin(V)` has image `ad X ∈ so(V)` in
  `O_ν` (`IsInOrbitNu`: `V = F d₀ ⊕^⊥ U₁`, `d₀` anisotropic, `U₁ ≅ ⟨ν⟩ ⊕ H^k`, `ad X` kills `d₀`
  and is one Jordan block on `U₁`);
* if `dim W` is even and `≥ 4`, some regular nilpotent `X ∈ gspin(W)` has `ad X ∈ O_{−ν}`.

What the sources give, and what is packaged here. The sources classify `Nil_reg(so(U))` for a
quasi-split even-dimensional `U` by the classes `ν' ∈ 𝒩^U` such that `U ≅ ⟨a⟩ ⊕ ⟨ν'⟩ ⊕ H^{k}`,
the orbit `O_{ν'}` being the orbit of a regular nilpotent of `so(U₁)`, `U₁ = ⟨ν'⟩ ⊕ H^k`, extended
by `0` on `⟨a⟩`; it is a regular orbit of `so(U)` (Jordan type `(dim U − 1, 1)`), and lifts to
`gspin(U) = so(U) ⊕ F` with centralizer of dimension `rank so(U) + 1 = rank gspin(U)`. The axiom
also contains the elementary (Witt-theory) fact that the relevant class is in `𝒩`:
`dim V` even ⇒ `W` odd and quasi-split, hence split, `W = ⟨a⟩ ⊕ W₁` with `W₁` hyperbolic, so
`V = ⟨a⟩ ⊕ (W₁ ⊕ Z)` and `W₁ ⊕ Z ≅ ⟨ν⟩ ⊕ H^{k+r}`; `dim W = 2m' ≥ 4` ⇒ `V` odd quasi-split,
hence `V ≅ ⟨b⟩ ⊕ H^{m'+r}`, and Witt cancellation of `H^r ⊕ ⟨ν⟩` against `⟨ν⟩ ⊕ ⟨−ν⟩ ≅ H` gives
`W ≅ ⟨b⟩ ⊕ ⟨−ν⟩ ⊕ H^{m'−1}`. These are the classes `ν₀ = q(z₀)` (for `V`) and `−ν₀` (for `W`)
used by Luo §7.1.

All hypotheses are explicit binders; for `toyData`
(`dim W = 0`, `dim V = 1`) both conjuncts are vacuous; the smallest non-vacuous cases
(`dim W = 1`, `r = 1`, `dim V = 4`; `dim W = 4`, `r = 0`, `dim V = 5`) agree with the
classification. `ν ≠ 0` (it is a unit) is what makes `U₁ ≠ 0`, so the clause
`(ad X)^{dim U₁ − 1} ≠ 0` on `U₁` is satisfiable. -/
axiom exists_regularNil_inOrbitNu {F : Type*} [NontriviallyNormedField F] [PAdicField F]
    (d : GGPData F) (hqs : d.IsQuasiSplit) :
    (Even (finrank F d.V) → 4 ≤ finrank F d.V →
      ∃ X : CliffordAlgebra d.QV, IsRegularNil (gspin d.QV) X ∧
        IsInOrbitNu d.QV ⊤ (d.ν : F) (adV d.QV X)) ∧
    (Even d.m → 4 ≤ d.m →
      ∃ X : CliffordAlgebra d.QW, IsRegularNil (gspin d.QW) X ∧
        IsInOrbitNu d.QW ⊤ (-(d.ν : F)) (adV d.QW X))

end NilReg

/-! ## (f) Multiplicity one -/

section MultOne

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- **Multiplicity at most one** (Thesis Thm. 5.5.1).
For every GGP datum `d`, nontrivial additive character `ψ`, and irreducible tempered unitary
representation `π` of `G(F)`, `m(π) = dim Hom_{H(F)}(π^∞, ξ) ≤ 1`.

Sources: Emory–Takeda, *Contragredients and a multiplicity one theorem for general spin groups*,
Thm. 1.3 (`r = 0`, codimension one, `p`-adic); the general Bessel case by the reduction of
Beuzart-Plessis (2020) §6.3 and Gan–Gross–Prasad (2012) §15; directly, Pan Yan, *Uniqueness of
Bessel models for GSpin*, arXiv:2503.20116.  The instances on `↥d.G` are the layer-1 theorems of
`Foundations/LocalGroups` (closedness of `G` is `GGPData.isClosed_G`). -/
axiom emoryTakeda_mult_le_one (d : GGPData F) (ψ : NontrivialAddChar F) (π : UnitaryRep ↥d.G) :
    haveI := subgroup_isTopologicalGroup F d.ambient d.G
    haveI := subgroup_t2Space F d.ambient d.G
    haveI := subgroup_locallyCompactSpace_of_isClosed F d.ambient d.G d.isClosed_G
    IsTempered π → multiplicity π d.H (d.xi ψ.toAddChar) ≤ 1

end MultOne

end GSpinGGP
