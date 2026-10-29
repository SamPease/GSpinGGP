import Mathlib

/-!
# Quadratic spaces, general spin groups, GGP triples, inner twists, Whittaker data

Layer-1 foundations for the formalization of *The Local Gan–Gross–Prasad Conjecture for General
Spin Groups* (S. Pease, PhD thesis, Rutgers–Newark 2026, doi:10.7282/t3-qb3s-s249; the "Thesis").

Everything is over a field `K` with `2` invertible.  Groups are *unbundled linear groups*:
an ambient finite-dimensional `K`-algebra, a `Subgroup` of its units (the
`K`-points) and a `LieSubalgebra` of it.

## Contents
* quadratic spaces: `IsNondeg`, `IsTotallyIsotropic`, `wittIndex`, `IsQuasiSplitQF`, `IsSplitQF`,
  `SameDisc`, the split odd space `splitOddForm r ν` with basis `zvec r k` (Thesis (5.2.1));
* Clifford algebras: `Module.Finite`, the module topology, the left inverse `ιInv` of `ι`;
* `GSpin Q` (normalizer form, Thesis §5.1.2), `specP`, `scalarGSpin`, `gspin`,
  `GSpin.map`, `fixedSub`/`movedSub`;
* `IsHypPlane`, `splitCentralGSpin` (the split centre of `GSpin`; `GSpin` of a plane is
  commutative, `isComm_GSpin_of_finrank_eq_two`);
* isotropic flags, `flagStab`, `flagUnip`, and their closedness;
* `GGPData` and the GGP triple `(G, H, ξ)` (Thesis §5.2), the split central torus
  `AG` (with `AG_le_center`, `AG_inf_H`), `dimG`;
* inner twists, stable and strongly stable conjugacy (Thesis §6.1);
* Whittaker data (Thesis §4.4), `IsProperFlagPair`, `isClosed_whittB/U`;
* the central character `CentralCharOn d` of `A_G(F)` (Thesis §7.1).
-/

noncomputable section

open CliffordAlgebra Module
open scoped Matrix
open scoped TensorProduct

/- The commutator Lie structure on associative algebras is only a local instance in Mathlib;
we use the same local instance as `Foundations/LocalGroups.lean`. -/
attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

/-! ## Quadratic spaces -/

section QuadraticSpaces

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The symmetric bilinear form `b` attached to `q`, normalized by `q(v) = b(v,v)`
(Thesis §5.1).  This is Mathlib's `QuadraticMap.associated`. -/
abbrev bform (Q : QuadraticForm K V) : LinearMap.BilinForm K V :=
  QuadraticMap.associated Q

/-- A quadratic space is nondegenerate if its bilinear form is (Thesis §5.1). -/
def IsNondeg (Q : QuadraticForm K V) : Prop :=
  (bform Q).Nondegenerate

/-- A subspace is totally isotropic if `q` vanishes on it (equivalently, as `2` is invertible,
`b` vanishes on it) (Thesis §5.1.2). -/
def IsTotallyIsotropic (Q : QuadraticForm K V) (U : Submodule K V) : Prop :=
  ∀ u ∈ U, Q u = 0

/-- The Witt index: the maximal dimension of a totally isotropic subspace (Thesis §5.1.4).
Mathlib has no Witt index. -/
def wittIndex (Q : QuadraticForm K V) : ℕ :=
  sSup {n | ∃ U : Submodule K V, IsTotallyIsotropic Q U ∧ finrank K U = n}

/-- `GSpin(V)` (equivalently `SO(V)`) is quasi-split iff the anisotropic kernel has dimension
at most `2`, i.e. `dim V - 2 w(V) ≤ 2` (Thesis §5.1.4). -/
def IsQuasiSplitQF (Q : QuadraticForm K V) : Prop :=
  finrank K V ≤ 2 * wittIndex Q + 2

/-- `GSpin(V)` is split iff the anisotropic kernel has dimension at most `1`
(Thesis §5.2: "`GSpin(Z)` split"). -/
def IsSplitQF (Q : QuadraticForm K V) : Prop :=
  finrank K V ≤ 2 * wittIndex Q + 1

/-- `(V, q)` is a hyperbolic plane: nondegenerate of dimension `2` with Witt index `1`.  Then
`C⁺(V) ≅ K × K` and `GSpin(V)` is a two-dimensional split torus, so the split centre of `GSpin(V)`
is all of `GSpin(V)` rather than the scalars `G_m` (used for `A_G`; Thesis §2.1 "split
component"). -/
def IsHypPlane (Q : QuadraticForm K V) : Prop :=
  finrank K V = 2 ∧ IsNondeg Q ∧ wittIndex Q = 1

/-- Two quadratic forms on `K^m` have the same discriminant (in `K^×/K^{×2}`): the ratio of the
Gram determinants is a nonzero square (inner forms have the same dimension and discriminant). -/
def SameDisc {m : ℕ} (Q Q' : QuadraticForm K (Fin m → K)) : Prop :=
  ∃ c : K, c ≠ 0 ∧ Q'.discr' = c ^ 2 * Q.discr'

/-- Nondegeneracy only needs left separation (`b` is symmetric). -/
theorem isNondeg_iff (Q : QuadraticForm K V) :
    IsNondeg Q ↔ ∀ x, (∀ y, bform Q x y = 0) → x = 0 :=
  (LinearMap.IsSymm.isRefl (QuadraticForm.associated_isSymm (S := K) Q)).nondegenerate_iff_separatingLeft

/-- `polar q = 2 b`. -/
theorem polar_eq_two_mul_bform (Q : QuadraticForm K V) (x y : V) :
    QuadraticMap.polar Q x y = 2 * bform Q x y := by
  have h := congr($(QuadraticMap.two_nsmul_associated K Q) x y)
  simp only [LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply] at h
  rw [← h, two_nsmul, two_mul]

/-- Gram matrix of the split odd space `Z` of dimension `2r+1`: index `i : Fin (2r+1)` stands for
`z_{i-r}`, and `b(z_i, z_j) = ν δ_{i,-j}` (Thesis (5.2.1)). -/
def splitOddMatrix (r : ℕ) (ν : K) : Matrix (Fin (2 * r + 1)) (Fin (2 * r + 1)) K :=
  fun i j => if (i : ℕ) + (j : ℕ) = 2 * r then ν else 0

/-- The split odd quadratic space `Z = ⟨z_{-r}, …, z_r⟩`, `b(z_i,z_j) = ν δ_{i,-j}`,
`q(v) = b(v,v)` (Thesis (5.2.1)). -/
def splitOddForm (r : ℕ) (ν : K) : QuadraticForm K (Fin (2 * r + 1) → K) :=
  Matrix.toQuadraticForm' (splitOddMatrix r ν)

/-- The basis vector `z_k` of `Z` (`k ∈ {-r, …, r}`; for `|k| > r` this is `0`)
(Thesis (5.2.1)). -/
def zvec (r : ℕ) (k : ℤ) : Fin (2 * r + 1) → K :=
  fun i => if ((i : ℕ) : ℤ) - r = k then 1 else 0

omit [Invertible (2 : K)] in
theorem splitOddMatrix_symm (r : ℕ) (ν : K) (i j : Fin (2 * r + 1)) :
    splitOddMatrix r ν i j = splitOddMatrix r ν j i := by
  simp only [splitOddMatrix, add_comm]

/-- The bilinear form of `Z` in coordinates: `b(x, y) = xᵀ M y`. -/
theorem bform_splitOddForm (r : ℕ) (ν : K) (x y : Fin (2 * r + 1) → K) :
    bform (splitOddForm r ν) x y = x ⬝ᵥ (splitOddMatrix r ν *ᵥ y) := by
  unfold splitOddForm Matrix.toQuadraticForm'
  dsimp only [bform, QuadraticMap.associated]
  rw [QuadraticMap.associated_left_inverse]
  · simp [Matrix.toLinearMap₂'_apply']
  · intro x y
    have hT : (splitOddMatrix r ν)ᵀ = splitOddMatrix r ν := by
      ext a b
      exact splitOddMatrix_symm r ν b a
    simp only [Matrix.toLinearMap₂'_apply']
    rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hT]

omit [Invertible (2 : K)] in
theorem zvec_eq_single (r : ℕ) {k : ℤ} (hk : |k| ≤ r) :
    (zvec r k : Fin (2 * r + 1) → K) =
      Pi.single ⟨(k + r).toNat, by have := abs_le.mp hk; omega⟩ 1 := by
  ext i
  simp only [zvec, Pi.single_apply, Fin.ext_iff]
  congr 1
  apply propext
  rw [abs_le] at hk
  omega

/-- Thesis (5.2.1): `b(z_i, z_j) = ν δ_{i,-j}`. -/
theorem bform_splitOddForm_zvec (r : ℕ) (ν : K) {i j : ℤ} (hi : |i| ≤ r) (hj : |j| ≤ r) :
    bform (splitOddForm r ν) (zvec r i) (zvec r j) = if i + j = 0 then ν else 0 := by
  rw [bform_splitOddForm, zvec_eq_single r hi, zvec_eq_single r hj, Matrix.mulVec_single,
    single_dotProduct]
  rw [abs_le] at hi hj
  simp only [Matrix.col, MulOpposite.op_one, one_smul]
  rw [one_mul, Matrix.transpose_apply]
  simp only [splitOddMatrix]
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)

/-- `Z` is nondegenerate when `ν ≠ 0`. -/
theorem isNondeg_splitOddForm (r : ℕ) {ν : K} (hν : ν ≠ 0) : IsNondeg (splitOddForm r ν) := by
  rw [isNondeg_iff]
  intro x hx
  ext a
  have h := hx (Pi.single ⟨2 * r - a, by omega⟩ 1)
  rw [bform_splitOddForm, Matrix.mulVec_single, dotProduct, Finset.sum_eq_single a] at h
  · have ha : (a : ℕ) + (2 * r - a) = 2 * r := by omega
    simpa [Matrix.col, splitOddMatrix, ha, hν] using h
  · intro b _ hb
    have hb' : ¬ ((b : ℕ) + (2 * r - a) = 2 * r) := fun h' => hb (Fin.ext (by omega))
    simp [Matrix.col, splitOddMatrix, hb']
  · simp

/-- The bilinear form of an orthogonal direct sum. -/
theorem bform_prod {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
    [Module K V₂] (Q₁ : QuadraticForm K V₁) (Q₂ : QuadraticForm K V₂) (x y : V₁ × V₂) :
    bform (Q₁.prod Q₂) x y = bform Q₁ x.1 y.1 + bform Q₂ x.2 y.2 := by
  simp [bform, QuadraticMap.associated_prod]

/-- An orthogonal direct sum of nondegenerate spaces is nondegenerate. -/
theorem isNondeg_prod {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
    [Module K V₂] {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (h₁ : IsNondeg Q₁)
    (h₂ : IsNondeg Q₂) : IsNondeg (Q₁.prod Q₂) := by
  rw [isNondeg_iff] at h₁ h₂ ⊢
  intro x hx
  ext
  · exact h₁ x.1 fun y => by simpa [bform_prod] using hx (y, 0)
  · exact h₂ x.2 fun y => by simpa [bform_prod] using hx (0, y)

omit [Invertible (2 : K)] in
/-- `Z` is split (Thesis §5.2). -/
theorem isSplitQF_splitOddForm (r : ℕ) {ν : K} (_hν : ν ≠ 0) : IsSplitQF (splitOddForm r ν) := by
  -- `U = ⟨z_1, …, z_r⟩` is totally isotropic of dimension `r`
  let f : Fin r → Fin (2 * r + 1) := fun j => ⟨2 * r - j, by omega⟩
  have hf : Function.Injective f := fun a b h => Fin.ext (by
    have := congrArg Fin.val h; simp only [f] at this; omega)
  let U : Submodule K (Fin (2 * r + 1) → K) :=
    Submodule.span K (Set.range fun j => Pi.basisFun K (Fin (2 * r + 1)) (f j))
  have hli : LinearIndependent K (fun j => Pi.basisFun K (Fin (2 * r + 1)) (f j)) :=
    (Pi.basisFun K (Fin (2 * r + 1))).linearIndependent.comp f hf
  have hU : finrank K U = r := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hsupp : ∀ u ∈ U, ∀ n : Fin (2 * r + 1), (n : ℕ) < r + 1 → u n = 0 := by
    intro u hu
    refine Submodule.span_induction (p := fun u _ => ∀ n : Fin (2 * r + 1), (n : ℕ) < r + 1 →
      u n = 0) ?_ (fun _ _ => rfl) (fun x y _ _ hx hy n hn => by simp [hx n hn, hy n hn])
      (fun c x _ hx n hn => by simp [hx n hn]) hu
    rintro _ ⟨j, rfl⟩ n hn
    simp only [Pi.basisFun_apply, Pi.single_apply]
    split_ifs with h
    · subst h; simp only [f] at hn; omega
    · rfl
  have hiso : IsTotallyIsotropic (splitOddForm r ν) U := by
    intro u hu
    have h2 := hsupp u hu
    simp only [splitOddForm, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec, splitOddMatrix]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : (a : ℕ) < r + 1
    · rw [h2 a ha, zero_mul]
    · rw [Finset.sum_eq_zero, mul_zero]
      intro b _
      by_cases hb : (b : ℕ) < r + 1
      · rw [h2 b hb, mul_zero]
      · split_ifs with h
        · omega
        · rw [zero_mul]
  have hbdd : BddAbove {n | ∃ U : Submodule K (Fin (2 * r + 1) → K),
      IsTotallyIsotropic (splitOddForm r ν) U ∧ finrank K U = n} :=
    ⟨2 * r + 1, by
      rintro _ ⟨U', -, rfl⟩
      calc finrank K U' ≤ finrank K (Fin (2 * r + 1) → K) := Submodule.finrank_le U'
        _ = 2 * r + 1 := Module.finrank_fin_fun K⟩
  have hw : r ≤ wittIndex (splitOddForm r ν) := le_csSup hbdd ⟨U, hiso, hU⟩
  unfold IsSplitQF
  rw [Module.finrank_fin_fun]
  omega

end QuadraticSpaces

/-! ## Clifford algebras: finiteness, topology, the inverse of `ι` -/

section Clifford

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The exterior algebra of a finite-dimensional space is finite-dimensional
(basis indexed by `Finset (Fin n)`). -/
instance instFiniteExteriorAlgebra [Module.Finite K V] : Module.Finite K (ExteriorAlgebra K V) :=
  Module.Finite.of_basis (Module.finBasis K V).ExteriorAlgebra

/-- `dim C(V) = 2^{dim V} < ∞` (Thesis §5.1.1).  Not in Mathlib; we transport finiteness of the
exterior algebra along `CliffordAlgebra.equivExterior` (characteristic `≠ 2`). -/
instance instFiniteCliffordAlgebra [Module.Finite K V] (Q : QuadraticForm K V) :
    Module.Finite K (CliffordAlgebra Q) :=
  Module.Finite.equiv (equivExterior Q).symm

/-- The Clifford algebra over a topological field carries the module topology. -/
instance instTopologicalSpaceCliffordAlgebra {R : Type*} [CommRing R] [TopologicalSpace R]
    {M : Type*} [AddCommGroup M] [Module R M] (Q : QuadraticForm R M) :
    TopologicalSpace (CliffordAlgebra Q) :=
  moduleTopology R _

instance instIsModuleTopologyCliffordAlgebra {R : Type*} [CommRing R] [TopologicalSpace R]
    {M : Type*} [AddCommGroup M] [Module R M] (Q : QuadraticForm R M) :
    IsModuleTopology R (CliffordAlgebra Q) :=
  ⟨rfl⟩

/-- The Clifford algebra of a finite-dimensional space over a topological field is a topological
ring for the module topology. -/
instance instIsTopologicalRingCliffordAlgebra [TopologicalSpace K] [IsTopologicalRing K]
    [Module.Finite K V] (Q : QuadraticForm K V) : IsTopologicalRing (CliffordAlgebra Q) :=
  IsModuleTopology.isTopologicalRing K _

/-- A left inverse of `ι : V → C(V)` (characteristic `≠ 2`), via the exterior algebra. -/
def ιInv (Q : QuadraticForm K V) : CliffordAlgebra Q →ₗ[K] V :=
  ExteriorAlgebra.ιInv ∘ₗ (equivExterior Q).toLinearMap

@[simp] theorem ιInv_ι (Q : QuadraticForm K V) (v : V) : ιInv Q (ι Q v) = v := by
  simp only [ιInv, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  unfold equivExterior
  erw [changeFormEquiv_apply, changeForm_ι]
  exact ExteriorAlgebra.ι_leftInverse v

theorem ι_injective (Q : QuadraticForm K V) : Function.Injective (ι Q) :=
  Function.LeftInverse.injective (ιInv_ι Q)

end Clifford

/-! ## The centre of the Clifford algebra

An even element of `C(V)` commuting with every vector is a scalar (`V` nondegenerate).  The proof
uses the identity `ι(v) x − x̂ ι(v) = polar(v,·) ⌋ x` (contraction), transports to the exterior
algebra via `equivExterior`, and there shows that an element killed by all contractions is a
scalar, with the commuting idempotent-like operators `1 − ι(bᵢ)·(bᵢ* ⌋ ·)`, which avoids any
characteristic-dependent Euler-operator argument. -/

section CliffordCentre

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- `ι v * x - involute x * ι v = polar(v, ·) ⌋ x`. -/
theorem ι_mul_sub_involute_mul (Q : QuadraticForm K V) (v : V) (x : CliffordAlgebra Q) :
    ι Q v * x - involute x * ι Q v =
      CliffordAlgebra.contractLeft (QuadraticMap.polarBilin Q v) x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [Algebra.commutes]
  | add x y hx hy => rw [mul_add, map_add, add_mul, map_add, ← hx, ← hy]; abel
  | ι_mul x a hx =>
    rw [contractLeft_ι_mul, ← hx, map_mul, involute_ι]
    simp only [QuadraticMap.polarBilin_apply_apply]
    have h := ι_mul_ι_add_swap (Q := Q) v a
    rw [← mul_assoc, eq_sub_of_add_eq h, Algebra.smul_def]
    simp only [sub_mul, mul_sub, neg_mul, mul_assoc]
    abel

/-- In the exterior algebra of a finite-dimensional space, an element killed by every contraction
`d ⌋ ·` is a scalar.  Characteristic-free: with a basis `bᵢ`, the operators
`hᵢ = ι(bᵢ) · (bᵢ* ⌋ ·)` satisfy `(1 − hᵢ)(ι(bᵢ) y) = 0` and `(1 − hᵢ)(ι(bⱼ) y) = ι(bⱼ)(1 − hᵢ) y`
for `j ≠ i`, so `∏ᵢ (1 − hᵢ)` maps everything to scalars and fixes `X`. -/
theorem exterior_mem_range_of_contractLeft [Module.Finite K V]
    (X : ExteriorAlgebra K V) (hX : ∀ d : Module.Dual K V, CliffordAlgebra.contractLeft d X = 0) :
    ∃ r : K, X = algebraMap K _ r := by
  classical
  let b := Module.finBasis K V
  let n := finrank K V
  let h : Fin n → Module.End K (ExteriorAlgebra K V) := fun i =>
    LinearMap.mulLeft K (ExteriorAlgebra.ι K (b i)) ∘ₗ CliffordAlgebra.contractLeft (b.coord i)
  let T : List (Fin n) → Module.End K (ExteriorAlgebra K V) := fun L =>
    (L.map fun i => (1 - h i)).prod
  have anti : ∀ i j, ExteriorAlgebra.ι K (b i) * ExteriorAlgebra.ι K (b j) =
      -(ExteriorAlgebra.ι K (b j) * ExteriorAlgebra.ι K (b i)) := fun i j => by
    have := ι_mul_ι_add_swap (Q := (0 : QuadraticForm K V)) (b i) (b j)
    rw [show QuadraticMap.polar (0 : QuadraticForm K V) (b i) (b j) = 0 by
      simp [QuadraticMap.polar], map_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  have sq : ∀ i, ExteriorAlgebra.ι K (b i) * ExteriorAlgebra.ι K (b i) = 0 := fun i =>
    ExteriorAlgebra.ι_sq_zero _
  have kill : ∀ j Z, (1 - h j) (ExteriorAlgebra.ι K (b j) * Z) = 0 := fun j Z => by
    simp only [h, LinearMap.sub_apply, Module.End.one_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.mulLeft_apply]
    erw [contractLeft_ι_mul]
    rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same, one_smul, mul_sub,
      ← mul_assoc, sq, zero_mul, sub_zero, sub_self]
  have comm : ∀ i j, i ≠ j → ∀ Z, (1 - h i) (ExteriorAlgebra.ι K (b j) * Z) =
      ExteriorAlgebra.ι K (b j) * (1 - h i) Z := fun i j hij Z => by
    simp only [h, LinearMap.sub_apply, Module.End.one_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.mulLeft_apply]
    erw [contractLeft_ι_mul]
    rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne hij, zero_smul,
      zero_sub, mul_neg, ← mul_assoc]
    erw [anti i j]
    rw [neg_mul, neg_neg, mul_sub, mul_assoc]
  have hT : ∀ L : List (Fin n), ∀ j Z, T L (ExteriorAlgebra.ι K (b j) * Z) =
      if j ∈ L then 0 else ExteriorAlgebra.ι K (b j) * T L Z := by
    intro L
    induction L with
    | nil => intro j Z; simp [T]
    | cons a L ih =>
      intro j Z
      simp only [T, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
      rw [ih j Z]
      by_cases hjL : j ∈ L
      · simp [hjL]
      · simp only [hjL, ite_false]
        by_cases hja : j = a
        · subst hja; simp [kill]
        · rw [comm a j (Ne.symm hja)]
          simp [hja, hjL]
  have hT1 : ∀ L : List (Fin n), ∀ r : K, T L (algebraMap K _ r) = algebraMap K _ r := by
    intro L r
    induction L with
    | nil => simp [T]
    | cons a L ih =>
      simp only [T, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
      rw [ih]
      simp [h, contractLeft_algebraMap]
  have hTfix : ∀ L : List (Fin n), T L X = X := by
    intro L
    induction L with
    | nil => simp [T]
    | cons a L ih =>
      simp only [T, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
      rw [ih]
      simp [h, hX]
  have hrange : ∀ Y, ∃ r : K, T (List.finRange n) Y = algebraMap K _ r := by
    intro Y
    induction Y using CliffordAlgebra.left_induction with
    | algebraMap r => exact ⟨r, hT1 _ r⟩
    | add x y hx hy =>
      obtain ⟨r, hr⟩ := hx; obtain ⟨s, hs⟩ := hy
      exact ⟨r + s, by rw [map_add, hr, hs, map_add]⟩
    | ι_mul x m _ =>
      refine ⟨0, ?_⟩
      rw [← b.sum_repr m, map_sum, Finset.sum_mul, map_sum, map_zero]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smul, smul_mul_assoc, map_smul]
      erw [hT (List.finRange n) j x]
      simp
  obtain ⟨r, hr⟩ := hrange X
  exact ⟨r, by rw [← hr, hTfix]⟩


variable [Invertible (2 : K)]

/-- An even element of `C(V)` commuting with `ι(V)` is a scalar, for nondegenerate
finite-dimensional `V` (the even part of the centre of `C(V)` is `K`). -/
theorem eq_algebraMap_of_commute_ι [Module.Finite K V] {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    {x : CliffordAlgebra Q} (hx0 : x ∈ evenOdd Q 0) (hx : ∀ v, ι Q v * x = x * ι Q v) :
    ∃ r : K, x = algebraMap K _ r := by
  have hc : ∀ d : Module.Dual K V, CliffordAlgebra.contractLeft d x = 0 := by
    intro d
    obtain ⟨w, rfl⟩ := ((bform Q).toDual hQ).surjective d
    have hpol : QuadraticMap.polarBilin Q ((⅟2 : K) • w) = (bform Q).toDual hQ w := by
      ext y
      change _ = bform Q w y
      rw [bform, QuadraticMap.associated_apply,
        QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_smul_left, smul_eq_mul]
      simp [invOf_eq_inv, QuadraticMap.polar]
    rw [← hpol, ← ι_mul_sub_involute_mul, involute_eq_of_mem_even hx0, hx, sub_self]
  set X := equivExterior Q x
  have hX : ∀ d : Module.Dual K V, CliffordAlgebra.contractLeft d X = 0 := fun d => by
    simp only [X, equivExterior, changeFormEquiv_apply]
    rw [← changeForm_contractLeft, hc, map_zero]
  obtain ⟨r, hr⟩ := exterior_mem_range_of_contractLeft X hX
  refine ⟨r, ?_⟩
  have := congrArg (equivExterior Q).symm hr
  rw [LinearEquiv.symm_apply_apply] at this
  rw [this]
  simp [equivExterior, changeFormEquiv_symm]

end CliffordCentre

/-! ## The general spin group -/

section GSpinGroup

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The general spin group, in normalizer form (Thesis §5.1.2):
`GSpin(V) = {g ∈ C⁺(V)^× | g V g⁻¹ = V}`.  We impose both `g V g⁻¹ ⊆ V` and `g⁻¹ V g ⊆ V`, which
together are `g V g⁻¹ = V` and make the set visibly closed under inverses.  Mathlib's
`spinGroup`/`pinGroup` (unit Clifford norm) are *not* this group. -/
def GSpin (Q : QuadraticForm K V) : Subgroup (CliffordAlgebra Q)ˣ where
  carrier := {g | (g : CliffordAlgebra Q) ∈ even Q ∧
    (∀ v, (g : CliffordAlgebra Q) * ι Q v * ((g⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
      LinearMap.range (ι Q)) ∧
    (∀ v, ((g⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q v * (g : CliffordAlgebra Q) ∈
      LinearMap.range (ι Q))}
  one_mem' := ⟨Subalgebra.one_mem _, fun v => ⟨v, by simp⟩, fun v => ⟨v, by simp⟩⟩
  mul_mem' := by
    rintro g h ⟨hg0, hg1, hg2⟩ ⟨hh0, hh1, hh2⟩
    refine ⟨by simpa using Subalgebra.mul_mem _ hg0 hh0, fun v => ?_, fun v => ?_⟩
    · obtain ⟨w, hw⟩ := hh1 v
      have : ((g * h : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q v *
          (((g * h)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
          (g : CliffordAlgebra Q) * ((h : CliffordAlgebra Q) * ι Q v *
            ((h⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) *
            ((g⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
        simp [mul_inv_rev, mul_assoc]
      rw [this, ← hw]
      exact hg1 w
    · obtain ⟨w, hw⟩ := hg2 v
      have : (((g * h)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q v *
          ((g * h : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
          ((h⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
            (((g⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q v *
              (g : CliffordAlgebra Q)) * (h : CliffordAlgebra Q) := by
        simp [mul_inv_rev, mul_assoc]
      rw [this, ← hw]
      exact hh2 w
  inv_mem' := by
    rintro g ⟨hg0, hg1, hg2⟩
    refine ⟨?_, fun v => by simpa using hg2 v, fun v => by simpa using hg1 v⟩
    -- the inverse of an even unit is even: its odd component `b₁` satisfies `g b₁ = 0`
    rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hg0 ⊢
    set a : CliffordAlgebra Q := (g : CliffordAlgebra Q)
    set b : CliffordAlgebra Q := ((g⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
    have hab : a * b = 1 := Units.mul_inv g
    have hba : b * a = 1 := Units.inv_mul g
    have h1 : (DirectSum.decompose (evenOdd Q) b 1 : CliffordAlgebra Q) = 0 := by
      have h := DirectSum.coe_decompose_mul_of_left_mem_zero (𝒜 := evenOdd Q) (b := b)
        (j := (1 : ZMod 2)) hg0
      rw [hab, DirectSum.decompose_of_mem_ne (evenOdd Q) (SetLike.one_mem_graded (evenOdd Q))
        (by decide : (0 : ZMod 2) ≠ 1)] at h
      calc (DirectSum.decompose (evenOdd Q) b 1 : CliffordAlgebra Q)
          = b * (a * (DirectSum.decompose (evenOdd Q) b 1 : CliffordAlgebra Q)) := by
            rw [← mul_assoc, hba, one_mul]
        _ = 0 := by rw [← h, mul_zero]
    have hb : DirectSum.decompose (evenOdd Q) b =
        DirectSum.of _ 0 (DirectSum.decompose (evenOdd Q) b 0) := by
      ext i : 1
      by_cases hi : i = 0
      · subst hi; rw [DirectSum.of_eq_same]
      · obtain rfl : i = 1 := (by decide : ∀ j : ZMod 2, j ≠ 0 → j = 1) i hi
        rw [DirectSum.of_eq_of_ne _ _ _ hi]
        exact Subtype.ext h1
    have : b = (DirectSum.decompose (evenOdd Q) b 0 : CliffordAlgebra Q) := by
      conv_lhs => rw [← (DirectSum.decompose (evenOdd Q)).symm_apply_apply b, hb,
        DirectSum.decompose_symm_of]
    rw [this]
    exact (DirectSum.decompose (evenOdd Q) b 0).2

variable [Invertible (2 : K)]

omit [Invertible (2 : K)] in
/-- Every subspace of a finite-dimensional module with the module topology over a Hausdorff
topological field is closed (it is cut out by finitely many continuous linear functionals). -/
theorem isClosed_submodule_of_moduleTopology [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] {M : Type*} [AddCommGroup M] [Module K M] [Module.Finite K M] [TopologicalSpace M]
    [IsModuleTopology K M] (S : Submodule K M) : IsClosed (S : Set M) := by
  let b := Module.finBasis K (M ⧸ S)
  have h : (S : Set M) = ⋂ i, (fun x => b.coord i (S.mkQ x)) ⁻¹' {0} := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    rw [b.forall_coord_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [h]
  exact isClosed_iInter fun i => isClosed_singleton.preimage
    (IsModuleTopology.continuous_of_linearMap ((b.coord i) ∘ₗ S.mkQ))

/-- `GSpin(V)` is closed in `C(V)^×` (it is the set of `K`-points of an algebraic group).
`K` must be Hausdorff: for the indiscrete topology on `K` the statement is false. -/
theorem isClosed_GSpin [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] [Module.Finite K V]
    (Q : QuadraticForm K V) : IsClosed (GSpin Q : Set (CliffordAlgebra Q)ˣ) := by
  have hcl := fun S : Submodule K (CliffordAlgebra Q) => isClosed_submodule_of_moduleTopology S
  have hval : Continuous (fun g : (CliffordAlgebra Q)ˣ => (g : CliffordAlgebra Q)) :=
    Units.continuous_val
  have hinv : Continuous (fun g : (CliffordAlgebra Q)ˣ =>
      ((g⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) := Units.continuous_coe_inv
  have h : (GSpin Q : Set (CliffordAlgebra Q)ˣ) =
      ((fun g : (CliffordAlgebra Q)ˣ => (g : CliffordAlgebra Q)) ⁻¹'
          (Subalgebra.toSubmodule (even Q) : Set (CliffordAlgebra Q))) ∩
        (⋂ v, (fun g : (CliffordAlgebra Q)ˣ => (g : CliffordAlgebra Q) * ι Q v *
          ((g⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) ⁻¹'
            (LinearMap.range (ι Q) : Set (CliffordAlgebra Q))) ∩
        (⋂ v, (fun g : (CliffordAlgebra Q)ˣ => ((g⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
          ι Q v * (g : CliffordAlgebra Q)) ⁻¹'
            (LinearMap.range (ι Q) : Set (CliffordAlgebra Q))) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter,
      Subalgebra.mem_toSubmodule]
    exact ⟨fun ⟨h0, h1, h2⟩ => ⟨⟨h0, h1⟩, h2⟩, fun ⟨⟨h0, h1⟩, h2⟩ => ⟨h0, h1, h2⟩⟩
  rw [h]
  refine ((hcl _).preimage hval).inter (isClosed_iInter fun v => (hcl _).preimage ?_) |>.inter
    (isClosed_iInter fun v => (hcl _).preimage ?_)
  · exact (hval.mul continuous_const).mul hinv
  · exact (hinv.mul continuous_const).mul hval

/-- Conjugation `v ↦ ι⁻¹(g ι(v) g⁻¹)`, a linear endomorphism of `V`. -/
def conjV (Q : QuadraticForm K V) (g : (CliffordAlgebra Q)ˣ) : V →ₗ[K] V :=
  ιInv Q ∘ₗ (LinearMap.mulLeft K (g : CliffordAlgebra Q) ∘ₗ
    LinearMap.mulRight K ((g⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) ∘ₗ ι Q

theorem ι_conjV {Q : QuadraticForm K V} {g : (CliffordAlgebra Q)ˣ} (hg : g ∈ GSpin Q) (v : V) :
    ι Q (conjV Q g v) =
      (g : CliffordAlgebra Q) * ι Q v * ((g⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  obtain ⟨w, hw⟩ := hg.2.1 v
  have : conjV Q g v = w := by
    simp only [conjV, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
      LinearMap.mulLeft_apply]
    rw [← mul_assoc, ← hw, ιInv_ι]
  rw [this, hw]

/-- The canonical projection `P : GSpin(V) → SO(V)`, `P(g)v = g v g⁻¹` (Thesis §5.1.2). -/
def specP (Q : QuadraticForm K V) : GSpin Q →* (V ≃ₗ[K] V) where
  toFun g := LinearEquiv.ofLinearMap (conjV Q g) (conjV Q (g⁻¹ : GSpin Q))
    (by
      ext v
      apply ι_injective Q
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
      rw [ι_conjV g.2, ι_conjV (g⁻¹ : GSpin Q).2]
      simp [mul_assoc])
    (by
      ext v
      apply ι_injective Q
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
      rw [ι_conjV (g⁻¹ : GSpin Q).2, ι_conjV g.2]
      simp [mul_assoc])
  map_one' := by
    ext v
    apply ι_injective Q
    change ι Q (conjV Q ((1 : GSpin Q) : (CliffordAlgebra Q)ˣ) v) = ι Q v
    rw [ι_conjV (1 : GSpin Q).2]
    simp
  map_mul' g h := by
    ext v
    apply ι_injective Q
    change ι Q (conjV Q ((g * h : GSpin Q) : (CliffordAlgebra Q)ˣ) v) =
      ι Q (conjV Q (g : (CliffordAlgebra Q)ˣ) (conjV Q (h : (CliffordAlgebra Q)ˣ) v))
    rw [ι_conjV (g * h).2, ι_conjV g.2, ι_conjV h.2]
    simp [mul_assoc]

theorem specP_apply_eq {Q : QuadraticForm K V} (g : GSpin Q) (v : V) :
    specP Q g v = ιInv Q (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * (ι Q v *
      (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))) :=
  rfl

theorem ι_specP {Q : QuadraticForm K V} (g : GSpin Q) (v : V) :
    ι Q (specP Q g v) = ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q v *
      (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) :=
  ι_conjV g.2 v

/-- `P(g)` is an isometry of `(V, q)` (Thesis §5.1.2). -/
theorem specP_isometry {Q : QuadraticForm K V} (g : GSpin Q) (v : V) :
    Q (specP Q g v) = Q v := by
  apply (algebraMap K (CliffordAlgebra Q)).injective
  rw [← ι_sq_scalar, ← ι_sq_scalar, ι_specP]
  set a : CliffordAlgebra Q := ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  set b : CliffordAlgebra Q :=
    (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  have hba : b * a = 1 := Units.inv_mul _
  have hab : a * b = 1 := Units.mul_inv _
  calc a * ι Q v * b * (a * ι Q v * b) = a * (ι Q v * ι Q v) * b := by
        rw [show a * ι Q v * b * (a * ι Q v * b) = a * ι Q v * (b * a) * ι Q v * b by
          simp only [mul_assoc], hba, mul_one, mul_assoc a, mul_assoc a]
    _ = ι Q v * ι Q v := by
        rw [ι_sq_scalar, ← Algebra.commutes, mul_assoc, hab, mul_one]

theorem specP_mul_apply {Q : QuadraticForm K V} (g h : GSpin Q) (v : V) :
    specP Q (g * h) v = specP Q g (specP Q h v) := by
  rw [map_mul]; rfl

theorem specP_inv_apply_apply {Q : QuadraticForm K V} (g : GSpin Q) (v : V) :
    specP Q g (specP Q g⁻¹ v) = v := by
  rw [← specP_mul_apply, mul_inv_cancel, map_one]; rfl

/-- `P(g)` preserves the bilinear form (Thesis §5.1.2). -/
theorem bform_specP {Q : QuadraticForm K V} (g : GSpin Q) (x y : V) :
    bform Q (specP Q g x) (specP Q g y) = bform Q x y := by
  have h : QuadraticMap.polar Q (specP Q g x) (specP Q g y) = QuadraticMap.polar Q x y := by
    simp only [QuadraticMap.polar, ← map_add, specP_isometry]
  rw [polar_eq_two_mul_bform, polar_eq_two_mul_bform] at h
  exact mul_left_cancel₀ (Invertible.ne_zero (2 : K)) h

omit [Invertible (2 : K)] in
/-- A contraction vanishing on each factor kills a product of vectors. -/
theorem contractLeft_prod_eq_zero {Q : QuadraticForm K V} (d : Module.Dual K V) (l : List V)
    (hl : ∀ a ∈ l, d a = 0) : CliffordAlgebra.contractLeft d (l.map (ι Q)).prod = 0 := by
  induction l with
  | nil => simp [contractLeft_one]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, contractLeft_ι_mul, hl a (by simp), zero_smul, zero_sub,
      ih (fun b hb => hl b (by simp [hb])), mul_zero, neg_zero]

omit [Invertible (2 : K)] in
/-- `changeForm` is multiplicative on products of pairwise `B`-orthogonal vectors. -/
theorem changeForm_prod_of_pairwise {Q Q' : QuadraticForm K V} {B : LinearMap.BilinForm K V}
    (h : B.toQuadraticMap = Q' - Q) (l : List V) (hl : l.Pairwise fun a b => B a b = 0) :
    changeForm h (l.map (ι Q)).prod = (l.map (ι Q')).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    rw [List.map_cons, List.prod_cons, changeForm_ι_mul, ih hl.2, List.map_cons, List.prod_cons,
      contractLeft_prod_eq_zero _ _ hl.1, sub_zero]

omit [Invertible (2 : K)] in
/-- Commuting a fixed element past a product, picking up central scalars. -/
theorem mul_prod_map_eq {A ι' : Type*} [Ring A] [Algebra K A] (X : A) (f : ι' → A) (σ : ι' → K)
    (hσ : ∀ i, X * f i = algebraMap K A (σ i) * f i * X) (l : List ι') :
    X * (l.map f).prod = algebraMap K A (l.map σ).prod * (l.map f).prod * X := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul]
    rw [← mul_assoc, hσ, mul_assoc _ (f a) X, mul_assoc, mul_assoc, ih,
      ← mul_assoc (f a), ← mul_assoc (f a), ← Algebra.commutes (l.map σ).prod (f a)]
    simp only [mul_assoc]

omit [Invertible (2 : K)] in
/-- Conjugation of a product. -/
theorem conj_prod_map {A ι' : Type*} [Ring A] (g : Aˣ) (f : ι' → A) (l : List ι') :
    (g : A) * (l.map f).prod * ((g⁻¹ : Aˣ) : A) =
      (l.map fun i => (g : A) * f i * ((g⁻¹ : Aˣ) : A)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, ← ih]
    simp only [mul_assoc, Units.inv_mul_cancel_left]

/-- `P(g)` has determinant one, i.e. `P : GSpin(V) → SO(V)` (Thesis §5.1.2).
No nondegeneracy is needed.  Proof: take a `b`-orthogonal basis `e` and `ω = ι(e₁)⋯ι(eₙ)`; `ω`
commutes with even elements, so `g ω g⁻¹ = ω`, while `g ω g⁻¹ = ι(P e₁)⋯ι(P eₙ)`.  Products of
pairwise orthogonal vectors go to wedge products under `C(V) ≅ Λ(V)`, and pairing the top degree
with `e.det` gives `det P = 1`. -/
theorem det_specP [Module.Finite K V] {Q : QuadraticForm K V} (g : GSpin Q) :
    LinearMap.det (specP Q g : V →ₗ[K] V) = 1 := by
  classical
  set n := finrank K V
  obtain ⟨e, he⟩ : ∃ e : Basis (Fin n) K V, (bform Q).IsOrthoᵢ e :=
    LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm (S := K) Q)
  set P : V →ₗ[K] V := (specP Q g : V →ₗ[K] V) with hP
  have hneg : QuadraticMap.associated (-Q) = -bform Q := by
    ext a b
    simp only [bform, QuadraticMap.associated_apply, LinearMap.neg_apply, neg_apply]
    rw [← smul_neg]; congr 1; ring
  -- the functional `Λ`: top exterior coefficient against `e.det`
  let F : ∀ i, V [⋀^Fin i]→ₗ[K] K := Function.update 0 n e.det
  let Λ : CliffordAlgebra Q →ₗ[K] K :=
    ExteriorAlgebra.liftAlternating F ∘ₗ (equivExterior Q).toLinearMap
  have hΛ : ∀ w : Fin n → V, (∀ i j, i ≠ j → bform Q (w i) (w j) = 0) →
      Λ ((List.ofFn fun i => ι Q (w i)).prod) = e.det w := by
    intro w hw
    have hpw : (List.ofFn w).Pairwise fun a b => QuadraticMap.associated (-Q) a b = 0 := by
      rw [List.pairwise_ofFn]
      intro i j hij
      rw [hneg, LinearMap.neg_apply, LinearMap.neg_apply, hw i j hij.ne, neg_zero]
    have e1 : (List.ofFn fun i => ι Q (w i)) = (List.ofFn w).map (ι Q) := by
      rw [List.map_ofFn]; rfl
    simp only [Λ, LinearMap.comp_apply, LinearEquiv.coe_coe, equivExterior, changeFormEquiv_apply]
    rw [e1, changeForm_prod_of_pairwise _ _ hpw, List.map_ofFn]
    have e2 : ((List.ofFn ((ι (0 : QuadraticForm K V)) ∘ w)).prod : ExteriorAlgebra K V) =
        ExteriorAlgebra.ιMulti K n w := by
      rw [ExteriorAlgebra.ιMulti_apply]; rfl
    rw [e2, ExteriorAlgebra.liftAlternating_apply_ιMulti]
    simp [F]
  -- `ω = e₁ ⋯ eₙ` and its commutation with vectors
  set ω : CliffordAlgebra Q := (List.ofFn fun i => ι Q (e i)).prod with hω
  set s : K := (-1) ^ (n - 1)
  have hωj : ∀ j, ι Q (e j) * ω = algebraMap K _ s * ω * ι Q (e j) := by
    intro j
    let σ : Fin n → K := fun i => if i = j then 1 else -1
    have hσ : ∀ i, ι Q (e j) * ι Q (e i) = algebraMap K _ (σ i) * ι Q (e i) * ι Q (e j) := by
      intro i
      by_cases hij : i = j
      · subst hij; simp [σ]
      · have h1 := ι_mul_ι_add_swap (Q := Q) (e j) (e i)
        have hb : bform Q (e j) (e i) = 0 := he (Ne.symm hij)
        rw [polar_eq_two_mul_bform, hb, mul_zero, map_zero] at h1
        simp only [σ, hij, ite_false, map_neg, map_one, neg_mul, one_mul]
        exact eq_neg_of_add_eq_zero_left h1
    have := mul_prod_map_eq (K := K) (ι Q (e j)) (fun i => ι Q (e i)) σ hσ (List.finRange n)
    rw [← List.ofFn_eq_map, ← List.ofFn_eq_map, List.prod_ofFn] at this
    rw [this]
    congr 3
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, Finset.filter_ne',
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hωv : ∀ v, ι Q v * ω = algebraMap K _ s * ω * ι Q v := by
    have : (LinearMap.mulRight K ω) ∘ₗ ι Q = (LinearMap.mulLeft K (algebraMap K _ s * ω)) ∘ₗ ι Q :=
      e.ext fun j => by simpa [mul_assoc] using hωj j
    exact fun v => congr($this v)
  have hs : s * s = 1 := by
    rw [← pow_two, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hcomm : ∀ x ∈ evenOdd Q 0, x * ω = ω * x := by
    intro x hx
    induction x, hx using even_induction with
    | algebraMap r => exact (Algebra.commutes r ω)
    | add x y _ _ ihx ihy => rw [add_mul, mul_add, ihx, ihy]
    | ι_mul_ι_mul m₁ m₂ x _ ih =>
      have e1 : ι Q m₁ * (ι Q m₂ * ω) = ω * (ι Q m₁ * ι Q m₂) := by
        calc ι Q m₁ * (ι Q m₂ * ω) = ι Q m₁ * (algebraMap K _ s * (ω * ι Q m₂)) := by
              rw [hωv, mul_assoc]
          _ = algebraMap K _ s * ((ι Q m₁ * ω) * ι Q m₂) := by
              rw [Algebra.left_comm, mul_assoc]
          _ = algebraMap K _ s * (algebraMap K _ s * (ω * ι Q m₁) * ι Q m₂) := by
              rw [hωv, mul_assoc (algebraMap K _ s)]
          _ = algebraMap K _ (s * s) * (ω * (ι Q m₁ * ι Q m₂)) := by
              rw [map_mul]; simp only [mul_assoc]
          _ = ω * (ι Q m₁ * ι Q m₂) := by rw [hs, map_one, one_mul]
      rw [mul_assoc _ x, ih, ← mul_assoc, mul_assoc (ι Q m₁), e1]
      simp only [mul_assoc]
  have hg0 : ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    rw [← even_toSubmodule]; exact g.2.1
  have hconj : ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ω *
      (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = ω := by
    rw [hcomm _ hg0, mul_assoc, Units.mul_inv, mul_one]
  have hconj' : ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ω *
      (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      (List.ofFn fun i => ι Q (P (e i))).prod := by
    rw [hω, List.ofFn_eq_map, conj_prod_map, List.ofFn_eq_map]
    congr 2
    funext i
    exact (ι_specP g (e i)).symm
  have hPe : ∀ i j, i ≠ j → bform Q (P (e i)) (P (e j)) = 0 := fun i j hij => by
    rw [hP]; erw [bform_specP]; exact he hij
  have key := hΛ (P ∘ e) hPe
  rw [show (List.ofFn fun i => ι Q ((P ∘ e) i)) = List.ofFn fun i => ι Q (P (e i)) from rfl,
    ← hconj', hconj, hΛ e (fun i j hij => he hij), Basis.det_comp, Basis.det_self, mul_one] at key
  exact key.symm

/-- The central scalars `K^× ⊆ GSpin(V)` (Thesis §5.1, the `F^×` of the exact sequence). -/
def scalarGSpin (Q : QuadraticForm K V) : Kˣ →* GSpin Q where
  toFun c := ⟨Units.map (algebraMap K (CliffordAlgebra Q)).toMonoidHom c, by
    refine ⟨Subalgebra.algebraMap_mem _ _, fun v => ⟨v, ?_⟩, fun v => ⟨v, ?_⟩⟩ <;>
    · simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
        Units.coe_map_inv]
      rw [← Algebra.commutes, ← mul_assoc, ← map_mul]
      simp⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

/-- The central scalars lie in the kernel of `P`. -/
theorem specP_scalarGSpin_eq_one {Q : QuadraticForm K V} (c : Kˣ) :
    specP Q (scalarGSpin Q c) = 1 := by
  ext v
  apply ι_injective Q
  change ι Q (specP Q (scalarGSpin Q c) v) = ι Q v
  rw [ι_specP]
  simp only [scalarGSpin, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, Units.coe_map_inv]
  rw [← Algebra.commutes, ← mul_assoc, ← map_mul]
  simp

/-- Exactness of `1 → K^× → GSpin(V) → SO(V)` at `GSpin(V)` (Thesis §5.1.2). -/
theorem ker_specP [Module.Finite K V] {Q : QuadraticForm K V} (hQ : IsNondeg Q) :
    (specP Q).ker = (scalarGSpin Q).range := by
  apply le_antisymm
  · intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hcomm : ∀ v, ι Q v * ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
        ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q v := by
      intro v
      have h := ι_specP g v
      rw [hg] at h
      change ι Q v = _ at h
      conv_lhs => rw [h]
      rw [mul_assoc, Units.inv_mul, mul_one]
    have h0 : ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
      rw [← even_toSubmodule]; exact g.2.1
    obtain ⟨r, hr⟩ := eq_algebraMap_of_commute_ι hQ h0 hcomm
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact (g : (CliffordAlgebra Q)ˣ).ne_zero (by rw [hr, map_zero])
    refine ⟨Units.mk0 r hr0, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [hr]
    rfl
  · rintro _ ⟨c, rfl⟩
    exact specP_scalarGSpin_eq_one c

omit [Invertible (2 : K)] in
/-- The scalars `K^×` are central in `GSpin(V)` (Thesis §5.1.2). -/
theorem scalarGSpin_mem_center (Q : QuadraticForm K V) (c : Kˣ) :
    scalarGSpin Q c ∈ Subgroup.center (GSpin Q) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext; apply Units.ext
  simp [scalarGSpin, Algebra.commutes]

/-- A `2`-dimensional quadratic space has an orthogonal basis indexed by `Fin 2`. -/
theorem exists_orthogonal_basis_fin_two [Module.Finite K V] (Q : QuadraticForm K V)
    (hV : finrank K V = 2) :
    ∃ e : Basis (Fin 2) K V, ∀ i j, i ≠ j → bform Q (e i) (e j) = 0 := by
  obtain ⟨e', he'⟩ : ∃ e : Basis (Fin (finrank K V)) K V, (bform Q).IsOrthoᵢ e :=
    LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm (S := K) Q)
  refine ⟨e'.reindex (finCongr hV), fun i j hij => ?_⟩
  rw [e'.reindex_apply, e'.reindex_apply]
  exact he' (fun h => hij ((finCongr hV).symm.injective h))

/-- For an orthogonal basis `e₀, e₁` of a plane, the even Clifford algebra is `K ⊕ K ω` with
`ω = e₀e₁` (Thesis §5.1.1: `dim C⁺(V) = 2^{dim V - 1}`). -/
theorem exists_eq_smul_one_add_smul_of_even {Q : QuadraticForm K V} (e : Basis (Fin 2) K V)
    (he : ∀ i j, i ≠ j → bform Q (e i) (e j) = 0) (x : CliffordAlgebra Q)
    (hx : x ∈ evenOdd Q 0) :
    ∃ a b : K, x = a • (1 : CliffordAlgebra Q) + b • (ι Q (e 0) * ι Q (e 1)) := by
  set ω : CliffordAlgebra Q := ι Q (e 0) * ι Q (e 1) with hω
  have h10 : ι Q (e 1) * ι Q (e 0) = -ω := by
    have h1 := ι_mul_ι_add_swap (Q := Q) (e 1) (e 0)
    have hb : bform Q (e 1) (e 0) = 0 := he 1 0 (by decide)
    rw [polar_eq_two_mul_bform, hb, mul_zero, (algebraMap K (CliffordAlgebra Q)).map_zero] at h1
    exact eq_neg_of_add_eq_zero_left h1
  have hsq : ∀ i, ι Q (e i) * ι Q (e i) = Q (e i) • (1 : CliffordAlgebra Q) := fun i => by
    rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one]
  have hωω : ω * ω = (-(Q (e 0) * Q (e 1))) • (1 : CliffordAlgebra Q) := by
    calc ω * ω = ι Q (e 0) * (ι Q (e 1) * ι Q (e 0)) * ι Q (e 1) := by
          simp only [ω, mul_assoc]
      _ = -((ι Q (e 0) * ι Q (e 0)) * (ι Q (e 1) * ι Q (e 1))) := by
          rw [h10]; simp only [ω, mul_neg, neg_mul, mul_assoc]
      _ = _ := by rw [hsq, hsq, smul_mul_smul_comm, one_mul, neg_smul]
  -- `ι u ι v ∈ K + K ω`
  have hvv : ∀ u v : V, ∃ p q : K, ι Q u * ι Q v = p • (1 : CliffordAlgebra Q) + q • ω := by
    intro u v
    have hu := e.sum_repr u
    have hv := e.sum_repr v
    rw [Fin.sum_univ_two] at hu hv
    refine ⟨e.repr u 0 * e.repr v 0 * Q (e 0) + e.repr u 1 * e.repr v 1 * Q (e 1),
      e.repr u 0 * e.repr v 1 - e.repr u 1 * e.repr v 0, ?_⟩
    conv_lhs => rw [← hu, ← hv]
    simp only [map_add, map_smul, add_mul, mul_add, smul_mul_smul_comm, hsq, h10, ← hω]
    module
  induction x, hx using even_induction with
  | algebraMap r => exact ⟨r, 0, by rw [Algebra.algebraMap_eq_smul_one]; module⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨a, b, rfl⟩ := ihx
    obtain ⟨c, d, rfl⟩ := ihy
    exact ⟨a + c, b + d, by module⟩
  | ι_mul_ι_mul m₁ m₂ x _ ih =>
    obtain ⟨a, b, rfl⟩ := ih
    obtain ⟨p, q, hpq⟩ := hvv m₁ m₂
    refine ⟨p * a + q * b * (-(Q (e 0) * Q (e 1))), p * b + q * a, ?_⟩
    rw [hpq]
    simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, hωω]
    module

/-- `GSpin(V)` is commutative when `dim V = 2`: it lies in `C⁺(V) = K ⊕ K e₀e₁`, a commutative
algebra.  (For a hyperbolic plane `GSpin(V)` is a split torus `G_m²`, for an anisotropic plane
`E^×`; Thesis §5.1.2.)  The hyperbolic hypothesis is not needed. -/
theorem isComm_GSpin_of_finrank_eq_two [Module.Finite K V] {Q : QuadraticForm K V}
    (hV : finrank K V = 2) (g h : GSpin Q) : g * h = h * g := by
  obtain ⟨e, he⟩ := exists_orthogonal_basis_fin_two Q hV
  have hg : ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    rw [← even_toSubmodule]; exact g.2.1
  have hh : ((h : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    rw [← even_toSubmodule]; exact h.2.1
  obtain ⟨a, b, hab⟩ := exists_eq_smul_one_add_smul_of_even e he _ hg
  obtain ⟨c, d, hcd⟩ := exists_eq_smul_one_add_smul_of_even e he _ hh
  apply Subtype.ext; apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, hab, hcd, add_mul, mul_add, smul_mul_smul_comm,
    one_mul, mul_one]
  module

/-- `GSpin` of a hyperbolic plane is commutative. -/
theorem isComm_GSpin_of_isHypPlane [Module.Finite K V] {Q : QuadraticForm K V}
    (hQ : IsHypPlane Q) (g h : GSpin Q) : g * h = h * g :=
  isComm_GSpin_of_finrank_eq_two hQ.1 g h

open scoped Classical in
/-- The `K`-points of the maximal split central torus `A_{GSpin(V)}` (Thesis §2.1 "split
component"): all of `GSpin(V)` when `V` is a hyperbolic plane (`GSpin(V) ≅ G_m²`), and the
scalars `K^×` otherwise (including the anisotropic plane, where `GSpin(V) = E^×` has split part
`K^×`, and `dim V ≥ 3`, where the centre is `G_m` up to a finite group). -/
def splitCentralGSpin (Q : QuadraticForm K V) : Subgroup (GSpin Q) :=
  if IsHypPlane Q then ⊤ else (scalarGSpin Q).range

/-- The scalars lie in the split centre (Thesis §2.1: `A_G ⊇ G_m`). -/
theorem scalarGSpin_mem_splitCentralGSpin (Q : QuadraticForm K V) (c : Kˣ) :
    scalarGSpin Q c ∈ splitCentralGSpin Q := by
  classical
  unfold splitCentralGSpin
  split_ifs
  · trivial
  · exact ⟨c, rfl⟩

/-- The split centre is central. -/
theorem splitCentralGSpin_le_center [Module.Finite K V] (Q : QuadraticForm K V) :
    splitCentralGSpin Q ≤ Subgroup.center (GSpin Q) := by
  classical
  unfold splitCentralGSpin
  split_ifs with h
  · intro g _
    rw [Subgroup.mem_center_iff]
    exact fun x => isComm_GSpin_of_isHypPlane h x g
  · rintro _ ⟨c, rfl⟩
    exact scalarGSpin_mem_center Q c

omit [Invertible (2 : K)] in
/-- Separation of a vector from a subspace by a linear functional. -/
theorem exists_dual_of_notMem {p : Submodule K V} {x : V} (hx : x ∉ p) :
    ∃ f : Module.Dual K V, f x ≠ 0 ∧ ∀ y ∈ p, f y = 0 := by
  obtain ⟨f, hf, hp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  refine ⟨f, hf, fun y hy => ?_⟩
  have : f y ∈ p.map f := Submodule.mem_map_of_mem hy
  rw [hp] at this
  exact this

/-- If `ι x ι u ι v ∈ ι(V)` for all `v`, `u ≠ 0` and `dim V ≥ 3`, then `x ∈ K u`. -/
theorem mem_span_of_ι_mul_ι_mul_ι_mem [Module.Finite K V] (hV : 3 ≤ finrank K V)
    {Q : QuadraticForm K V} {x u : V} (hu : u ≠ 0)
    (h : ∀ v, ι Q x * ι Q u * ι Q v ∈ LinearMap.range (ι Q)) : x ∈ K ∙ u := by
  by_contra hx
  -- `x, u` independent; pick `v ∉ span {x, u}`
  have hlt : Submodule.span K {x, u} ≠ ⊤ := by
    intro htop
    have h1 : finrank K (Submodule.span K ({x, u} : Set V)) ≤ 2 := by
      classical
      have := finrank_span_finset_le_card (R := K) ({x, u} : Finset V)
      rw [Finset.coe_insert, Finset.coe_singleton] at this
      exact this.trans Finset.card_le_two
    rw [htop, finrank_top] at h1
    omega
  obtain ⟨v, hv⟩ : ∃ v, v ∉ Submodule.span K {x, u} := by
    by_contra hall; push Not at hall
    exact hlt (eq_top_iff.mpr fun v _ => hall v)
  obtain ⟨d, hdv, hd⟩ := exists_dual_of_notMem hv
  have hdx : d x = 0 := hd x (Submodule.subset_span (by simp))
  have hdu : d u = 0 := hd u (Submodule.subset_span (by simp))
  obtain ⟨y, hy⟩ := h v
  have h1 := congrArg (CliffordAlgebra.contractLeft d) hy
  rw [contractLeft_ι, mul_assoc, contractLeft_ι_mul, contractLeft_ι_mul, contractLeft_ι, hdx, hdu,
    zero_smul, zero_sub, zero_smul, zero_sub, mul_neg, neg_neg, ← Algebra.commutes,
    ← Algebra.smul_def] at h1
  -- so `ι x ι u` is a scalar
  have h1' : d v • (ι Q x * ι Q u) = algebraMap K _ (d y) := by rw [h1, mul_smul_comm]
  have hxu : ι Q x * ι Q u = algebraMap K _ ((d v)⁻¹ * d y) := by
    rw [map_mul, ← h1', ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hdv, one_smul]
  obtain ⟨d', hd'x, hd'⟩ := exists_dual_of_notMem hx
  have hd'u : d' u = 0 := hd' u (Submodule.mem_span_singleton_self u)
  have h2 := congrArg (CliffordAlgebra.contractLeft d') hxu
  rw [contractLeft_ι_mul, contractLeft_ι, hd'u, map_zero, mul_zero, sub_zero,
    contractLeft_algebraMap] at h2
  have : ι Q u = 0 := by
    have := congrArg (fun z => (d' x)⁻¹ • z) h2
    simpa [smul_smul, inv_mul_cancel₀ hd'x] using this
  exact hu (ι_injective Q (by rw [this, map_zero]))


/-- For anisotropic `u, w`, the product `ι(u) ι(w)` as an element of `GSpin(V)` (a lift of the
product of the reflections in `u` and `w`). -/
def gspinPair (Q : QuadraticForm K V) {u w : V} (hu : Q u ≠ 0) (hw : Q w ≠ 0) : GSpin Q :=
  ⟨⟨ι Q u * ι Q w, (Q u * Q w)⁻¹ • (ι Q w * ι Q u),
    by
      rw [mul_smul_comm, show ι Q u * ι Q w * (ι Q w * ι Q u) = ι Q u * (ι Q w * ι Q w) * ι Q u by
        simp only [mul_assoc], ι_sq_scalar, ← Algebra.commutes, mul_assoc, ι_sq_scalar,
        ← (algebraMap K (CliffordAlgebra Q)).map_mul, Algebra.smul_def,
        ← (algebraMap K (CliffordAlgebra Q)).map_mul, mul_comm (Q w) (Q u),
        inv_mul_cancel₀ (mul_ne_zero hu hw), map_one],
    by
      rw [smul_mul_assoc, show ι Q w * ι Q u * (ι Q u * ι Q w) = ι Q w * (ι Q u * ι Q u) * ι Q w by
        simp only [mul_assoc], ι_sq_scalar, ← Algebra.commutes, mul_assoc, ι_sq_scalar,
        ← (algebraMap K (CliffordAlgebra Q)).map_mul, Algebra.smul_def,
        ← (algebraMap K (CliffordAlgebra Q)).map_mul,
        inv_mul_cancel₀ (mul_ne_zero hu hw), map_one]⟩,
    by
      refine ⟨?_, fun v => ?_, fun v => ?_⟩
      · rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
        exact ι_mul_ι_mem_evenOdd_zero Q u w
      · show ι Q u * ι Q w * ι Q v * ((Q u * Q w)⁻¹ • (ι Q w * ι Q u)) ∈ _
        rw [mul_smul_comm, show ι Q u * ι Q w * ι Q v * (ι Q w * ι Q u) =
          ι Q u * (ι Q w * ι Q v * ι Q w) * ι Q u by simp only [mul_assoc], ι_mul_ι_mul_ι,
          ι_mul_ι_mul_ι, ← map_smul]
        exact LinearMap.mem_range_self _ _
      · show (Q u * Q w)⁻¹ • (ι Q w * ι Q u) * ι Q v * (ι Q u * ι Q w) ∈ _
        rw [smul_mul_assoc, smul_mul_assoc, show ι Q w * ι Q u * ι Q v * (ι Q u * ι Q w) =
          ι Q w * (ι Q u * ι Q v * ι Q u) * ι Q w by simp only [mul_assoc], ι_mul_ι_mul_ι,
          ι_mul_ι_mul_ι, ← map_smul]
        exact LinearMap.mem_range_self _ _⟩

omit [Invertible (2 : K)] in
/-- The underlying Clifford element of `gspinPair`. -/
@[simp] theorem coe_gspinPair (Q : QuadraticForm K V) {u w : V} (hu : Q u ≠ 0) (hw : Q w ≠ 0) :
    (((gspinPair Q hu hw : GSpin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      ι Q u * ι Q w := rfl

/-- A central element of `GSpin(V)`, `dim V ≥ 3`, acts on `V` by a scalar. -/
theorem specP_eq_smul_of_mem_center [Module.Finite K V] (hV : 3 ≤ finrank K V)
    {Q : QuadraticForm K V} (hQ : IsNondeg Q) {b : GSpin Q} (hb : ∀ y : GSpin Q, b * y = y * b) :
    ∃ c : K, ∀ v, specP Q b v = c • v := by
  classical
  set n := finrank K V
  obtain ⟨e, he⟩ : ∃ e : Basis (Fin n) K V, (bform Q).IsOrthoᵢ e :=
    LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm (S := K) Q)
  have hQe : ∀ i, Q (e i) ≠ 0 := by
    intro i hi
    apply e.ne_zero i
    rw [isNondeg_iff] at hQ
    apply hQ
    have h0 : (bform Q (e i) : V →ₗ[K] K) = 0 := by
      refine e.ext fun j => ?_
      by_cases hij : i = j
      · subst hij
        rw [LinearMap.zero_apply, bform, QuadraticMap.associated_eq_self_apply, hi]
      · exact he hij
    intro y; rw [h0, LinearMap.zero_apply]
  set T : V →ₗ[K] V := (specP Q b : V →ₗ[K] V)
  set B : CliffordAlgebra Q := ((b : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  set Bi : CliffordAlgebra Q := (((b : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) :
    CliffordAlgebra Q)
  have hBBi : B * Bi = 1 := Units.mul_inv _
  have hTv : ∀ v, ι Q (T v) = B * ι Q v * Bi := fun v => ι_specP b v
  -- `ι(T eᵢ) ι(T eⱼ) = ι eᵢ ι eⱼ`
  have hT : ∀ i j, ι Q (T (e i)) * ι Q (T (e j)) = ι Q (e i) * ι Q (e j) := by
    intro i j
    have hc := congrArg (fun y : GSpin Q => ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
      (hb (gspinPair Q (hQe i) (hQe j)))
    simp only [Subgroup.coe_mul, Units.val_mul, coe_gspinPair] at hc
    change B * (ι Q (e i) * ι Q (e j)) = ι Q (e i) * ι Q (e j) * B at hc
    rw [hTv, hTv, show B * ι Q (e i) * Bi * (B * ι Q (e j) * Bi) =
      B * ι Q (e i) * (Bi * B) * ι Q (e j) * Bi by simp only [mul_assoc], Units.inv_mul, mul_one,
      mul_assoc B, hc, mul_assoc, hBBi, mul_one]
  have hT' : ∀ i v, ι Q (T (e i)) * ι Q (T v) = ι Q (e i) * ι Q v := by
    intro i
    have : (LinearMap.mulLeft K (ι Q (T (e i)))) ∘ₗ ι Q ∘ₗ T =
        (LinearMap.mulLeft K (ι Q (e i))) ∘ₗ ι Q := e.ext fun j => by simpa using hT i j
    exact fun v => congr($this v)
  have hspan : ∀ i, T (e i) ∈ K ∙ e i := by
    intro i
    refine mem_span_of_ι_mul_ι_mul_ι_mem (Q := Q) hV (e.ne_zero i) fun v => ⟨Q (T (e i)) • T v, ?_⟩
    rw [map_smul, Algebra.smul_def, ← ι_sq_scalar, mul_assoc, hT', mul_assoc]
  choose μ hμ using fun i => Submodule.mem_span_singleton.mp (hspan i)
  have hne : ∀ i j, ι Q (e i) * ι Q (e j) ≠ 0 := fun i j =>
    (gspinPair Q (hQe i) (hQe j) : (CliffordAlgebra Q)ˣ).ne_zero
  have hμμ : ∀ i j, μ i * μ j = 1 := by
    intro i j
    have h := hT i j
    rw [← hμ, ← hμ, map_smul, map_smul, smul_mul_smul_comm] at h
    have : (μ i * μ j - 1) • (ι Q (e i) * ι Q (e j)) = 0 := by rw [sub_smul, h, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right (hne i j))
  have hμ0 : ∀ i, μ i ≠ 0 := fun i h => by simpa [h] using hμμ i i
  refine ⟨μ ⟨0, by omega⟩, fun v => ?_⟩
  have hall : ∀ j, μ j = μ ⟨0, by omega⟩ := by
    intro j
    obtain ⟨k, hk1, hk2⟩ : ∃ k : Fin n, k ≠ j ∧ k ≠ ⟨0, by omega⟩ := by
      by_cases hj : (j : ℕ) = 1
      · exact ⟨⟨2, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega,
          fun h => by simp [Fin.ext_iff] at h⟩
      · exact ⟨⟨1, by omega⟩, fun h => hj (by rw [← h]),
          fun h => by simp [Fin.ext_iff] at h⟩
    have h1 := hμμ j k
    have h2 := hμμ ⟨0, by omega⟩ k
    exact mul_right_cancel₀ (hμ0 k) (h1.trans h2.symm)
  have : T = μ ⟨0, by omega⟩ • LinearMap.id := e.ext fun j => by
    rw [← hμ, hall j]; rfl
  exact congr($this v)


omit [Invertible (2 : K)] in
/-- On a space of dimension `≤ 1`, an endomorphism of determinant `1` is the identity. -/
theorem eq_id_of_det_eq_one_of_finrank_le_one [Module.Finite K V] (hV : finrank K V ≤ 1)
    {f : V →ₗ[K] V} (hf : LinearMap.det f = 1) : f = LinearMap.id := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hV with h0 | h1
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0
    ext v; exact Subsingleton.elim _ _
  · have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h1
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one h1 hx (f x)
    have hfc : f = c • LinearMap.id := by
      ext y
      obtain ⟨t, rfl⟩ := exists_smul_eq_of_finrank_eq_one h1 hx y
      rw [map_smul, ← hc, LinearMap.smul_apply, LinearMap.id_apply, smul_comm]
    rw [hfc, LinearMap.det_smul, LinearMap.det_id, mul_one, h1, pow_one] at hf
    rw [hfc, hf, one_smul]

/-- The Lie algebra `gspin(V) = {X ∈ C⁺(V) | [X, v] ∈ V for all v ∈ V}`
(Thesis Prop. 5.1.3.1). -/
def gspin (Q : QuadraticForm K V) : LieSubalgebra K (CliffordAlgebra Q) where
  carrier := {X | X ∈ even Q ∧ ∀ v, ⁅X, ι Q v⁆ ∈ LinearMap.range (ι Q)}
  add_mem' := by
    rintro X Y ⟨hX0, hX⟩ ⟨hY0, hY⟩
    exact ⟨Subalgebra.add_mem _ hX0 hY0, fun v => by
      rw [add_lie]; exact Submodule.add_mem _ (hX v) (hY v)⟩
  zero_mem' := ⟨Subalgebra.zero_mem _, fun v => by simp⟩
  smul_mem' := by
    rintro c X ⟨hX0, hX⟩
    exact ⟨Subalgebra.smul_mem _ hX0 c, fun v => by
      rw [smul_lie]; exact Submodule.smul_mem _ c (hX v)⟩
  lie_mem' := by
    rintro X Y ⟨hX0, hX⟩ ⟨hY0, hY⟩
    refine ⟨?_, fun v => ?_⟩
    · rw [Ring.lie_def]
      exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hX0 hY0) (Subalgebra.mul_mem _ hY0 hX0)
    · obtain ⟨w, hw⟩ := hY v
      obtain ⟨u, hu⟩ := hX v
      have h := leibniz_lie X Y (ι Q v)
      rw [← hw] at h
      rw [show ⁅⁅X, Y⁆, ι Q v⁆ = ⁅X, ι Q w⁆ - ⁅Y, ⁅X, ι Q v⁆⁆ by rw [h]; abel, ← hu]
      exact Submodule.sub_mem _ (hX w) (hY u)

/-- `dim C(V) = 2^{dim V}` (Thesis §5.1.1). -/
theorem finrank_cliffordAlgebra [Module.Finite K V] (Q : QuadraticForm K V) :
    finrank K (CliffordAlgebra Q) = 2 ^ finrank K V := by
  rw [(equivExterior Q).finrank_eq, Module.finrank_eq_card_basis (Module.finBasis K V).ExteriorAlgebra,
    Fintype.card_finset, Fintype.card_fin]

/-- `2^{dim V} ≠ 0` in `K` (characteristic `≠ 2`). -/
theorem cast_finrank_cliffordAlgebra_ne_zero [Module.Finite K V] (Q : QuadraticForm K V) :
    (finrank K (CliffordAlgebra Q) : K) ≠ 0 := by
  rw [finrank_cliffordAlgebra, Nat.cast_pow, Nat.cast_ofNat]
  exact pow_ne_zero _ (Invertible.ne_zero 2)

omit [Invertible (2 : K)] in
/-- `[ι a ι b, ι v] = polar(b, v) ι a - polar(a, v) ι b`. -/
theorem ι_mul_ι_commutator (Q : QuadraticForm K V) (a b v : V) :
    ι Q a * ι Q b * ι Q v - ι Q v * (ι Q a * ι Q b) =
      ι Q (QuadraticMap.polar Q b v • a - QuadraticMap.polar Q a v • b) := by
  have h1 := ι_mul_ι_add_swap (Q := Q) b v
  have h2 := ι_mul_ι_add_swap (Q := Q) v a
  calc ι Q a * ι Q b * ι Q v - ι Q v * (ι Q a * ι Q b)
      = ι Q a * (ι Q b * ι Q v + ι Q v * ι Q b) - (ι Q v * ι Q a + ι Q a * ι Q v) * ι Q b := by
        noncomm_ring
    _ = _ := by
        rw [h1, h2, map_sub, map_smul, map_smul, Algebra.smul_def, Algebra.smul_def,
          ← Algebra.commutes, QuadraticMap.polar_comm Q v a]

omit [Invertible (2 : K)] in
/-- Bivectors lie in `gspin(V)` (Thesis Prop. 5.1.3.1). -/
theorem ι_mul_ι_mem_gspin (Q : QuadraticForm K V) (a b : V) : ι Q a * ι Q b ∈ gspin Q := by
  refine ⟨?_, fun v => ⟨_, (ι_mul_ι_commutator Q a b v).symm.trans ?_⟩⟩
  · rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
    exact ι_mul_ι_mem_evenOdd_zero Q a b
  · rw [Ring.lie_def]

omit [Invertible (2 : K)] in
/-- The scalars lie in `gspin(V)`. -/
theorem one_mem_gspin (Q : QuadraticForm K V) : (1 : CliffordAlgebra Q) ∈ gspin Q :=
  ⟨Subalgebra.one_mem _, fun v => ⟨0, by simp [Ring.lie_def]⟩⟩

/-- For `X ∈ gspin(V)`: `X ι(u) = ι(u) X + ι(A u)` with `A u = ι⁻¹[X, ι u]`. -/
theorem gspin_mul_ι {Q : QuadraticForm K V} {X : CliffordAlgebra Q} (hX : X ∈ gspin Q) (u : V) :
    X * ι Q u = ι Q u * X + ι Q (ιInv Q (X * ι Q u - ι Q u * X)) := by
  obtain ⟨w, hw⟩ := hX.2 u
  rw [Ring.lie_def] at hw
  rw [← hw, ιInv_ι, hw]
  abel

omit [Invertible (2 : K)] in
/-- The trace form `x ↦ tr(L_x)` on `C(V)` is symmetric: `tr(L_{xy}) = tr(L_{yx})`. -/
theorem trace_mulLeft_comm (Q : QuadraticForm K V) [Module.Finite K V] (x y : CliffordAlgebra Q) :
    LinearMap.trace K _ (LinearMap.mulLeft K (x * y)) =
      LinearMap.trace K _ (LinearMap.mulLeft K (y * x)) := by
  rw [LinearMap.mulLeft_mul, LinearMap.mulLeft_mul, ← Module.End.mul_eq_comp,
    ← Module.End.mul_eq_comp, LinearMap.trace_mul_comm]

/-- The trace form is nondegenerate on `gspin(V)`. -/
theorem trace_nondegenerate_gspin [Module.Finite K V] {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    {X : CliffordAlgebra Q} (hX : X ∈ gspin Q)
    (h : ∀ Y ∈ gspin Q, LinearMap.trace K _ (LinearMap.mulLeft K (X * Y)) = 0) : X = 0 := by
  set t : CliffordAlgebra Q → K := fun x => LinearMap.trace K _ (LinearMap.mulLeft K x) with ht
  have tadd : ∀ x y, t (x + y) = t x + t y := fun x y => by
    have e : LinearMap.mulLeft K (x + y) = LinearMap.mulLeft K x + LinearMap.mulLeft K y := by
      ext z; simp [add_mul]
    simp only [t, e, map_add]
  have tsub : ∀ x y, t (x - y) = t x - t y := fun x y => by
    have e : LinearMap.mulLeft K (x - y) = LinearMap.mulLeft K x - LinearMap.mulLeft K y := by
      ext z; simp [sub_mul]
    simp only [t, e, map_sub]
  have talg : ∀ r : K, ∀ x, t (algebraMap K _ r * x) = r * t x := fun r x => by
    have e : LinearMap.mulLeft K (algebraMap K _ r * x) = r • LinearMap.mulLeft K x := by
      ext y; simp [Algebra.smul_def]
    simp only [t, e, map_smul, smul_eq_mul]
  have tcomm : ∀ x y, t (x * y) = t (y * x) := trace_mulLeft_comm Q
  have t1 : t 1 = (finrank K (CliffordAlgebra Q) : K) := by
    simp only [t, LinearMap.mulLeft_one, LinearMap.trace_id]
  have hX1 : t X = 0 := by simpa using h 1 (one_mem_gspin Q)
  -- `t(ι a ι b) = ½ polar(a,b) t(1)`
  have tab : ∀ a b, 2 * t (ι Q a * ι Q b) = QuadraticMap.polar Q a b * t 1 := fun a b => by
    have := congrArg t (ι_mul_ι_add_swap (Q := Q) a b)
    rw [tadd, tcomm (ι Q b), ← mul_one (algebraMap K _ _), talg] at this
    rw [two_mul, this]
  set A : V → V := fun u => ιInv Q (X * ι Q u - ι Q u * X)
  have hXA : ∀ u, X * ι Q u = ι Q u * X + ι Q (A u) := gspin_mul_ι hX
  -- `2 t(X ι u ι w) = polar(w,u) t(X) + t(ι w ι(Au))`
  have key : ∀ u w, 2 * t (X * (ι Q u * ι Q w)) =
      QuadraticMap.polar Q w u * t X + t (ι Q w * ι Q (A u)) := fun u w => by
    have e1 : t (X * (ι Q u * ι Q w)) = t (ι Q w * ι Q u * X) + t (ι Q w * ι Q (A u)) := by
      rw [← mul_assoc, tcomm, ← mul_assoc, mul_assoc (ι Q w), hXA, mul_add, ← mul_assoc, tadd]
    have e2 : ι Q w * ι Q u = algebraMap K _ (QuadraticMap.polar Q w u) - ι Q u * ι Q w :=
      eq_sub_of_add_eq (ι_mul_ι_add_swap w u)
    have e3 : t (ι Q w * ι Q u * X) = QuadraticMap.polar Q w u * t X - t (X * (ι Q u * ι Q w)) := by
      rw [e2, sub_mul, tsub, talg, tcomm]
    rw [two_mul]
    nth_rewrite 1 [e1]
    rw [e3]; ring
  have hA : ∀ u, A u = 0 := by
    intro u
    rw [isNondeg_iff] at hQ
    apply hQ
    intro w
    have h0 : t (X * (ι Q u * ι Q w)) = 0 := h _ (ι_mul_ι_mem_gspin Q u w)
    have := key u w
    rw [h0, hX1, mul_zero, mul_zero, zero_add] at this
    have h2 := tab w (A u)
    rw [← this, mul_zero] at h2
    have hne := cast_finrank_cliffordAlgebra_ne_zero Q
    rw [← t1] at hne
    have hp : QuadraticMap.polar Q w (A u) = 0 := by
      rcases mul_eq_zero.mp h2.symm with h3 | h3
      · exact h3
      · exact absurd h3 hne
    rw [polar_eq_two_mul_bform] at hp
    have := (mul_eq_zero.mp hp).resolve_left (Invertible.ne_zero 2)
    rw [QuadraticMap.associated_isSymm K Q w (A u)] at this
    exact this
  have hcomm : ∀ v, ι Q v * X = X * ι Q v := fun v => by rw [hXA, hA, map_zero, add_zero]
  have h0 : X ∈ evenOdd Q 0 := by rw [← even_toSubmodule]; exact hX.1
  obtain ⟨r, rfl⟩ := eq_algebraMap_of_commute_ι hQ h0 hcomm
  have : r * t 1 = 0 := by rw [← talg, mul_one]; exact hX1
  rw [t1] at this
  rw [(mul_eq_zero.mp this).resolve_right (cast_finrank_cliffordAlgebra_ne_zero Q), map_zero]



/-- Thesis Prop. 5.1.3.1: `gspin(V) = so(V) ⊕ K`, where `so(V)` is the
span of the bivectors `v₁ v₂` (for `V ≠ 0` the scalars are already in that span). -/
theorem gspin_eq_span [Module.Finite K V] {Q : QuadraticForm K V} (hQ : IsNondeg Q) :
    (gspin Q).toSubmodule =
      Submodule.span K (Set.range fun p : V × V => ι Q p.1 * ι Q p.2) ⊔
        Submodule.span K {(1 : CliffordAlgebra Q)} := by
  apply le_antisymm
  · intro X hX
    change X ∈ gspin Q at hX
    let A : V →ₗ[K] V := ιInv Q ∘ₗ (LinearMap.mulLeft K X - LinearMap.mulRight K X) ∘ₗ ι Q
    have hXA : ∀ u, X * ι Q u = ι Q u * X + ι Q (A u) := gspin_mul_ι hX
    -- `A` is skew
    have hskew : ∀ u w, bform Q (A u) w = -bform Q u (A w) := by
      intro u w
      have e := ι_mul_ι_add_swap (Q := Q) u w
      have h1 : X * (ι Q u * ι Q w + ι Q w * ι Q u) = (ι Q u * ι Q w + ι Q w * ι Q u) * X := by
        rw [e, Algebra.commutes]
      have h2 : X * (ι Q u * ι Q w + ι Q w * ι Q u) = (ι Q u * ι Q w + ι Q w * ι Q u) * X +
          ((ι Q u * ι Q (A w) + ι Q (A w) * ι Q u) + (ι Q (A u) * ι Q w + ι Q w * ι Q (A u))) := by
        simp only [mul_add, ← mul_assoc, hXA, add_mul]
        simp only [mul_assoc, hXA, mul_add]
        abel
      rw [h1, e, ι_mul_ι_add_swap u (A w), ι_mul_ι_add_swap (A u) w, ← map_add,
        left_eq_add] at h2
      have h3 := (algebraMap K (CliffordAlgebra Q)).injective (h2.trans (map_zero _).symm)
      rw [polar_eq_two_mul_bform, polar_eq_two_mul_bform, ← mul_add] at h3
      have h4 := (mul_eq_zero.mp h3).resolve_left (Invertible.ne_zero 2)
      rw [QuadraticMap.associated_isSymm K Q u (A w)] at h4
      change bform Q (A w) u + bform Q (A u) w = 0 at h4
      rw [QuadraticMap.associated_isSymm K Q u (A w)]
      exact eq_neg_of_add_eq_zero_right h4
    let b := Module.finBasis K V
    have hQ' : (bform Q).Nondegenerate := hQ
    let f := (bform Q).dualBasis hQ' b
    have hrepr : ∀ v i, b.repr v i = bform Q (f i) v := by
      intro v i
      conv_rhs => rw [← b.sum_repr v]
      simp only [map_sum, map_smul, smul_eq_mul, f]
      rw [Finset.sum_eq_single i]
      · rw [LinearMap.BilinForm.apply_dualBasis_left]; simp
      · intro j _ hj; rw [LinearMap.BilinForm.apply_dualBasis_left]; simp [hj]
      · simp
    have h4 : (4 : K) ≠ 0 := by
      have h2 := Invertible.ne_zero (2 : K)
      rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
    let Y : CliffordAlgebra Q := (4 : K)⁻¹ • ∑ i, ι Q (A (b i)) * ι Q (f i)
    have hY : ∀ v, Y * ι Q v - ι Q v * Y = ι Q (A v) := by
      intro v
      have hs1 : ∑ i, QuadraticMap.polar Q (f i) v • A (b i) = (2 : K) • A v := by
        conv_rhs => rw [← b.sum_repr v]
        rw [map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [polar_eq_two_mul_bform, hrepr, map_smul, smul_smul]
      have hs2 : ∑ i, QuadraticMap.polar Q (A (b i)) v • f i = -((2 : K) • A v) := by
        conv_rhs => rw [← f.sum_repr (A v)]
        rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [polar_eq_two_mul_bform, hskew]
        simp only [f, LinearMap.BilinForm.dualBasis_repr_apply]
        rw [QuadraticMap.associated_isSymm K Q (b i) (A v), smul_smul, ← neg_smul]
        congr 1; ring
      simp only [Y, smul_mul_assoc, mul_smul_comm, ← smul_sub, Finset.sum_mul, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      simp_rw [ι_mul_ι_commutator]
      rw [← map_sum, Finset.sum_sub_distrib, hs1, hs2, ← map_smul]
      congr 1
      rw [sub_neg_eq_add, ← two_smul K ((2 : K) • A v), smul_smul, smul_smul]
      rw [show (4 : K)⁻¹ * 2 * 2 = 1 by
        rw [mul_assoc, show (2 : K) * 2 = 4 by norm_num, inv_mul_cancel₀ h4], one_smul]
    have hYmem : Y ∈ Submodule.span K (Set.range fun p : V × V => ι Q p.1 * ι Q p.2) :=
      Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
        Submodule.subset_span ⟨(A (b i), f i), rfl⟩)
    have hYeven : Y ∈ evenOdd Q 0 := by
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
      exact ι_mul_ι_mem_evenOdd_zero Q _ _
    have hX0 : X ∈ evenOdd Q 0 := by rw [← even_toSubmodule]; exact hX.1
    obtain ⟨r, hr⟩ := eq_algebraMap_of_commute_ι hQ (Submodule.sub_mem _ hX0 hYeven)
      (fun v => by
        have := hY v
        rw [mul_sub, sub_mul, hXA]
        rw [← sub_eq_zero] at this ⊢
        rw [← this]; abel)
    rw [Submodule.mem_sup]
    refine ⟨Y, hYmem, algebraMap K _ r, ?_, by rw [← hr]; abel⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact ι_mul_ι_mem_gspin Q p.1 p.2
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact one_mem_gspin Q

omit [Invertible (2 : K)] in
/-- An isometry preserves the polar form. -/
theorem polar_isometry {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁]
    [AddCommGroup V₂] [Module K V₂] {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (f : Q₁ →qᵢ Q₂) (x y : V₁) :
    QuadraticMap.polar Q₂ (f x) (f y) = QuadraticMap.polar Q₁ x y := by
  simp only [QuadraticMap.polar, ← map_add, QuadraticMap.Isometry.map_app]

/-- An isometry preserves the symmetric bilinear form. -/
theorem bform_isometry {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁]
    [AddCommGroup V₂] [Module K V₂] {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (f : Q₁ →qᵢ Q₂) (x y : V₁) : bform Q₂ (f x) (f y) = bform Q₁ x y := by
  have h := polar_isometry f x y
  rw [polar_eq_two_mul_bform, polar_eq_two_mul_bform] at h
  exact mul_left_cancel₀ (Invertible.ne_zero (2 : K)) h

omit [Invertible (2 : K)] in
/-- `C(f)` maps even elements to even elements. -/
theorem map_mem_evenOdd_zero {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁]
    [AddCommGroup V₂] [Module K V₂] {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (f : Q₁ →qᵢ Q₂) {x : CliffordAlgebra Q₁} (hx : x ∈ evenOdd Q₁ 0) :
    CliffordAlgebra.map f x ∈ evenOdd Q₂ 0 := by
  induction x, hx using even_induction with
  | algebraMap r => rw [AlgHom.commutes]; exact SetLike.algebraMap_mem_graded _ _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x _ ih =>
    rw [map_mul, map_mul, map_apply_ι, map_apply_ι]
    exact zero_add (0 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero Q₂ _ _) ih

omit [Invertible (2 : K)] in
/-- The image under `C(f)` of an even element commutes with `ι(u)` whenever `u ⊥ f(V₁)`
(used for `GSpin.map`, and for `GSpin(W)` fixing `Z` pointwise). -/
theorem map_even_commute_ι {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁]
    [AddCommGroup V₂] [Module K V₂] {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (f : Q₁ →qᵢ Q₂) {x : CliffordAlgebra Q₁} (hx : x ∈ evenOdd Q₁ 0) {u : V₂}
    (hu : ∀ w, QuadraticMap.polar Q₂ (f w) u = 0) :
    CliffordAlgebra.map f x * ι Q₂ u = ι Q₂ u * CliffordAlgebra.map f x := by
  have ac : ∀ w, ι Q₂ (f w) * ι Q₂ u = -(ι Q₂ u * ι Q₂ (f w)) := fun w => by
    rw [ι_mul_ι_comm, hu, map_zero, zero_sub]
  induction x, hx using even_induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes _ _
  | add x y _ _ ihx ihy => rw [map_add, add_mul, mul_add, ihx, ihy]
  | ι_mul_ι_mul m₁ m₂ x _ ih =>
    rw [map_mul, map_mul, map_apply_ι, map_apply_ι, mul_assoc, ih, ← mul_assoc,
      mul_assoc (ι Q₂ (f m₁)), ac m₂, mul_neg, ← mul_assoc, ac m₁]
    simp only [neg_mul, neg_neg, mul_assoc]

/-- `V₂ = f(V₁) ⊕ f(V₁)^⊥` for an isometric embedding of a nondegenerate finite-dimensional
`V₁`. -/
theorem exists_orthogonal_decomp {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁]
    [Module.Finite K V₁] [AddCommGroup V₂] [Module K V₂] {Q₁ : QuadraticForm K V₁}
    {Q₂ : QuadraticForm K V₂} (f : Q₁ →qᵢ Q₂) (hf : IsNondeg Q₁) (v : V₂) :
    ∃ w u, v = f w + u ∧ ∀ w', QuadraticMap.polar Q₂ (f w') u = 0 := by
  let φ : Module.Dual K V₁ := ((bform Q₂).flip v).comp f.toLinearMap
  set w := ((bform Q₁).toDual hf).symm φ
  have hw : ∀ w', bform Q₁ w w' = bform Q₂ (f w') v := fun w' => by
    have := congr($(((bform Q₁).toDual hf).apply_symm_apply φ) w')
    change bform Q₁ w w' = _ at this
    simpa [φ] using this
  refine ⟨w, v - f w, by abel, fun w' => ?_⟩
  rw [polar_eq_two_mul_bform, map_sub, bform_isometry,
    show bform Q₁ w' w = bform Q₁ w w' from QuadraticMap.associated_isSymm K Q₁ w' w, hw,
    show bform Q₂ (f w') v = bform Q₂ v (f w') from QuadraticMap.associated_isSymm K Q₂ _ _,
    sub_self, mul_zero]

/-- The map `C(W) → C(V)` induced by an isometric embedding of a
nondegenerate `W` restricts to `GSpin(W) → GSpin(V)` (Thesis Prop. 5.1.2.1
[Emory–Takeda, Prop. 2.10]).
Membership uses `V = W ⊕ W^⊥` and that even elements of `C(W)` commute with `W^⊥`. -/
def GSpin.map {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [Module.Finite K V₁]
    [AddCommGroup V₂] [Module K V₂] {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (f : Q₁ →qᵢ Q₂) (hf : IsNondeg Q₁) : GSpin Q₁ →* GSpin Q₂ :=
  ((Units.map (CliffordAlgebra.map f).toMonoidHom).comp (GSpin Q₁).subtype).codRestrict (GSpin Q₂)
    (fun g => by
      obtain ⟨hg0, hg1, hg2⟩ := g.2
      obtain ⟨hi0, -, -⟩ := (g⁻¹ : GSpin Q₁).2
      rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hg0 hi0
      set x : CliffordAlgebra Q₁ := ((g : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁)
      set y : CliffordAlgebra Q₁ :=
        (((g : (CliffordAlgebra Q₁)ˣ)⁻¹ : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁)
      have hxy : x * y = 1 := Units.mul_inv _
      have hyx : y * x = 1 := Units.inv_mul _
      -- conjugating `ι(v)` by `C(f)(a)`, `a ∈ {x, y}` even with `a ι(V₁) b ⊆ ι(V₁)`, `ab = 1`
      have key : ∀ a b : CliffordAlgebra Q₁, a ∈ evenOdd Q₁ 0 → a * b = 1 →
          (∀ v, a * ι Q₁ v * b ∈ LinearMap.range (ι Q₁)) → ∀ v : V₂,
          CliffordAlgebra.map f a * ι Q₂ v * CliffordAlgebra.map f b ∈
            LinearMap.range (ι Q₂) := by
        intro a b ha hab hrange v
        obtain ⟨w, u, rfl, hu⟩ := exists_orthogonal_decomp f hf v
        obtain ⟨w', hw'⟩ := hrange w
        refine ⟨f w' + u, ?_⟩
        rw [map_add, map_add, mul_add, add_mul]
        congr 1
        · rw [← map_apply_ι f w', hw', map_mul, map_mul, map_apply_ι]
        · rw [map_even_commute_ι f ha hu, mul_assoc, ← map_mul, hab, map_one, mul_one]
      refine ⟨?_, key x y hg0 hxy hg1, key y x hi0 hyx hg2⟩
      rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
      exact map_mem_evenOdd_zero f hg0)

@[simp] theorem GSpin.coe_map {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [Module.Finite K V₁]
    [AddCommGroup V₂] [Module K V₂] {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (f : Q₁ →qᵢ Q₂) (hf : IsNondeg Q₁) (g : GSpin Q₁) :
    (((GSpin.map f hf g : GSpin Q₂) : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra Q₂) =
      CliffordAlgebra.map f ((g : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) :=
  rfl

/-- `W'_x = ker(P(x) − 1)`. -/
def fixedSub {Q : QuadraticForm K V} (x : GSpin Q) : Submodule K V :=
  LinearMap.ker ((specP Q x : V →ₗ[K] V) - LinearMap.id)

/-- `W''_x = Im(P(x) − 1)`. -/
def movedSub {Q : QuadraticForm K V} (x : GSpin Q) : Submodule K V :=
  LinearMap.range ((specP Q x : V →ₗ[K] V) - LinearMap.id)

/-- `W = W'_x ⊕^⊥ W''_x` for semisimple `x` (we state the orthogonality, which holds
for every `x` since `P(x)` is an isometry). -/
theorem fixedSub_orthogonal_movedSub {Q : QuadraticForm K V} (x : GSpin Q) :
    ∀ u ∈ fixedSub x, ∀ w ∈ movedSub x, bform Q u w = 0 := by
  rintro u hu _ ⟨y, rfl⟩
  have hu' : specP Q x u = u := by
    have := LinearMap.mem_ker.mp hu
    simp only [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    exact this
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  conv_lhs => rw [← hu']
  rw [show ((specP Q x : V →ₗ[K] V) y) = specP Q x y from rfl, bform_specP, hu', sub_self]

end GSpinGroup

/-! ## Isotropic flags, parabolic subgroups and their unipotent radicals -/

section Flags

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- A flag of totally isotropic subspaces `0 = Z₀ ⊊ Z₁ ⊊ ⋯ ⊊ Z_len` (Thesis §5.1.2: every
parabolic subgroup of `GSpin(V)` is the stabilizer of such a flag). -/
structure IsotropicFlag (Q : QuadraticForm K V) where
  len : ℕ
  sub : Fin (len + 1) → Submodule K V
  sub_zero : sub 0 = ⊥
  strictMono : StrictMono sub
  isotropic : ∀ i, IsTotallyIsotropic Q (sub i)

namespace IsotropicFlag

variable {Q : QuadraticForm K V}

/-- The largest member `Z_len` of the flag. -/
def top (F : IsotropicFlag Q) : Submodule K V := F.sub (Fin.last F.len)

/-- The flag is a full flag in a maximal totally isotropic subspace: its stabilizer is then a
Borel subgroup (when `GSpin(V)` is quasi-split) (Thesis §4.4). -/
def IsFull (F : IsotropicFlag Q) : Prop :=
  F.len = wittIndex Q ∧ ∀ i, finrank K (F.sub i) = (i : ℕ)

end IsotropicFlag

/-- The parabolic subgroup `P_F ⊆ GSpin(V)`: the stabilizer of every member of the flag
(Thesis §5.1.2, §5.2). -/
def flagStab {Q : QuadraticForm K V} (F : IsotropicFlag Q) : Subgroup (GSpin Q) where
  carrier := {g | ∀ i, (F.sub i).map (specP Q g : V →ₗ[K] V) = F.sub i}
  one_mem' := by
    intro i
    simp only [map_one]
    exact Submodule.map_id _
  mul_mem' := by
    intro g h hg hh i
    rw [map_mul, show ((specP Q g * specP Q h : V ≃ₗ[K] V) : V →ₗ[K] V) =
      (specP Q g : V →ₗ[K] V) ∘ₗ (specP Q h : V →ₗ[K] V) from rfl, Submodule.map_comp, hh i, hg i]
  inv_mem' := by
    intro g hg i
    have h := hg i
    rw [map_inv]
    show Submodule.map ((specP Q g).symm : V →ₗ[K] V) (F.sub i) = F.sub i
    rw [Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm]
    conv_lhs => rw [← h]
    exact Submodule.comap_map_eq_of_injective (specP Q g).injective _

omit [Invertible (2 : K)] in
/-- In a finite-dimensional algebra, `x` is nilpotent iff `x ^ dim = 0` (Cayley–Hamilton for
left multiplication). -/
theorem isNilpotent_iff_pow_finrank {A : Type*} [Ring A] [Algebra K A] [FiniteDimensional K A]
    (x : A) : IsNilpotent x ↔ x ^ finrank K A = 0 := by
  refine ⟨fun h => ?_, fun h => ⟨_, h⟩⟩
  have hL : IsNilpotent (LinearMap.mulLeft K x) := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [LinearMap.pow_mulLeft, hk]; ext; simp⟩
  have h0 : LinearMap.mulLeft K x ^ finrank K A = 0 := by
    rw [← Polynomial.aeval_X_pow (R := K), ← IsNilpotent.charpoly_eq_X_pow_finrank hL,
      LinearMap.aeval_self_charpoly]
  have := congr($h0 (1 : A))
  rwa [LinearMap.pow_mulLeft, LinearMap.mulLeft_apply, mul_one, LinearMap.zero_apply] at this

/-- In finite dimension, `P(g)` stabilizes a subspace as soon as it maps it into itself. -/
theorem mem_flagStab_iff [FiniteDimensional K V] {Q : QuadraticForm K V} {F : IsotropicFlag Q}
    {g : GSpin Q} : g ∈ flagStab F ↔ ∀ i, ∀ v ∈ F.sub i, specP Q g v ∈ F.sub i := by
  refine ⟨fun hg i v hv => hg i ▸ Submodule.mem_map_of_mem hv, fun h i => ?_⟩
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩; exact h i v hv
  · exact LinearEquiv.finrank_map_eq (specP Q g) (F.sub i)

theorem flagStab_mapsTo {Q : QuadraticForm K V} {F : IsotropicFlag Q} {g : GSpin Q}
    (hg : g ∈ flagStab F) (i : Fin (F.len + 1)) {v : V} (hv : v ∈ F.sub i) :
    specP Q g v ∈ F.sub i :=
  hg i ▸ Submodule.mem_map_of_mem hv

/-- Elements of `P_F` preserve `Z_lenᗮ`. -/
theorem flagStab_mapsTo_orthogonal {Q : QuadraticForm K V} {F : IsotropicFlag Q} {g : GSpin Q}
    (hg : g ∈ flagStab F) {v : V} (hv : v ∈ (bform Q).orthogonal F.top) :
    specP Q g v ∈ (bform Q).orthogonal F.top := by
  intro t ht
  have ht' : specP Q g⁻¹ t ∈ F.top := flagStab_mapsTo ((flagStab F).inv_mem hg) _ ht
  rw [← specP_inv_apply_apply g t, bform_specP]
  exact hv _ ht'

/-- The linear conditions defining `N_F`: `P(g)` lies in the unipotent radical of the stabilizer of
the flag in `SO(V)`, i.e. it stabilizes the flag, acts trivially on the graded pieces
`Z_i / Z_{i-1}` and on `Z_lenᗮ / Z_len` (Thesis §5.2).  This is the preimage of `N_F^{SO}` in
`GSpin(V)`, which is `K^× · N_F`. -/
def flagUnipSO {Q : QuadraticForm K V} (F : IsotropicFlag Q) : Subgroup (GSpin Q) where
  carrier := {g | g ∈ flagStab F ∧
    (∀ i : Fin F.len, ∀ v ∈ F.sub i.succ, specP Q g v - v ∈ F.sub i.castSucc) ∧
    (∀ v ∈ (bform Q).orthogonal F.top, specP Q g v - v ∈ F.top)}
  one_mem' := ⟨(flagStab F).one_mem, fun i v _ => by simp, fun v _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg0, hg1, hg2⟩ ⟨hh0, hh1, hh2⟩
    -- `P(gh)v - v = P(g)(P(h)v - v) + (P(g)v - v)`
    have key : ∀ v, specP Q (g * h) v - v =
        specP Q g (specP Q h v - v) + (specP Q g v - v) := fun v => by
      rw [specP_mul_apply, map_sub]; abel
    refine ⟨(flagStab F).mul_mem hg0 hh0, fun i v hv => ?_, fun v hv => ?_⟩
    · rw [key]
      exact add_mem (flagStab_mapsTo hg0 _ (hh1 i v hv)) (hg1 i v hv)
    · rw [key]
      exact add_mem (flagStab_mapsTo hg0 _ (hh2 v hv)) (hg2 v hv)
  inv_mem' := by
    rintro g ⟨hg0, hg1, hg2⟩
    have hi0 := (flagStab F).inv_mem hg0
    -- with `w = P(g⁻¹)v`: `P(g⁻¹)v - v = -(P(g)w - w)`
    have key : ∀ v, specP Q g⁻¹ v - v = -(specP Q g (specP Q g⁻¹ v) - specP Q g⁻¹ v) :=
      fun v => by rw [specP_inv_apply_apply]; abel
    refine ⟨hi0, fun i v hv => ?_, fun v hv => ?_⟩
    · rw [key]
      exact neg_mem (hg1 i _ (flagStab_mapsTo hi0 _ hv))
    · rw [key]
      exact neg_mem (hg2 _ (flagStab_mapsTo_orthogonal hi0 hv))

end Flags

/-! ## The lift of the unipotent radical

`K^×·N_F ∩ {g | g − 1 nilpotent}` is a group (Thesis §5.2: `N` is the unipotent radical of `P`).
Route: the flag gives a self-dual weight filtration `V_{≥w}` of `V` (`flagWt`), hence a
multiplicative filtration of `C(V)` by spans of monomials (`wtFil`).  Positive-weight elements are
nilpotent (computed in the exterior algebra through `equivExterior`).  For `g ∈ K^×·N_F`,
`[ι(v), g] = −ι(P(g)v − v) g` raises weight, so a graded form of the centre lemma
(`exterior_sub_algebraMap_mem_wtFil`, with a basis adapted to the filtration, no Witt basis) shows
`g = c + (positive weight)` with `c ∈ K`; `g − 1` nilpotent forces `c = 1`.  A degenerate `V` is
reduced to a complement of its radical. -/

section WeightFiltration

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- Monomials `ι(v₁)⋯ι(vₘ)` with `vₖ ∈ Vf(wₖ)` and `∑ wₖ ≥ j`. -/
def wtMonomials (Q : QuadraticForm K V) (Vf : ℤ → Submodule K V) (j : ℤ) :
    Set (CliffordAlgebra Q) :=
  {x | ∃ l : List (ℤ × V), (∀ p ∈ l, p.2 ∈ Vf p.1) ∧ j ≤ (l.map Prod.fst).sum ∧
    x = (l.map fun p => ι Q p.2).prod}

/-- The weight filtration of `C(V)` induced by a filtration `Vf` of `V`. -/
def wtFil (Q : QuadraticForm K V) (Vf : ℤ → Submodule K V) (j : ℤ) :
    Submodule K (CliffordAlgebra Q) :=
  Submodule.span K (wtMonomials Q Vf j)

variable {Q : QuadraticForm K V} {Vf : ℤ → Submodule K V}

theorem prod_mem_wtFil {l : List (ℤ × V)} (hl : ∀ p ∈ l, p.2 ∈ Vf p.1) {j : ℤ}
    (hj : j ≤ (l.map Prod.fst).sum) : (l.map fun p => ι Q p.2).prod ∈ wtFil Q Vf j :=
  Submodule.subset_span ⟨l, hl, hj, rfl⟩

theorem wtFil_anti {j j' : ℤ} (h : j ≤ j') : wtFil Q Vf j' ≤ wtFil Q Vf j :=
  Submodule.span_mono fun _ ⟨l, hl, hj, hx⟩ => ⟨l, hl, h.trans hj, hx⟩

theorem algebraMap_mem_wtFil (r : K) {j : ℤ} (hj : j ≤ 0) :
    algebraMap K (CliffordAlgebra Q) r ∈ wtFil Q Vf j := by
  rw [Algebra.algebraMap_eq_smul_one]
  refine Submodule.smul_mem _ r ?_
  simpa using prod_mem_wtFil (Q := Q) (Vf := Vf) (l := []) (by simp) (by simpa using hj)

theorem ι_mul_mem_wtFil {w j : ℤ} {v : V} (hv : v ∈ Vf w) {x : CliffordAlgebra Q}
    (hx : x ∈ wtFil Q Vf j) : ι Q v * x ∈ wtFil Q Vf (w + j) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, hj, rfl⟩ := hx
    have := prod_mem_wtFil (Q := Q) (Vf := Vf) (l := (w, v) :: l)
      (by rintro p (_ | ⟨_, hp⟩); exacts [hv, hl p hp]) (j := w + j) (by simpa using hj)
    simpa using this
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

theorem mul_mem_wtFil {a b : ℤ} {x y : CliffordAlgebra Q} (hx : x ∈ wtFil Q Vf a)
    (hy : y ∈ wtFil Q Vf b) : x * y ∈ wtFil Q Vf (a + b) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, hj, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l', hl', hj', rfl⟩ := hy
      have := prod_mem_wtFil (Q := Q) (Vf := Vf) (l := l ++ l')
        (by intro p hp; rcases List.mem_append.mp hp with hp | hp; exacts [hl p hp, hl' p hp])
        (j := a + b) (by simp only [List.map_append, List.sum_append]; omega)
      simpa [List.map_append, List.prod_append] using this
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy
  | zero => simp
  | add x x' _ _ hx hx' => rw [add_mul]; exact add_mem hx hx'
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

/-- Contraction by a functional killing `Vf a` for `a + w ≥ 1` raises the weight by `w`. -/
theorem contractLeft_mem_wtFil {d : Module.Dual K V} {w : ℤ}
    (hd : ∀ a, 1 ≤ a + w → ∀ v ∈ Vf a, d v = 0) {j : ℤ} {x : CliffordAlgebra Q}
    (hx : x ∈ wtFil Q Vf j) : contractLeft d x ∈ wtFil Q Vf (j + w) := by
  have key : ∀ l : List (ℤ × V), (∀ p ∈ l, p.2 ∈ Vf p.1) →
      contractLeft d (l.map fun p => ι Q p.2).prod ∈ wtFil Q Vf ((l.map Prod.fst).sum + w) := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons p l ih =>
      intro hl
      have hl' : ∀ q ∈ l, q.2 ∈ Vf q.1 := fun q hq => hl q (List.mem_cons_of_mem _ hq)
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [contractLeft_ι_mul]
      refine sub_mem ?_ ?_
      · by_cases hp : 1 ≤ p.1 + w
        · rw [hd p.1 hp p.2 (hl p List.mem_cons_self), zero_smul]; exact zero_mem _
        · refine Submodule.smul_mem _ _ (wtFil_anti ?_ (prod_mem_wtFil hl' le_rfl))
          omega
      · have := ι_mul_mem_wtFil (hl p List.mem_cons_self) (ih hl')
        exact wtFil_anti (by omega) this
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, hj, rfl⟩ := hx
    exact wtFil_anti (by omega) (key l hl)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- `changeForm` preserves the weight filtration when the change of form `B` pairs `Vf a` with
`Vf b` trivially for `a + b ≥ 1`. -/
theorem changeForm_mem_wtFil {Q' : QuadraticForm K V} {B : LinearMap.BilinForm K V}
    (h : B.toQuadraticMap = Q' - Q)
    (hB : ∀ a b, 1 ≤ a + b → ∀ u ∈ Vf a, ∀ v ∈ Vf b, B u v = 0) {j : ℤ}
    {x : CliffordAlgebra Q} (hx : x ∈ wtFil Q Vf j) : changeForm h x ∈ wtFil Q' Vf j := by
  have key : ∀ l : List (ℤ × V), (∀ p ∈ l, p.2 ∈ Vf p.1) →
      changeForm h (l.map fun p => ι Q p.2).prod ∈ wtFil Q' Vf (l.map Prod.fst).sum := by
    intro l
    induction l with
    | nil => intro _; simpa using algebraMap_mem_wtFil (Q := Q') (Vf := Vf) (1 : K) le_rfl
    | cons p l ih =>
      intro hl
      have hl' : ∀ q ∈ l, q.2 ∈ Vf q.1 := fun q hq => hl q (List.mem_cons_of_mem _ hq)
      have hp := hl p List.mem_cons_self
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [changeForm_ι_mul]
      refine sub_mem (ι_mul_mem_wtFil hp (ih hl')) ?_
      have := contractLeft_mem_wtFil (Q := Q') (d := B p.2) (w := p.1)
        (fun a ha v hv => hB p.1 a (by omega) _ hp v hv) (ih hl')
      rwa [add_comm] at this
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, hj, rfl⟩ := hx
    exact wtFil_anti hj (key l hl)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- Every element has some weight, once some `Vf(w)` is everything. -/
theorem exists_mem_wtFil {R : ℤ} (hR : ∀ v, v ∈ Vf R) (x : CliffordAlgebra Q) :
    ∃ j, x ∈ wtFil Q Vf j := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => exact ⟨0, algebraMap_mem_wtFil r le_rfl⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, add_mem (wtFil_anti (min_le_left _ _) ha)
      (wtFil_anti (min_le_right _ _) hb)⟩
  | ι_mul x m hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨R + a, ι_mul_mem_wtFil (hR m) ha⟩

/-- In the exterior algebra, high weights vanish: if `Vf(a) = 0` for `a > R` (`R ≥ 0`), a
monomial of weight `> R · dim V` has a zero factor or more than `dim V` factors. -/
theorem wtFil_exterior_eq_bot [Module.Finite K V] {R : ℕ} (hR : ∀ a : ℤ, (R : ℤ) < a → Vf a = ⊥)
    {j : ℤ} (hj : (R : ℤ) * finrank K V < j) :
    wtFil (0 : QuadraticForm K V) Vf j = ⊥ := by
  rw [eq_bot_iff, wtFil, Submodule.span_le]
  rintro _ ⟨l, hl, hjl, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_bot]
  by_cases h0 : ∃ p ∈ l, R < p.1
  · obtain ⟨p, hp, hpR⟩ := h0
    have : p.2 = 0 := by simpa [hR p.1 hpR] using hl p hp
    exact List.prod_eq_zero (List.mem_map.mpr ⟨p, hp, by simp [this]⟩)
  push Not at h0
  have hsum : (l.map Prod.fst).sum ≤ R * l.length := by
    have : ∀ l : List (ℤ × V), (∀ p ∈ l, p.1 ≤ R) → (l.map Prod.fst).sum ≤ R * l.length := by
      intro l hl
      induction l with
      | nil => simp
      | cons p l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
        have := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
        have := hl p List.mem_cons_self
        nlinarith
    exact this l h0
  have hlen : finrank K V < l.length := by
    by_contra hc
    push Not at hc
    have : (R : ℤ) * l.length ≤ R * finrank K V :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (by positivity)
    omega
  have hv : ¬LinearIndependent K (fun i : Fin l.length => (l.get i).2) := fun hli => by
    have := hli.fintype_card_le_finrank
    simp at this
    omega
  have := (ExteriorAlgebra.ιMulti K l.length).map_linearDependent _ hv
  rw [ExteriorAlgebra.ιMulti_apply] at this
  convert this using 2
  have e : (List.ofFn fun i => ExteriorAlgebra.ι K (l.get i).2) =
      (List.ofFn fun i => l.get i).map (fun p : ℤ × V => ExteriorAlgebra.ι K p.2) := by
    rw [List.map_ofFn]; rfl
  rw [e, List.ofFn_get]

/-- Graded form of `exterior_mem_range_of_contractLeft`: with a basis `bᵢ ∈ Vf(wtᵢ)` adapted to
the filtration (the coordinate `bᵢ*` kills `Vf(a)` for `a > wtᵢ`), an element `X` with
`bᵢ* ⌋ X` of weight `≥ m − wtᵢ + 1` for all `i` is a scalar modulo weight `≥ m + 1`. -/
theorem exterior_sub_algebraMap_mem_wtFil {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (b : Basis ι' K V) (wt : ι' → ℤ) (hb : ∀ i, b i ∈ Vf (wt i))
    (hcoord : ∀ i a, wt i < a → ∀ v ∈ Vf a, b.coord i v = 0) {m : ℤ}
    (X : ExteriorAlgebra K V)
    (hX : ∀ i, contractLeft (b.coord i) X ∈ wtFil (0 : QuadraticForm K V) Vf (m - wt i + 1)) :
    ∃ r : K, X - algebraMap K _ r ∈ wtFil (0 : QuadraticForm K V) Vf (m + 1) := by
  let h : ι' → Module.End K (ExteriorAlgebra K V) := fun i =>
    LinearMap.mulLeft K (ExteriorAlgebra.ι K (b i)) ∘ₗ CliffordAlgebra.contractLeft (b.coord i)
  let T : List ι' → Module.End K (ExteriorAlgebra K V) := fun L => (L.map fun i => (1 - h i)).prod
  have hpres : ∀ i j (Y : ExteriorAlgebra K V), Y ∈ wtFil (0 : QuadraticForm K V) Vf j →
      h i Y ∈ wtFil (0 : QuadraticForm K V) Vf j := by
    intro i j Y hY
    have h1 := contractLeft_mem_wtFil (d := b.coord i) (w := -wt i)
      (fun a ha v hv => hcoord i a (by omega) v hv) hY
    have h2 := ι_mul_mem_wtFil (hb i) h1
    exact wtFil_anti (le_of_eq (by ring)) h2
  have hXi : ∀ i, h i X ∈ wtFil (0 : QuadraticForm K V) Vf (m + 1) := fun i =>
    wtFil_anti (le_of_eq (by ring)) (ι_mul_mem_wtFil (hb i) (hX i))
  have hTX : ∀ L : List ι', T L X - X ∈ wtFil (0 : QuadraticForm K V) Vf (m + 1) := by
    intro L
    induction L with
    | nil => simp [T]
    | cons a L ih =>
      simp only [T, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
      set Y := (List.map (fun i => 1 - h i) L).prod X
      have : (1 - h a) Y - X = (Y - X) - (h a X + h a (Y - X)) := by
        rw [← map_add, add_sub_cancel]
        simp only [LinearMap.sub_apply, Module.End.one_apply]; abel
      rw [this]
      exact sub_mem ih (add_mem (hXi a) (hpres a _ _ ih))
  have anti : ∀ i j, ExteriorAlgebra.ι K (b i) * ExteriorAlgebra.ι K (b j) =
      -(ExteriorAlgebra.ι K (b j) * ExteriorAlgebra.ι K (b i)) := fun i j => by
    have := ι_mul_ι_add_swap (Q := (0 : QuadraticForm K V)) (b i) (b j)
    rw [show QuadraticMap.polar (0 : QuadraticForm K V) (b i) (b j) = 0 by
      simp [QuadraticMap.polar], map_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  have sq : ∀ i, ExteriorAlgebra.ι K (b i) * ExteriorAlgebra.ι K (b i) = 0 := fun i =>
    ExteriorAlgebra.ι_sq_zero _
  have kill : ∀ j Z, (1 - h j) (ExteriorAlgebra.ι K (b j) * Z) = 0 := fun j Z => by
    simp only [h, LinearMap.sub_apply, Module.End.one_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.mulLeft_apply]
    erw [contractLeft_ι_mul]
    rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same, one_smul, mul_sub,
      ← mul_assoc, sq, zero_mul, sub_zero, sub_self]
  have comm : ∀ i j, i ≠ j → ∀ Z, (1 - h i) (ExteriorAlgebra.ι K (b j) * Z) =
      ExteriorAlgebra.ι K (b j) * (1 - h i) Z := fun i j hij Z => by
    simp only [h, LinearMap.sub_apply, Module.End.one_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.mulLeft_apply]
    erw [contractLeft_ι_mul]
    rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne hij, zero_smul,
      zero_sub, mul_neg, ← mul_assoc]
    erw [anti i j]
    rw [neg_mul, neg_neg, mul_sub, mul_assoc]
  have hT : ∀ L : List ι', ∀ j Z, T L (ExteriorAlgebra.ι K (b j) * Z) =
      if j ∈ L then 0 else ExteriorAlgebra.ι K (b j) * T L Z := by
    intro L
    induction L with
    | nil => intro j Z; simp [T]
    | cons a L ih =>
      intro j Z
      simp only [T, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
      rw [ih j Z]
      by_cases hjL : j ∈ L
      · simp [hjL]
      · simp only [hjL, ite_false]
        by_cases hja : j = a
        · subst hja; simp [kill]
        · rw [comm a j (Ne.symm hja)]
          simp [hja, hjL]
  have hT1 : ∀ L : List ι', ∀ r : K, T L (algebraMap K _ r) = algebraMap K _ r := by
    intro L r
    induction L with
    | nil => simp [T]
    | cons a L ih =>
      simp only [T, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
      rw [ih]
      simp [h, contractLeft_algebraMap]
  have hrange : ∀ Y, ∃ r : K, T Finset.univ.toList Y = algebraMap K _ r := by
    intro Y
    induction Y using CliffordAlgebra.left_induction with
    | algebraMap r => exact ⟨r, hT1 _ r⟩
    | add x y hx hy =>
      obtain ⟨r, hr⟩ := hx; obtain ⟨s, hs⟩ := hy
      exact ⟨r + s, by rw [map_add, hr, hs, map_add]⟩
    | ι_mul x m _ =>
      refine ⟨0, ?_⟩
      rw [← b.sum_repr m, map_sum, Finset.sum_mul, map_sum, map_zero]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smul, smul_mul_assoc, map_smul]
      erw [hT Finset.univ.toList j x]
      simp
  obtain ⟨r, hr⟩ := hrange X
  refine ⟨r, ?_⟩
  rw [← hr, ← neg_sub]
  exact neg_mem (hTX _)

/-- A basis adapted to a finite filtration `Vf` of `V`: each basis vector `bᵢ` lies in
`Vf(wtᵢ)`, and the coordinate `bᵢ*` vanishes on `Vf(a)` for `a > wtᵢ`. -/
theorem exists_adapted_basis [Module.Finite K V] (hanti : Antitone Vf) (N : ℕ)
    (htop : Vf (-N) = ⊤) (hbot : Vf N = ⊥) :
    ∃ (s : Set V) (b : Basis s K V) (wt : s → ℤ), (∀ i, b i ∈ Vf (wt i)) ∧
      ∀ i a, wt i < a → ∀ v ∈ Vf a, b.coord i v = 0 := by
  have step : ∀ k : ℕ, ∃ s : Set V, s ⊆ Vf ((N : ℤ) - k) ∧ LinearIndepOn K id s ∧
      ∀ a : ℤ, (N : ℤ) - k ≤ a → (Vf a : Set V) ⊆ Submodule.span K (s ∩ Vf a) := by
    intro k
    induction k with
    | zero =>
      refine ⟨∅, by simp, linearIndepOn_empty K id, fun a ha => ?_⟩
      have : Vf a = ⊥ := eq_bot_iff.mpr (hbot ▸ hanti (by simpa using ha))
      rw [this]; simp
    | succ k ih =>
      obtain ⟨s, hs, hli, hspan⟩ := ih
      have hst : s ⊆ Vf ((N : ℤ) - (k + 1 : ℕ)) :=
        hs.trans (hanti (by push_cast; omega))
      obtain ⟨b, hbt, hsb, htb, hbli⟩ := exists_linearIndepOn_id_extension hli hst
      refine ⟨b, hbt, hbli, fun a ha => ?_⟩
      by_cases hak : (N : ℤ) - k ≤ a
      · exact (hspan a hak).trans (Submodule.span_mono (Set.inter_subset_inter_left _ hsb))
      · have ha' : a = (N : ℤ) - (k + 1 : ℕ) := by push_cast at ha ⊢; omega
        subst ha'
        rw [Set.inter_eq_left.mpr hbt]
        exact htb
  obtain ⟨s, -, hli, hspan⟩ := step (2 * N)
  have hli' : LinearIndependent K ((↑) : s → V) := hli
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((↑) : s → V)) := by
    rw [Subtype.range_coe]
    intro v _
    have := hspan (-N) (by push_cast; omega) (show v ∈ Vf (-N) by rw [htop]; trivial)
    exact Submodule.span_mono Set.inter_subset_left this
  let b := Basis.mk hli' hsp
  have hex : ∀ x : s, ∃ k : ℕ, (x : V) ∈ Vf ((N : ℤ) - k) := fun x =>
    ⟨2 * N, by rw [show (N : ℤ) - (2 * N : ℕ) = -N by push_cast; ring, htop]; trivial⟩
  classical
  let kx : s → ℕ := fun x => Nat.find (hex x)
  refine ⟨s, b, fun x => (N : ℤ) - kx x, fun x => ?_, fun x a ha v hv => ?_⟩
  · rw [Basis.mk_apply]; exact Nat.find_spec (hex x)
  · have ha : (N : ℤ) - kx x < a := ha
    have hkx : kx x ≤ 2 * N := Nat.find_min' (hex x) (by
      rw [show (N : ℤ) - (2 * N : ℕ) = -N by push_cast; ring, htop]; trivial)
    have hxa : (x : V) ∉ Vf a := by
      intro hxa
      by_cases haN : a ≤ N
      · have : (x : V) ∈ Vf ((N : ℤ) - (N - a).toNat) := by
          rwa [show (N : ℤ) - (N - a).toNat = a by omega]
        have := Nat.find_min (hex x) (m := (N - a).toNat)
          (show (N - a).toNat < kx x by omega)
        exact this (by assumption)
      · have : (x : V) ∈ Vf N := hanti (by omega) hxa
        rw [hbot, Submodule.mem_bot] at this
        exact hli'.ne_zero x this
    have hv' := hspan a (by push_cast; omega) hv
    have himg : s ∩ (Vf a : Set V) = b '' {y : s | (y : V) ∈ Vf a} := by
      ext y
      simp only [b, Basis.coe_mk, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_image,
        Set.mem_ofPred_eq]
      exact ⟨fun ⟨hy, hya⟩ => ⟨⟨y, hy⟩, hya, rfl⟩, fun ⟨y', hy', e⟩ => e ▸ ⟨y'.2, hy'⟩⟩
    rw [himg, SetLike.mem_coe, Basis.mem_span_image] at hv'
    rw [Basis.coord_apply]
    by_contra hne
    exact hxa (hv' (Finsupp.mem_support_iff.mpr hne))

end WeightFiltration

section FlagWeights

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V}

/-- Clamp an integer into the index range `0, …, len` of a flag. -/
def IsotropicFlag.idx (F : IsotropicFlag Q) (t : ℤ) : Fin (F.len + 1) :=
  ⟨min t.toNat F.len, by omega⟩

/-- The weight filtration of `V` attached to an isotropic flag `Z₁ ⊂ ⋯ ⊂ Z_r` (the filtration
of the cocharacter defining the parabolic, Thesis §5.2): `V_{≥w} = Z_{r+1−w}` for `w ≥ 1` and
`V_{≥w} = Z_{r+w}ᗮ` for `w ≤ 0` (indices clamped to `0, …, r`). -/
def flagWt (F : IsotropicFlag Q) (w : ℤ) : Submodule K V :=
  if 1 ≤ w then F.sub (F.idx (F.len + 1 - w))
  else (bform Q).orthogonal (F.sub (F.idx (F.len + w)))

theorem bform_comm (Q : QuadraticForm K V) (x y : V) : bform Q x y = bform Q y x :=
  QuadraticMap.associated_isSymm K Q x y

/-- `b` vanishes on a totally isotropic subspace. -/
theorem bform_eq_zero_of_isTotallyIsotropic {U : Submodule K V} (hU : IsTotallyIsotropic Q U)
    {u v : V} (hu : u ∈ U) (hv : v ∈ U) : bform Q u v = 0 := by
  rw [bform, QuadraticMap.associated_apply, hU _ (add_mem hu hv), hU u hu, hU v hv]
  simp

namespace IsotropicFlag

variable (F : IsotropicFlag Q)

omit [Invertible (2 : K)] in
theorem idx_mono {s t : ℤ} (h : s ≤ t) : F.idx s ≤ F.idx t := by
  simp only [idx, Fin.mk_le_mk]; omega

omit [Invertible (2 : K)] in
theorem sub_mono {i j : Fin (F.len + 1)} (h : i ≤ j) : F.sub i ≤ F.sub j :=
  F.strictMono.monotone h

theorem flagWt_of_pos {w : ℤ} (hw : 1 ≤ w) : flagWt F w = F.sub (F.idx (F.len + 1 - w)) := by
  simp only [flagWt, hw, ↓reduceIte]

theorem flagWt_of_nonpos {w : ℤ} (hw : w ≤ 0) :
    flagWt F w = (bform Q).orthogonal (F.sub (F.idx (F.len + w))) := by
  have : ¬1 ≤ w := by omega
  simp only [flagWt, this, ↓reduceIte]

theorem sub_le_orthogonal (i j : Fin (F.len + 1)) :
    F.sub i ≤ (bform Q).orthogonal (F.sub j) := by
  intro u hu
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro v hv
  exact bform_eq_zero_of_isTotallyIsotropic (F.isotropic (Fin.last F.len))
    (F.sub_mono (Fin.le_last j) hv) (F.sub_mono (Fin.le_last i) hu)

theorem flagWt_anti : Antitone (flagWt F) := by
  intro a b hab
  by_cases hb : 1 ≤ b
  · rw [F.flagWt_of_pos hb]
    by_cases ha : 1 ≤ a
    · rw [F.flagWt_of_pos ha]; exact F.sub_mono (F.idx_mono (by omega))
    · rw [F.flagWt_of_nonpos (by omega)]; exact F.sub_le_orthogonal _ _
  · rw [F.flagWt_of_nonpos (by omega), F.flagWt_of_nonpos (by omega)]
    exact LinearMap.BilinForm.orthogonal_le (F.sub_mono (F.idx_mono (by omega)))

/-- `V_{≥a} ⊥ V_{≥b}` for `a + b ≥ 1`. -/
theorem bform_flagWt {a b : ℤ} (hab : 1 ≤ a + b) {u v : V} (hu : u ∈ flagWt F a)
    (hv : v ∈ flagWt F b) : bform Q u v = 0 := by
  wlog ha : 1 ≤ a generalizing a b u v
  · rw [bform_comm]; exact this (by omega) hv hu (by omega)
  rw [F.flagWt_of_pos ha] at hu
  by_cases hb : 1 ≤ b
  · rw [F.flagWt_of_pos hb] at hv
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp
      (F.sub_le_orthogonal (F.idx (F.len + 1 - b)) (F.idx (F.len + 1 - a)) hv)) u hu
  · rw [F.flagWt_of_nonpos (by omega)] at hv
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hv) u
      (F.sub_mono (F.idx_mono (by omega)) hu)

theorem flagWt_eq_bot {a : ℤ} (ha : (F.len : ℤ) < a) : flagWt F a = ⊥ := by
  rw [F.flagWt_of_pos (by omega), show F.idx (F.len + 1 - a) = 0 by
    simp only [idx, Fin.ext_iff, Fin.val_zero]; omega, F.sub_zero]

theorem flagWt_eq_top {a : ℤ} (ha : a ≤ -(F.len : ℤ)) : flagWt F a = ⊤ := by
  rw [F.flagWt_of_nonpos (by omega), show F.idx (F.len + a) = 0 by
    simp only [idx, Fin.ext_iff, Fin.val_zero]; omega, F.sub_zero,
    LinearMap.BilinForm.orthogonal_bot]

/-- Self-duality `V_{≥w+1}ᗮ ⊆ V_{≥−w}` (nondegenerate, finite-dimensional `V`). -/
theorem orthogonal_flagWt_le [Module.Finite K V] (hQ : IsNondeg Q) (w : ℤ) :
    (bform Q).orthogonal (flagWt F (w + 1)) ≤ flagWt F (-w) := by
  by_cases hw : 0 ≤ w
  · rw [F.flagWt_of_pos (by omega), F.flagWt_of_nonpos (by omega),
      show (F.len : ℤ) + 1 - (w + 1) = F.len + -w by ring]
  · rw [F.flagWt_of_nonpos (by omega), F.flagWt_of_pos (by omega),
      LinearMap.BilinForm.orthogonal_orthogonal hQ
        (QuadraticForm.associated_isSymm (S := K) Q).isRefl,
      show (F.len : ℤ) + (w + 1) = F.len + 1 - -w by ring]

/-- `V_{≥−w} = V_{≥w+1}ᗮ` for `w ≥ 0` (by definition). -/
theorem flagWt_neg_eq_orthogonal {w : ℤ} (hw : 0 ≤ w) :
    flagWt F (-w) = (bform Q).orthogonal (flagWt F (w + 1)) := by
  rw [F.flagWt_of_pos (w := w + 1) (by omega), F.flagWt_of_nonpos (w := -w) (by omega),
    show (F.len : ℤ) + 1 - (w + 1) = F.len + -w by ring]

/-- `V_{≥w+1} = V_{≥−w}ᗮ` for `w < 0` (by definition). -/
theorem flagWt_succ_eq_orthogonal {w : ℤ} (hw : w < 0) :
    flagWt F (w + 1) = (bform Q).orthogonal (flagWt F (-w)) := by
  rw [F.flagWt_of_nonpos (w := w + 1) (by omega), F.flagWt_of_pos (w := -w) (by omega),
    show (F.len : ℤ) + (w + 1) = F.len + 1 - -w by ring]

/-- Elements of `K^×·N_F` act trivially on the graded pieces: `(P(g) − 1) V_{≥w} ⊆ V_{≥w+1}`. -/
theorem specP_sub_mem_flagWt {g : GSpin Q} (hg : g ∈ flagUnipSO F) :
    ∀ w : ℤ, ∀ v ∈ flagWt F w, specP Q g v - v ∈ flagWt F (w + 1) := by
  -- positive weights, for any element of `flagUnipSO`
  have hpos : ∀ g ∈ flagUnipSO F, ∀ w : ℤ, 1 ≤ w → ∀ v ∈ flagWt F w,
      specP Q g v - v ∈ flagWt F (w + 1) := by
    intro g hg w hw v hv
    rw [F.flagWt_of_pos hw] at hv
    rw [F.flagWt_of_pos (by omega)]
    by_cases hwr : (F.len : ℤ) + 1 - w ≤ 0
    · rw [show F.idx (F.len + 1 - w) = 0 by
        simp only [idx, Fin.ext_iff, Fin.val_zero]; omega, F.sub_zero, Submodule.mem_bot] at hv
      subst hv; simp
    · let i : Fin F.len := ⟨(F.len - w).toNat, by omega⟩
      have h1 : F.idx (F.len + 1 - w) = i.succ := by
        simp only [idx, i, Fin.ext_iff, Fin.val_succ]; omega
      have h2 : F.idx (F.len + 1 - (w + 1)) = i.castSucc := by
        simp only [idx, i, Fin.ext_iff, Fin.val_castSucc]; omega
      rw [h1] at hv
      rw [h2]
      exact hg.2.1 i v hv
  intro w v hv
  by_cases hw : 1 ≤ w
  · exact hpos g hg w hw v hv
  by_cases hw0 : w = 0
  · subst hw0
    rw [F.flagWt_of_nonpos le_rfl, show F.idx (F.len + 0) = Fin.last F.len by
      simp only [idx, Fin.ext_iff, Fin.val_last]; omega] at hv
    rw [zero_add, F.flagWt_of_pos le_rfl, show F.idx (F.len + 1 - 1) = Fin.last F.len by
      simp only [idx, Fin.ext_iff, Fin.val_last]; omega]
    exact hg.2.2 v hv
  -- negative weights, by duality with the positive ones for `g⁻¹`
  have hgi := (flagUnipSO F).inv_mem hg
  have hv' : v ∈ flagWt F w := hv
  rw [F.flagWt_of_nonpos (by omega)]
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro z hz
  have hz' : z ∈ flagWt F (-w) := by
    rw [F.flagWt_of_pos (by omega), show (F.len : ℤ) + 1 - -w = F.len + (w + 1) by ring]
    exact hz
  have key := hpos g⁻¹ hgi (-w) (by omega) z hz'
  -- `b(z, P v − v) = b(P⁻¹ z − z, v)`
  have e : bform Q z (specP Q g v - v) = bform Q (specP Q g⁻¹ z - z) v := by
    have := bform_specP g (specP Q g⁻¹ z) v
    rw [specP_inv_apply_apply] at this
    simp only [map_sub, LinearMap.sub_apply]
    rw [this]
  change bform Q z (specP Q g v - v) = 0
  rw [e]
  exact F.bform_flagWt (by omega) key hv'

end IsotropicFlag

end FlagWeights

section SelfDualFiltration

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {Vf : ℤ → Submodule K V}

/-- A weight filtration `V_{≥w}` of `(V, q)` with weights in `[−N, N]` and `V_{≥a} ⊥ V_{≥b}` for
`a + b ≥ 1` (e.g. the filtration of a cocharacter of `SO(V)`). -/
structure IsWtFil (Q : QuadraticForm K V) (Vf : ℤ → Submodule K V) (N : ℕ) : Prop where
  anti : Antitone Vf
  orth : ∀ a b, 1 ≤ a + b → ∀ u ∈ Vf a, ∀ v ∈ Vf b, bform Q u v = 0
  top : ∀ a, a ≤ -(N : ℤ) → Vf a = ⊤
  bot : ∀ a, (N : ℤ) < a → Vf a = ⊥

/-- The change of form `C(Q) → Λ(V)` preserves the weight filtration. -/
theorem equivExterior_mem_wtFil {N : ℕ} (hV : IsWtFil Q Vf N) {j : ℤ} {x : CliffordAlgebra Q}
    (hx : x ∈ wtFil Q Vf j) : equivExterior Q x ∈ wtFil (0 : QuadraticForm K V) Vf j := by
  simp only [equivExterior, changeFormEquiv_apply]
  refine changeForm_mem_wtFil _ (fun a b hab u hu v hv => ?_) hx
  rw [map_neg, LinearMap.neg_apply, LinearMap.neg_apply]
  exact neg_eq_zero.mpr (hV.orth a b hab u hu v hv)

/-- The change of form `Λ(V) → C(Q)` preserves the weight filtration. -/
theorem equivExterior_symm_mem_wtFil {N : ℕ} (hV : IsWtFil Q Vf N) {j : ℤ}
    {X : ExteriorAlgebra K V} (hX : X ∈ wtFil (0 : QuadraticForm K V) Vf j) :
    (equivExterior Q).symm X ∈ wtFil Q Vf j := by
  simp only [equivExterior, changeFormEquiv_symm, changeFormEquiv_apply]
  refine changeForm_mem_wtFil _ (fun a b hab u hu v hv => ?_) hX
  rw [LinearMap.neg_apply, LinearMap.neg_apply, map_neg, LinearMap.neg_apply,
    LinearMap.neg_apply, neg_neg]
  exact hV.orth a b hab u hu v hv

/-- Positive-weight elements of `C(V)` are nilpotent (via the exterior algebra). -/
theorem isNilpotent_of_mem_wtFil_one [Module.Finite K V] {N : ℕ} (hV : IsWtFil Q Vf N)
    {x : CliffordAlgebra Q} (hx : x ∈ wtFil Q Vf 1) : IsNilpotent x := by
  have hpow : ∀ n : ℕ, x ^ (n + 1) ∈ wtFil Q Vf (n + 1) := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      rw [pow_succ]
      exact wtFil_anti (le_of_eq (by push_cast; ring)) (mul_mem_wtFil ih hx)
  refine ⟨N * finrank K V + 1, ?_⟩
  have h := equivExterior_mem_wtFil hV (hpow (N * finrank K V))
  rw [wtFil_exterior_eq_bot (R := N) hV.bot (by push_cast; omega), Submodule.mem_bot] at h
  exact (equivExterior Q).injective (by rw [h, map_zero])

omit [Invertible (2 : K)] in
/-- If `x` is even, `x ι(v) = ι(P v) x`, and `P` is trivial on the graded pieces, then for
`x` of weight `≥ m` and `v ∈ V_{≥w}`, `polar(v,·) ⌋ x = ι(v) x − x ι(v) = −ι(Pv − v) x` has weight
`≥ m + w + 1`. -/
theorem contractLeft_polar_mem_wtFil {x : CliffordAlgebra Q} (hx0 : x ∈ evenOdd Q 0)
    {P : V →ₗ[K] V} (hPx : ∀ v, x * ι Q v = ι Q (P v) * x)
    (hP : ∀ w, ∀ v ∈ Vf w, P v - v ∈ Vf (w + 1)) {m : ℤ} (hxm : x ∈ wtFil Q Vf m)
    {w : ℤ} {v : V} (hv : v ∈ Vf w) :
    contractLeft (QuadraticMap.polarBilin Q v) x ∈ wtFil Q Vf (m + w + 1) := by
  rw [← ι_mul_sub_involute_mul, involute_eq_of_mem_even hx0, hPx, ← sub_mul, ← map_sub,
    ← neg_sub, map_neg, neg_mul]
  exact neg_mem (wtFil_anti (le_of_eq (by ring)) (ι_mul_mem_wtFil (hP w v hv) hxm))

/-- **Leading-term step.**  Under the hypotheses of `contractLeft_polar_mem_wtFil`, with `V`
nondegenerate and the filtration self-dual (`V_{≥w+1}ᗮ ⊆ V_{≥−w}`), an `x` of weight `≥ m` is a
scalar modulo weight `≥ m + 1` (graded form of `eq_algebraMap_of_commute_ι`). -/
theorem exists_sub_algebraMap_mem_wtFil [Module.Finite K V] (hQ : IsNondeg Q) {N : ℕ}
    (hV : IsWtFil Q Vf N) (hdual : ∀ w, (bform Q).orthogonal (Vf (w + 1)) ≤ Vf (-w))
    {x : CliffordAlgebra Q} (hx0 : x ∈ evenOdd Q 0)
    {P : V →ₗ[K] V} (hPx : ∀ v, x * ι Q v = ι Q (P v) * x)
    (hP : ∀ w, ∀ v ∈ Vf w, P v - v ∈ Vf (w + 1)) {m : ℤ} (hxm : x ∈ wtFil Q Vf m) :
    ∃ c : K, x - algebraMap K _ c ∈ wtFil Q Vf (m + 1) := by
  classical
  obtain ⟨s, b, wt, hb, hcoord⟩ := exists_adapted_basis hV.anti (N + 1)
    (hV.top _ (by push_cast; omega)) (hV.bot _ (by push_cast; omega))
  have : Fintype s := FiniteDimensional.fintypeBasisIndex b
  have hX : ∀ i, contractLeft (b.coord i) (equivExterior Q x) ∈
      wtFil (0 : QuadraticForm K V) Vf (m - wt i + 1) := by
    intro i
    obtain ⟨w0, hw0⟩ := ((bform Q).toDual hQ).surjective (b.coord i)
    have hpol : QuadraticMap.polarBilin Q ((⅟2 : K) • w0) = b.coord i := by
      rw [← hw0]
      ext y
      change _ = bform Q w0 y
      rw [QuadraticMap.polarBilin_apply_apply,
        polar_eq_two_mul_bform, map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc,
        mul_invOf_self, one_mul]
    have hu : (⅟2 : K) • w0 ∈ Vf (-wt i) := by
      refine Submodule.smul_mem _ _ (hdual (wt i) ?_)
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      rw [bform_comm]
      have : bform Q w0 n = b.coord i n := by rw [← hw0]; rfl
      rw [this]
      exact hcoord i (wt i + 1) (by omega) n hn
    rw [← hpol]
    simp only [equivExterior, changeFormEquiv_apply]
    rw [← changeForm_contractLeft]
    have h2 := equivExterior_mem_wtFil hV (contractLeft_polar_mem_wtFil hx0 hPx hP hxm hu)
    simp only [equivExterior, changeFormEquiv_apply] at h2
    exact wtFil_anti (le_of_eq (by ring)) h2
  obtain ⟨r, hr⟩ := exterior_sub_algebraMap_mem_wtFil b wt hb hcoord _ hX
  refine ⟨r, ?_⟩
  have := equivExterior_symm_mem_wtFil hV hr
  rwa [map_sub, LinearEquiv.symm_apply_apply, show (equivExterior Q).symm (algebraMap K _ r) =
    algebraMap K _ r by simp [equivExterior, changeFormEquiv_symm]] at this

/-- Iterating the leading-term step from the bottom weight: `x = c + (positive weight)`. -/
theorem exists_sub_algebraMap_mem_wtFil_one [Module.Finite K V] (hQ : IsNondeg Q) {N : ℕ}
    (hV : IsWtFil Q Vf N) (hdual : ∀ w, (bform Q).orthogonal (Vf (w + 1)) ≤ Vf (-w))
    {x : CliffordAlgebra Q} (hx0 : x ∈ evenOdd Q 0)
    {P : V →ₗ[K] V} (hPx : ∀ v, x * ι Q v = ι Q (P v) * x)
    (hP : ∀ w, ∀ v ∈ Vf w, P v - v ∈ Vf (w + 1)) :
    ∃ c : K, x - algebraMap K _ c ∈ wtFil Q Vf 1 := by
  have hup : ∀ k : ℕ, x ∈ wtFil Q Vf (-k) → x ∈ wtFil Q Vf 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_wtFil hQ hV hdual hx0 hPx hP hk
      refine ih ?_
      have hc' : x - algebraMap K _ c ∈ wtFil Q Vf (-k) :=
        wtFil_anti (le_of_eq (by push_cast; ring)) hc
      simpa using add_mem hc' (algebraMap_mem_wtFil (Q := Q) (Vf := Vf) c
        (by omega : -(k : ℤ) ≤ 0))
  obtain ⟨j, hj⟩ := exists_mem_wtFil (Q := Q) (Vf := Vf) (R := -(N : ℤ))
    (fun v => by rw [hV.top _ le_rfl]; trivial) x
  have h0 := hup (-j).toNat (wtFil_anti (by omega) hj)
  simpa using exists_sub_algebraMap_mem_wtFil hQ hV hdual hx0 hPx hP h0

/-- If moreover `x − 1` is nilpotent, then `x − 1` has positive weight. -/
theorem sub_one_mem_wtFil_one [Module.Finite K V] (hQ : IsNondeg Q) {N : ℕ}
    (hV : IsWtFil Q Vf N) (hdual : ∀ w, (bform Q).orthogonal (Vf (w + 1)) ≤ Vf (-w))
    {x : CliffordAlgebra Q} (hx0 : x ∈ evenOdd Q 0)
    {P : V →ₗ[K] V} (hPx : ∀ v, x * ι Q v = ι Q (P v) * x)
    (hP : ∀ w, ∀ v ∈ Vf w, P v - v ∈ Vf (w + 1)) (hx : IsNilpotent (x - 1)) :
    x - 1 ∈ wtFil Q Vf 1 := by
  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_wtFil_one hQ hV hdual hx0 hPx hP
  have hcomm : Commute (x - 1) (x - algebraMap K _ c) :=
    ((Commute.refl x).sub_right (Algebra.commutes c x).symm).sub_left
      ((Commute.one_left x).sub_right (Commute.one_left _))
  have hn := Commute.isNilpotent_sub hcomm hx (isNilpotent_of_mem_wtFil_one hV hc)
  rw [sub_sub_sub_cancel_left, ← map_one (algebraMap K (CliffordAlgebra Q)), ← map_sub,
    IsNilpotent.map_iff (algebraMap K (CliffordAlgebra Q)).injective] at hn
  have hc1 : c = 1 := by
    have := hn.eq_zero
    rwa [sub_eq_zero] at this
  rw [hc1, map_one] at hc
  exact hc

end SelfDualFiltration

section FlagUnipLift

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {F : IsotropicFlag Q}

theorem IsotropicFlag.isWtFil (F : IsotropicFlag Q) : IsWtFil Q (flagWt F) F.len where
  anti := F.flagWt_anti
  orth _ _ hab _ hu _ hv := F.bform_flagWt hab hu hv
  top _ ha := F.flagWt_eq_top ha
  bot _ ha := F.flagWt_eq_bot ha

/-- **The lift of the unipotent radical** (finite-dimensional nondegenerate case): for
`g, h ∈ K^×·N_F` with `g − 1`, `h − 1` nilpotent, `gh − 1` is nilpotent.  Both `g − 1` and
`h − 1` have positive weight for the weight filtration of `C(V)` attached to the flag. -/
theorem isNilpotent_mul_sub_one_of_flagUnipSO_of_nondeg [Module.Finite K V] (hQ : IsNondeg Q)
    {g h : GSpin Q} (hg : g ∈ flagUnipSO F) (hh : h ∈ flagUnipSO F)
    (hg' : IsNilpotent (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1))
    (hh' : IsNilpotent (((h : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1)) :
    IsNilpotent ((((g * h : GSpin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1) := by
  have hone : ∀ y : GSpin Q, y ∈ flagUnipSO F →
      IsNilpotent (((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1) →
      ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1 ∈ wtFil Q (flagWt F) 1 := by
    intro y hy hy'
    have hx0 : ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
      have := y.2.1
      rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at this
      exact this
    refine sub_one_mem_wtFil_one hQ F.isWtFil (F.orthogonal_flagWt_le hQ) hx0
      (P := (specP Q y : V →ₗ[K] V)) (fun v => ?_) (F.specP_sub_mem_flagWt hy) hy'
    rw [LinearEquiv.coe_coe, ι_specP, mul_assoc, Units.inv_mul, mul_one]
  have h1 := hone g hg hg'
  have h2 := hone h hh hh'
  have e : (((g * h : GSpin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1 =
      (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1) *
        (((h : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1) +
      (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1) +
      (((h : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1) := by
    simp only [Subgroup.coe_mul, Units.val_mul]; noncomm_ring
  rw [e]
  exact isNilpotent_of_mem_wtFil_one F.isWtFil
    (add_mem (add_mem (wtFil_anti (by norm_num) (mul_mem_wtFil h1 h2)) h1) h2)

end FlagUnipLift

section Degenerate

/-! ### Degenerate `V`: pass to a complement of the radical

For a finite-dimensional, possibly degenerate `(V, q)` with radical `R`, choose `V = V₀ ⊕ R`.
The projection `p : V → V₀` is an isometry, so it induces `π = C(p) : C(V) → C(V₀)`, and
`V₀` is nondegenerate.  The kernel of `π` consists of nilpotent elements: every `z` is
`C(i)(π z)` plus an element of positive weight for the filtration "`R` in weight `1`". -/

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V}

/-- The filtration with the radical `R` in weight `1` and everything in weight `0`. -/
def radWt (Q : QuadraticForm K V) (w : ℤ) : Submodule K V :=
  if w ≤ 0 then ⊤ else if w = 1 then LinearMap.ker (bform Q) else ⊥

theorem bform_eq_zero_of_mem_ker {r : V} (hr : r ∈ LinearMap.ker (bform Q)) (y : V) :
    bform Q r y = 0 := by
  rw [LinearMap.mem_ker] at hr; rw [hr]; rfl

theorem isWtFil_radWt (Q : QuadraticForm K V) : IsWtFil Q (radWt Q) 1 where
  anti a b hab := by
    unfold radWt
    split_ifs <;> first | exact le_rfl | exact le_top | exact bot_le | omega
  orth a b hab u hu v hv := by
    unfold radWt at hu hv
    by_cases ha : 1 ≤ a
    · split_ifs at hu with h1 h2
      · omega
      · exact bform_eq_zero_of_mem_ker hu v
      · rw [Submodule.mem_bot] at hu; subst hu; simp
    · have hb : 1 ≤ b := by omega
      split_ifs at hv with h1 h2
      · omega
      · rw [bform_comm]; exact bform_eq_zero_of_mem_ker hv u
      · rw [Submodule.mem_bot] at hv; subst hv; simp
  top a ha := by
    have : a ≤ 0 := by omega
    simp only [radWt, this, ↓reduceIte]
  bot a ha := by
    have h1 : ¬a ≤ 0 := by omega
    have h2 : ¬a = 1 := by omega
    simp only [radWt, h1, h2, ↓reduceIte]

theorem mem_wtFil_radWt_zero (x : CliffordAlgebra Q) : x ∈ wtFil Q (radWt Q) 0 := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => exact algebraMap_mem_wtFil r le_rfl
  | add x y hx hy => exact add_mem hx hy
  | ι_mul x m hx =>
    have : m ∈ radWt Q 0 := by simp [radWt]
    simpa using ι_mul_mem_wtFil this hx

variable [Module.Finite K V]

/-- **Finite-dimensional case** of the lift of the unipotent radical, for arbitrary (possibly
degenerate) `q`: reduce to the nondegenerate space `V₀ = V/R`. -/
theorem isNilpotent_mul_sub_one_of_flagUnipSO_of_finite {F : IsotropicFlag Q}
    {g h : GSpin Q} (hg : g ∈ flagUnipSO F) (hh : h ∈ flagUnipSO F)
    (hg' : IsNilpotent (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1))
    (hh' : IsNilpotent (((h : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1)) :
    IsNilpotent ((((g * h : GSpin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1) := by
  set R := LinearMap.ker (bform Q)
  obtain ⟨V0, hc⟩ := Submodule.exists_isCompl R
  have hc' : IsCompl V0 R := hc.symm
  set p : V →ₗ[K] V0 := Submodule.projectionOnto V0 R hc'
  have hp_left : ∀ u : V0, p u = u := Submodule.projectionOnto_apply_left hc'
  have hp_sub : ∀ v, v - (p v : V) ∈ R := fun v => by
    rw [← Submodule.projectionOnto_apply_eq_zero_iff hc', map_sub, hp_left, sub_self]
  have hp_R : ∀ r ∈ R, p r = 0 := fun r hr =>
    (Submodule.projectionOnto_apply_eq_zero_iff hc').mpr hr
  -- `b(p x, p y) = b(x, y)`
  have hbp : ∀ x y, bform Q (p x : V) (p y : V) = bform Q x y := by
    intro x y
    have hx := hp_sub x; have hy := hp_sub y
    have h1 : bform Q x y = bform Q (p x : V) y := by
      have : bform Q (x - p x) y = 0 := bform_eq_zero_of_mem_ker hx y
      rwa [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    have h2 : bform Q (p x : V) y = bform Q (p x : V) (p y : V) := by
      have : bform Q (y - p y) (p x : V) = 0 := bform_eq_zero_of_mem_ker hy _
      rwa [map_sub, LinearMap.sub_apply, sub_eq_zero, bform_comm Q y,
        bform_comm Q (p y : V)] at this
    rw [h1, h2]
  set Q0 : QuadraticForm K V0 := Q.comp V0.subtype
  have hbQ0 : ∀ u u' : V0, bform Q0 u u' = bform Q u u' := fun u u' => by
    simp [Q0, bform, QuadraticMap.associated_comp]
  have hQ0 : IsNondeg Q0 := by
    rw [isNondeg_iff]
    intro x hx
    have hxR : (x : V) ∈ R := by
      rw [LinearMap.mem_ker]
      ext v
      have := hx (p v)
      rw [hbQ0] at this
      have e : bform Q (x : V) v = bform Q (p x : V) (p v : V) := (hbp _ _).symm
      rw [hp_left] at e
      simp [e, this]
    have : (x : V) ∈ V0 ⊓ R := ⟨x.2, hxR⟩
    rw [hc'.inf_eq_bot, Submodule.mem_bot] at this
    exact Subtype.ext this
  have hQp : ∀ v, Q0 (p v) = Q v := by
    intro v
    have hr := hp_sub v
    change Q (p v : V) = Q v
    conv_rhs => rw [show v = (p v : V) + (v - (p v : V)) by abel]
    rw [QuadraticMap.map_add Q, show Q (v - (p v : V)) = 0 by
      rw [← QuadraticMap.associated_eq_self_apply K]; exact bform_eq_zero_of_mem_ker hr _]
    rw [QuadraticMap.polar_comm, polar_eq_two_mul_bform, bform_eq_zero_of_mem_ker hr]
    simp
  let pp : Q →qᵢ Q0 := ⟨p, hQp⟩
  let ip : Q0 →qᵢ Q := ⟨V0.subtype, fun _ => rfl⟩
  let π := CliffordAlgebra.map pp
  -- the kernel of `π` is nilpotent
  have hker : ∀ z : CliffordAlgebra Q, z - CliffordAlgebra.map ip (π z) ∈ wtFil Q (radWt Q) 1 := by
    intro z
    induction z using CliffordAlgebra.left_induction with
    | algebraMap r => simp [π, AlgHom.commutes]
    | add x y hx hy =>
      rw [map_add, map_add, add_sub_add_comm]; exact add_mem hx hy
    | ι_mul x v hx =>
      rw [map_mul, map_mul, map_apply_ι, map_apply_ι]
      have hipp : ip (pp v) = (p v : V) := rfl
      have e : ι Q v * x - ι Q (ip (pp v)) * CliffordAlgebra.map ip (π x) =
          ι Q (v - (p v : V)) * x + ι Q (p v : V) * (x - CliffordAlgebra.map ip (π x)) := by
        rw [hipp, map_sub, sub_mul, mul_sub]; abel
      rw [e]
      refine add_mem ?_ ?_
      · have hr : v - (p v : V) ∈ radWt Q 1 := by
          rw [show radWt Q 1 = R by simp [radWt, R]]; exact hp_sub v
        simpa using ι_mul_mem_wtFil hr (mem_wtFil_radWt_zero x)
      · have h0 : (p v : V) ∈ radWt Q 0 := by simp [radWt]
        simpa using ι_mul_mem_wtFil h0 hx
  -- the filtration of `V₀`
  set Vf0 : ℤ → Submodule K V0 := fun w => (flagWt F w).map p
  have horth_map : ∀ S : Submodule K V,
      ((bform Q).orthogonal S).map p = (bform Q0).orthogonal (S.map p) := by
    intro S
    ext u
    simp only [Submodule.mem_map, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩ _ ⟨s, hs, rfl⟩
      change bform Q0 (p s) (p y) = 0
      rw [hbQ0, hbp]; exact hy s hs
    · intro hu
      refine ⟨u, fun s hs => ?_, hp_left u⟩
      have := hu (p s) ⟨s, hs, rfl⟩
      change bform Q0 (p s) u = 0 at this
      rw [hbQ0, ← hp_left u, hbp] at this
      exact this
  have hV0 : IsWtFil Q0 Vf0 F.len := by
    refine ⟨fun a b hab => Submodule.map_mono (F.flagWt_anti hab), ?_, ?_, ?_⟩
    · intro a b hab
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [hbQ0, hbp]; exact F.bform_flagWt hab hx hy
    · intro a ha
      change (flagWt F a).map p = ⊤
      rw [F.flagWt_eq_top ha, Submodule.map_top, Submodule.range_projectionOnto]
    · intro a ha
      change (flagWt F a).map p = ⊥
      rw [F.flagWt_eq_bot ha, Submodule.map_bot]
  have hdual0 : ∀ w, (bform Q0).orthogonal (Vf0 (w + 1)) ≤ Vf0 (-w) := by
    intro w
    by_cases hw : 0 ≤ w
    · change _ ≤ (flagWt F (-w)).map p
      rw [F.flagWt_neg_eq_orthogonal hw, horth_map]
    · change (bform Q0).orthogonal ((flagWt F (w + 1)).map p) ≤ _
      rw [F.flagWt_succ_eq_orthogonal (by omega), horth_map,
        LinearMap.BilinForm.orthogonal_orthogonal hQ0
          (QuadraticForm.associated_isSymm (S := K) Q0).isRefl]
  -- the image of `y ∈ K^×·N_F` with `y − 1` nilpotent has `π(y) − 1` of positive weight
  have hone : ∀ y : GSpin Q, y ∈ flagUnipSO F →
      IsNilpotent (((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1) →
      π ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1 ∈ wtFil Q0 Vf0 1 := by
    intro y hy hy'
    have hx0 : ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
      have := y.2.1
      rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at this
      exact this
    have hPR : ∀ r ∈ R, specP Q y r ∈ R := by
      intro r hr
      rw [LinearMap.mem_ker]
      ext z
      rw [← specP_inv_apply_apply y z]
      simp only [LinearMap.zero_apply]
      rw [show bform Q (specP Q y r) (specP Q y (specP Q y⁻¹ z)) =
        bform Q r (specP Q y⁻¹ z) from bform_specP y r _]
      exact bform_eq_zero_of_mem_ker hr _
    let P0 : V0 →ₗ[K] V0 := p ∘ₗ (specP Q y : V →ₗ[K] V) ∘ₗ V0.subtype
    refine sub_one_mem_wtFil_one hQ0 hV0 hdual0 (map_mem_evenOdd_zero pp hx0) (P := P0)
      (fun u => ?_) (fun w u hu => ?_) (by have := hy'.map π; rwa [map_sub, map_one] at this)
    · have e : ι Q0 u = π (ι Q (u : V)) := by
        change ι Q0 u = CliffordAlgebra.map pp (ι Q (u : V))
        rw [map_apply_ι]
        exact congrArg _ (hp_left u).symm
      have hcomm : ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q (u : V) =
          ι Q (specP Q y u) * ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
        rw [ι_specP, mul_assoc, Units.inv_mul, mul_one]
      rw [e]
      change π _ * π _ = _
      rw [← map_mul, hcomm, map_mul, map_apply_ι]
      rfl
    · obtain ⟨v, hv, rfl⟩ := hu
      refine ⟨specP Q y v - v, F.specP_sub_mem_flagWt hy w v hv, ?_⟩
      have hr := hp_sub v
      have hPv : specP Q y (p v : V) = specP Q y v - specP Q y (v - p v) := by
        rw [map_sub, sub_sub_cancel]
      change p (specP Q y v - v) = p (specP Q y (p v : V)) - p v
      rw [hPv, map_sub, map_sub, hp_R _ (hPR _ hr), sub_zero]
  have h1 := hone g hg hg'
  have h2 := hone h hh hh'
  have e : π ((((g * h : GSpin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1) =
      (π ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1) *
        (π ((h : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1) +
      (π ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1) +
      (π ((h : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1) := by
    simp only [Subgroup.coe_mul, Units.val_mul, map_sub, map_mul, map_one]; noncomm_ring
  have hnil := isNilpotent_of_mem_wtFil_one hV0
    (add_mem (add_mem (wtFil_anti (by norm_num) (mul_mem_wtFil h1 h2)) h1) h2)
  rw [← e] at hnil
  obtain ⟨n, hn⟩ := hnil
  set z := (((g * h : GSpin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1
  have hz := hker (z ^ n)
  rw [map_pow, hn, map_zero, sub_zero] at hz
  obtain ⟨k, hk⟩ := isNilpotent_of_mem_wtFil_one (isWtFil_radWt Q) hz
  exact ⟨n * k, by rw [pow_mul, hk]⟩

end Degenerate

/-! ## Reduction to a finite-dimensional subspace

For a subspace `U ⊆ V`, `C(U) → C(V)` is injective (through `equivExterior` and the exterior
algebra) and `C(U) ∩ ι(V) = ι(U)`; every element of `C(V)` lies in `C(U)` for some
finite-dimensional `U`.  This reduces `isNilpotent_mul_sub_one_of_flagUnipSO` to finite
dimension. -/

section RestrictSubspace

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]


/-- The inclusion of a subspace, as an isometry `(U, q|_U) → (V, q)`. -/
def inclIsometry (Q : QuadraticForm K V) (U : Submodule K V) : Q.comp U.subtype →qᵢ Q where
  toLinearMap := U.subtype
  map_app' _ := rfl

/-- Contraction is natural for isometries. -/
theorem map_contractLeft {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (f : Q₁ →qᵢ Q₂)
    (d : Module.Dual K V₂) (x : CliffordAlgebra Q₁) :
    CliffordAlgebra.map f (contractLeft (d ∘ₗ f.toLinearMap) x) =
      contractLeft d (CliffordAlgebra.map f x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    rw [contractLeft_ι_mul, map_mul, map_apply_ι, contractLeft_ι_mul, map_sub, map_smul, map_mul,
      map_apply_ι, hx]
    rfl

/-- `changeForm` is natural for isometries along the same linear map. -/
theorem map_changeForm {Q₁ Q₁' : QuadraticForm K V₁} {Q₂ Q₂' : QuadraticForm K V₂}
    (f : Q₁ →qᵢ Q₂) (f' : Q₁' →qᵢ Q₂') (hff : ∀ v, f' v = f v)
    {B₁ : LinearMap.BilinForm K V₁} {B₂ : LinearMap.BilinForm K V₂}
    (hB : ∀ a b, B₂ (f a) (f b) = B₁ a b)
    (h₁ : B₁.toQuadraticMap = Q₁' - Q₁) (h₂ : B₂.toQuadraticMap = Q₂' - Q₂)
    (x : CliffordAlgebra Q₁) :
    CliffordAlgebra.map f' (changeForm h₁ x) = changeForm h₂ (CliffordAlgebra.map f x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [changeForm_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    have hd : B₁ m = B₂ (f m) ∘ₗ f'.toLinearMap := by
      ext v; simp [hff, hB]
    rw [changeForm_ι_mul, map_sub, map_mul, map_apply_ι, hd, map_contractLeft, hx, map_mul,
      map_apply_ι, changeForm_ι_mul, hff]

variable [Invertible (2 : K)]

/-- `equivExterior` is natural for isometries. -/
theorem equivExterior_map {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (f : Q₁ →qᵢ Q₂)
    (x : CliffordAlgebra Q₁) :
    equivExterior Q₂ (CliffordAlgebra.map f x) =
      ExteriorAlgebra.map f.toLinearMap (equivExterior Q₁ x) := by
  simp only [equivExterior, changeFormEquiv_apply]
  symm
  refine map_changeForm (Q₁' := 0) (Q₂' := 0) f
    { f.toLinearMap with map_app' := fun _ => rfl } (fun _ => rfl) (fun a b => ?_) _ _ x
  simp only [QuadraticMap.associated_apply, neg_apply, ← map_add, f.map_app]

/-- An isometry with injective underlying linear map induces an injective map of Clifford
algebras (`2` invertible). -/
theorem map_injective_of_injective {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (f : Q₁ →qᵢ Q₂) (hf : Function.Injective f) :
    Function.Injective (CliffordAlgebra.map f) := by
  intro x y hxy
  apply (equivExterior Q₁).injective
  apply ExteriorAlgebra.map_injective_field (f := f.toLinearMap) (LinearMap.ker_eq_bot.mpr hf)
  rw [← equivExterior_map, ← equivExterior_map, hxy]

theorem map_inclIsometry_injective (Q : QuadraticForm K V) (U : Submodule K V) :
    Function.Injective (CliffordAlgebra.map (inclIsometry Q U)) :=
  map_injective_of_injective _ Subtype.val_injective

/-- `C(U) ∩ ι(V) = ι(U)`. -/
theorem exists_eq_ι_of_map_eq_ι {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (f : Q₁ →qᵢ Q₂) (hf : Function.Injective f) {x : CliffordAlgebra Q₁} {v : V₂}
    (hx : CliffordAlgebra.map f x = ι Q₂ v) : ∃ u, f u = v ∧ x = ι Q₁ u := by
  have h1 := congrArg (fun y => ExteriorAlgebra.ιInv (equivExterior Q₂ y)) hx
  simp only [equivExterior_map] at h1
  have e2 : ExteriorAlgebra.ιInv (equivExterior Q₂ (ι Q₂ v)) = v := by
    simp [equivExterior, changeFormEquiv_apply, changeForm_ι, ExteriorAlgebra.ιInv]
  have h3 := LinearMap.congr_fun (ExteriorAlgebra.ιInv_comp_map f.toLinearMap) (equivExterior Q₁ x)
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply] at h3
  rw [h3, e2] at h1
  change f _ = v at h1
  refine ⟨_, h1, map_injective_of_injective f hf ?_⟩
  rw [hx, map_apply_ι, h1]

omit [Invertible (2 : K)] in
theorem ι_mem_range_map_inclIsometry (Q : QuadraticForm K V) {U : Submodule K V} {m : V}
    (hm : m ∈ U) : ι Q m ∈ (CliffordAlgebra.map (inclIsometry Q U)).range :=
  (AlgHom.mem_range _).mpr ⟨ι _ ⟨m, hm⟩, map_apply_ι _ _⟩

omit [Invertible (2 : K)] in
theorem range_map_inclIsometry_mono (Q : QuadraticForm K V) {U U' : Submodule K V}
    (h : U ≤ U') : (CliffordAlgebra.map (inclIsometry Q U)).range ≤
      (CliffordAlgebra.map (inclIsometry Q U')).range := by
  intro y hy
  obtain ⟨x, rfl⟩ := (AlgHom.mem_range _).mp hy
  clear hy
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ r
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | ι_mul x m hx =>
    rw [map_mul, map_apply_ι]
    exact mul_mem (ι_mem_range_map_inclIsometry Q (h m.2)) hx

omit [Invertible (2 : K)] in
/-- Every element of `C(V)` lies in `C(U)` for a finite-dimensional `U ⊆ V`. -/
theorem exists_fg_mem_range_map (Q : QuadraticForm K V) (x : CliffordAlgebra Q) :
    ∃ U : Submodule K V, U.FG ∧ x ∈ (CliffordAlgebra.map (inclIsometry Q U)).range := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    exact ⟨⊥, Submodule.fg_bot, Subalgebra.algebraMap_mem _ r⟩
  | add x y hx hy =>
    obtain ⟨U, hU, hxU⟩ := hx
    obtain ⟨U', hU', hyU⟩ := hy
    exact ⟨U ⊔ U', hU.sup hU', add_mem (range_map_inclIsometry_mono Q le_sup_left hxU)
      (range_map_inclIsometry_mono Q le_sup_right hyU)⟩
  | ι_mul x m hx =>
    obtain ⟨U, hU, hxU⟩ := hx
    refine ⟨U ⊔ K ∙ m, hU.sup (Submodule.fg_span_singleton m), mul_mem ?_
      (range_map_inclIsometry_mono Q le_sup_left hxU)⟩
    exact ι_mem_range_map_inclIsometry Q (Submodule.mem_sup_right (Submodule.mem_span_singleton_self m))

omit [Invertible (2 : K)] in
theorem map_involute {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (f : Q₁ →qᵢ Q₂)
    (x : CliffordAlgebra Q₁) :
    CliffordAlgebra.map f (involute x) = involute (CliffordAlgebra.map f x) := by
  have : (CliffordAlgebra.map f).comp involute = involute.comp (CliffordAlgebra.map f) :=
    CliffordAlgebra.hom_ext (LinearMap.ext fun m => by simp)
  exact congrArg (fun φ : CliffordAlgebra Q₁ →ₐ[K] CliffordAlgebra Q₂ => φ x) this

/-- Evenness is reflected by an injective `C(f)`. -/
theorem mem_evenOdd_zero_of_map {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (f : Q₁ →qᵢ Q₂) (hf : Function.Injective (CliffordAlgebra.map f)) {x : CliffordAlgebra Q₁}
    (hx : CliffordAlgebra.map f x ∈ evenOdd Q₂ 0) : x ∈ evenOdd Q₁ 0 := by
  have hinv : involute x = x := hf (by rw [map_involute, involute_eq_of_mem_even hx])
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
    ((evenOdd_isCompl Q₁).sup_eq_top ▸ Submodule.mem_top : x ∈ evenOdd Q₁ 0 ⊔ evenOdd Q₁ 1)
  rw [map_add, involute_eq_of_mem_even ha, involute_eq_of_mem_odd hb] at hinv
  have h2 : (2 : K) • b = 0 := by
    have hb' : -b = b := add_left_cancel hinv
    rw [two_smul]
    calc b + b = -b + b := by rw [hb']
      _ = 0 := neg_add_cancel b
  have hb0 : b = 0 := by
    have := congrArg (fun y => (⅟2 : K) • y) h2
    simpa [smul_smul] using this
  rw [hb0, add_zero]; exact ha


end RestrictSubspace

section FlagRestrict

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V}

omit [Invertible (2 : K)] in
/-- `C(U)` is stable under `x ↦ ι(v) x − involute(x) ι(v)` for every `v ∈ V` (a contraction). -/
theorem ι_mul_sub_involute_mul_mem_range {U : Submodule K V} {x : CliffordAlgebra Q}
    (hx : x ∈ (CliffordAlgebra.map (inclIsometry Q U)).range) (v : V) :
    ι Q v * x - involute x * ι Q v ∈ (CliffordAlgebra.map (inclIsometry Q U)).range := by
  obtain ⟨y, rfl⟩ := (AlgHom.mem_range _).mp hx
  rw [ι_mul_sub_involute_mul, ← map_contractLeft]
  exact (AlgHom.mem_range _).mpr ⟨_, rfl⟩

/-- If `g^{±1} ∈ C(U)`, then `P(g)v − v ∈ U` for every `v ∈ V`. -/
theorem specP_sub_mem_of_mem_range {U : Submodule K V} {g : GSpin Q}
    (hg : ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
      (CliffordAlgebra.map (inclIsometry Q U)).range)
    (hgi : (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
      (CliffordAlgebra.map (inclIsometry Q U)).range)
    (v : V) : specP Q g v - v ∈ U := by
  set a : CliffordAlgebra Q := ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  set b : CliffordAlgebra Q :=
    (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  have hab : a * b = 1 := Units.mul_inv _
  have ha0 : a ∈ evenOdd Q 0 := by
    have := g.2.1
    rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at this
    exact this
  have hc := ι_mul_sub_involute_mul_mem_range hg v
  rw [involute_eq_of_mem_even ha0] at hc
  have e : ι Q (specP Q g v - v) = -((ι Q v * a - a * ι Q v) * b) := by
    rw [map_sub, ι_specP, sub_mul, mul_assoc (ι Q v), hab, mul_one]; abel
  have hmem : ι Q (specP Q g v - v) ∈ (CliffordAlgebra.map (inclIsometry Q U)).range := by
    rw [e]; exact neg_mem (mul_mem hc hgi)
  obtain ⟨y, hy⟩ := (AlgHom.mem_range _).mp hmem
  obtain ⟨u, hu, -⟩ := exists_eq_ι_of_map_eq_ι (inclIsometry Q U) Subtype.val_injective hy
  rw [← hu]; exact u.2

/-- If `g^{±1} ∈ C(U)`, then `g` is the image of some `g' ∈ GSpin(U)`, and `P(g') = P(g)|_U`. -/
theorem exists_gspin_restrict {U : Submodule K V} {g : GSpin Q}
    (hg : ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
      (CliffordAlgebra.map (inclIsometry Q U)).range)
    (hgi : (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
      (CliffordAlgebra.map (inclIsometry Q U)).range) :
    ∃ g' : GSpin (Q.comp U.subtype),
      CliffordAlgebra.map (inclIsometry Q U)
          ((g' : (CliffordAlgebra (Q.comp U.subtype))ˣ) : CliffordAlgebra (Q.comp U.subtype)) =
        ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∧
      ∀ u : U, (specP _ g' u : V) = specP Q g u := by
  have hf := map_inclIsometry_injective Q U
  obtain ⟨x, hx⟩ := (AlgHom.mem_range _).mp hg
  obtain ⟨y, hy⟩ := (AlgHom.mem_range _).mp hgi
  have hxy : x * y = 1 := hf (by rw [map_mul, hx, hy, map_one, Units.mul_inv])
  have hyx : y * x = 1 := hf (by rw [map_mul, hx, hy, map_one, Units.inv_mul])
  let u : (CliffordAlgebra (Q.comp U.subtype))ˣ := ⟨x, y, hxy, hyx⟩
  have hgi' : (((g⁻¹ : GSpin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
      (CliffordAlgebra.map (inclIsometry Q U)).range := by
    simpa only [Subgroup.coe_inv] using hgi
  have hgii : (((((g⁻¹ : GSpin Q) : (CliffordAlgebra Q)ˣ))⁻¹ : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q) ∈
      (CliffordAlgebra.map (inclIsometry Q U)).range := by
    simpa only [Subgroup.coe_inv, inv_inv] using hg
  have hPU : ∀ w : U, specP Q g w ∈ U := fun w => by
    simpa using add_mem (specP_sub_mem_of_mem_range hg hgi w) w.2
  have hPU' : ∀ w : U, specP Q g⁻¹ w ∈ U := fun w => by
    simpa using add_mem (specP_sub_mem_of_mem_range hgi' hgii w) w.2
  have hconj : ∀ w : U, x * ι _ w * y = ι _ ⟨specP Q g w, hPU w⟩ := fun w => hf (by
    rw [map_mul, map_mul, hx, hy, map_apply_ι, map_apply_ι]; exact (ι_specP g w).symm)
  have hconj' : ∀ w : U, y * ι _ w * x = ι _ ⟨specP Q g⁻¹ w, hPU' w⟩ := fun w => hf (by
    rw [map_mul, map_mul, hx, hy, map_apply_ι, map_apply_ι]
    have := ι_specP g⁻¹ w
    simp only [Subgroup.coe_inv, inv_inv] at this
    exact this.symm)
  have hmem : u ∈ GSpin (Q.comp U.subtype) := by
    refine ⟨?_, fun w => ⟨_, (hconj w).symm⟩, fun w => ⟨_, (hconj' w).symm⟩⟩
    rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
    refine mem_evenOdd_zero_of_map (inclIsometry Q U) hf ?_
    change CliffordAlgebra.map (inclIsometry Q U) x ∈ _
    have := g.2.1
    rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at this
    rwa [hx]
  refine ⟨⟨u, hmem⟩, hx, fun w => ?_⟩
  have h1 := ι_specP (Q := Q.comp U.subtype) ⟨u, hmem⟩ w
  have h2 : specP _ (⟨u, hmem⟩ : GSpin (Q.comp U.subtype)) w = ⟨specP Q g w, hPU w⟩ :=
    ι_injective _ (h1.trans (hconj w))
  rw [h2]

/-- The flag `Z_• ∩ U` of `(U, q|_U)`, when `U` meets every step of the flag. -/
def IsotropicFlag.restrict (F : IsotropicFlag Q) (U : Submodule K V)
    (hU : ∀ i : Fin F.len, ∃ z ∈ U, z ∈ F.sub i.succ ∧ z ∉ F.sub i.castSucc) :
    IsotropicFlag (Q.comp U.subtype) where
  len := F.len
  sub i := (F.sub i).comap U.subtype
  sub_zero := by rw [F.sub_zero, Submodule.comap_bot, Submodule.ker_subtype]
  strictMono := Fin.strictMono_iff_lt_succ.mpr fun i => by
    obtain ⟨z, hzU, hz1, hz0⟩ := hU i
    refine lt_of_le_of_ne (Submodule.comap_mono (F.strictMono.monotone
      (Fin.castSucc_lt_succ (i := i)).le)) fun h => hz0 ?_
    have : (⟨z, hzU⟩ : U) ∈ (F.sub i.succ).comap U.subtype := hz1
    rw [← h] at this
    exact this
  isotropic i u hu := F.isotropic i _ hu

omit [Invertible (2 : K)] in
/-- Some finite-dimensional subspace meets every step of the flag. -/
theorem IsotropicFlag.exists_fg_witness (F : IsotropicFlag Q) :
    ∃ Z : Submodule K V, Z.FG ∧
      ∀ i : Fin F.len, ∃ z ∈ Z, z ∈ F.sub i.succ ∧ z ∉ F.sub i.castSucc := by
  choose z hz1 hz0 using fun i : Fin F.len =>
    IsConcreteLE.exists_of_lt (F.strictMono (Fin.castSucc_lt_succ (i := i)))
  exact ⟨Submodule.span K (Set.range z), Submodule.fg_span (Set.finite_range z),
    fun i => ⟨z i, Submodule.subset_span ⟨i, rfl⟩, hz1 i, hz0 i⟩⟩

/-- For a finite-dimensional `U₁` and any `W`, orthogonality to `W` on `U₁` is tested by a
finite-dimensional `T ⊆ W`. -/
theorem exists_fg_orthogonal_test (Q : QuadraticForm K V) {U₁ : Submodule K V} (hU₁ : U₁.FG)
    (W : Submodule K V) : ∃ T : Submodule K V, T.FG ∧ T ≤ W ∧
      ∀ u ∈ U₁, u ∈ (bform Q).orthogonal T → u ∈ (bform Q).orthogonal W := by
  classical
  have := (Submodule.fg_iff_finiteDimensional U₁).mp hU₁
  have hex : ∃ n, ∃ T : Submodule K V, T.FG ∧ T ≤ W ∧
      finrank K ↥(U₁ ⊓ (bform Q).orthogonal T) = n :=
    ⟨_, ⊥, Submodule.fg_bot, bot_le, rfl⟩
  obtain ⟨T, hT, hTW, hn⟩ := Nat.find_spec hex
  refine ⟨T, hT, hTW, fun u hu huT w hw => ?_⟩
  have hle : U₁ ⊓ (bform Q).orthogonal (T ⊔ K ∙ w) ≤ U₁ ⊓ (bform Q).orthogonal T :=
    inf_le_inf_left _ (LinearMap.BilinForm.orthogonal_le le_sup_left)
  have hmin := Nat.find_min' hex ⟨T ⊔ K ∙ w, hT.sup (Submodule.fg_span_singleton w),
    sup_le hTW ((Submodule.span_singleton_le_iff_mem _ _).mpr hw), rfl⟩
  have heq := Submodule.eq_of_le_of_finrank_le hle (hn ▸ hmin)
  have : u ∈ U₁ ⊓ (bform Q).orthogonal (T ⊔ K ∙ w) := heq ▸ ⟨hu, huT⟩
  exact this.2 w (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))

/-- Restricting `K^×·N_F` to `U`: if `U` meets every step of the flag and orthogonality to
`Z_len` on `U` is tested inside `U`, then `g' ∈ K^×·N_{F ∩ U}`. -/
theorem mem_flagUnipSO_restrict {F : IsotropicFlag Q} {U : Submodule K V} [FiniteDimensional K U]
    (hU : ∀ i : Fin F.len, ∃ z ∈ U, z ∈ F.sub i.succ ∧ z ∉ F.sub i.castSucc)
    (hsep : ∀ u ∈ U, (∀ z ∈ U, z ∈ F.top → bform Q z u = 0) → u ∈ (bform Q).orthogonal F.top)
    {g : GSpin Q} (hg : g ∈ flagUnipSO F) {g' : GSpin (Q.comp U.subtype)}
    (hP : ∀ u : U, (specP _ g' u : V) = specP Q g u) :
    g' ∈ flagUnipSO (F.restrict U hU) := by
  obtain ⟨hg0, hg1, hg2⟩ := hg
  refine ⟨mem_flagStab_iff.mpr fun i u hu => ?_, fun i u hu => ?_, fun u hu => ?_⟩
  · change (specP _ g' u : V) ∈ F.sub i
    rw [hP]; exact flagStab_mapsTo hg0 i hu
  · change ((specP _ g' u - u : U) : V) ∈ F.sub i.castSucc
    rw [Submodule.coe_sub, hP]; exact hg1 i u hu
  · change ((specP _ g' u - u : U) : V) ∈ F.top
    rw [Submodule.coe_sub, hP]
    refine hg2 u (hsep u u.2 fun z hzU hz => ?_)
    have := (LinearMap.BilinForm.mem_orthogonal_iff.mp hu) ⟨z, hzU⟩ hz
    simpa [bform, QuadraticMap.associated_comp] using this

end FlagRestrict

section Flags

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- For `g, h` in the preimage `K^× · N_F` of `N_F^{SO}`, if `g − 1` and `h − 1` are nilpotent in
`C(V)` then so is `gh − 1` (Thesis §5.2: `N` is the unipotent radical of `P`; the preimage is
`K^× × N_F`, unipotent groups lifting uniquely).  The finite-dimensional case is
`isNilpotent_mul_sub_one_of_flagUnipSO_of_finite`; in general, `g^{±1}, h^{±1}` lie in `C(U)` for a
finite-dimensional `U ⊆ V`, enlarged so that it meets every step of the flag and tests
orthogonality to `Z_len`, and the finite case applies to `(U, q|_U)` and the flag `Z_• ∩ U`. -/
theorem isNilpotent_mul_sub_one_of_flagUnipSO {Q : QuadraticForm K V} {F : IsotropicFlag Q}
    {g h : GSpin Q} (hg : g ∈ flagUnipSO F) (hh : h ∈ flagUnipSO F)
    (hg' : IsNilpotent (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1))
    (hh' : IsNilpotent (((h : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1)) :
    IsNilpotent ((((g * h : GSpin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1) := by
  obtain ⟨U₁, h1, hU₁⟩ := exists_fg_mem_range_map Q ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  obtain ⟨U₂, h2, hU₂⟩ := exists_fg_mem_range_map Q
    (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  obtain ⟨U₃, h3, hU₃⟩ := exists_fg_mem_range_map Q ((h : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  obtain ⟨U₄, h4, hU₄⟩ := exists_fg_mem_range_map Q
    (((h : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  obtain ⟨Z, hZ, hZw⟩ := F.exists_fg_witness
  have hU₀ : (U₁ ⊔ U₂ ⊔ U₃ ⊔ U₄ ⊔ Z).FG := (((h1.sup h2).sup h3).sup h4).sup hZ
  obtain ⟨T, hT, hTW, hsep⟩ := exists_fg_orthogonal_test Q hU₀ F.top
  set U₀ := U₁ ⊔ U₂ ⊔ U₃ ⊔ U₄ ⊔ Z
  set U := U₀ ⊔ T
  have : FiniteDimensional K U := (Submodule.fg_iff_finiteDimensional U).mp (hU₀.sup hT)
  have hle : ∀ {U' : Submodule K V}, U' ≤ U₀ → U' ≤ U := fun h => h.trans le_sup_left
  have mono : ∀ {U' : Submodule K V}, U' ≤ U₀ → (CliffordAlgebra.map (inclIsometry Q U')).range ≤
      (CliffordAlgebra.map (inclIsometry Q U)).range := fun h =>
    range_map_inclIsometry_mono Q (hle h)
  have hgU := mono (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))) hU₁
  have hgiU := mono (le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))) hU₂
  have hhU := mono (le_sup_right.trans (le_sup_left.trans le_sup_left)) hU₃
  have hhiU := mono (le_sup_right.trans le_sup_left) hU₄
  have hwit : ∀ i : Fin F.len, ∃ z ∈ U, z ∈ F.sub i.succ ∧ z ∉ F.sub i.castSucc := fun i => by
    obtain ⟨z, hz, hz1, hz0⟩ := hZw i
    exact ⟨z, hle le_sup_right hz, hz1, hz0⟩
  have htop : ∀ {a b : V}, a ∈ F.top → b ∈ F.top → bform Q a b = 0 := fun ha hb =>
    bform_eq_zero_of_isTotallyIsotropic (F.isotropic _) ha hb
  have hsepU : ∀ u ∈ U, (∀ z ∈ U, z ∈ F.top → bform Q z u = 0) →
      u ∈ (bform Q).orthogonal F.top := by
    intro u hu hz
    obtain ⟨u₀, hu₀, t, ht, rfl⟩ := Submodule.mem_sup.mp (show u ∈ U₀ ⊔ T from hu)
    have hu₀T : u₀ ∈ (bform Q).orthogonal T := fun s hs => by
      have := hz s (Submodule.mem_sup_right hs) (hTW hs)
      rwa [map_add, htop (hTW hs) (hTW ht), add_zero] at this
    exact add_mem (hsep u₀ hu₀ hu₀T) (fun n hn => htop hn (hTW ht))
  obtain ⟨g₁, hg₁, hPg⟩ := exists_gspin_restrict hgU hgiU
  obtain ⟨h₁, hh₁, hPh⟩ := exists_gspin_restrict hhU hhiU
  have hinj := map_inclIsometry_injective Q U
  have hg₁n : IsNilpotent (((g₁ : (CliffordAlgebra (Q.comp U.subtype))ˣ) :
      CliffordAlgebra (Q.comp U.subtype)) - 1) := by
    rw [← IsNilpotent.map_iff hinj, map_sub, map_one, hg₁]; exact hg'
  have hh₁n : IsNilpotent (((h₁ : (CliffordAlgebra (Q.comp U.subtype))ˣ) :
      CliffordAlgebra (Q.comp U.subtype)) - 1) := by
    rw [← IsNilpotent.map_iff hinj, map_sub, map_one, hh₁]; exact hh'
  have key := (isNilpotent_mul_sub_one_of_flagUnipSO_of_finite
    (mem_flagUnipSO_restrict hwit hsepU hg hPg) (mem_flagUnipSO_restrict hwit hsepU hh hPh)
    hg₁n hh₁n).map (CliffordAlgebra.map (inclIsometry Q U))
  simp only [Subgroup.coe_mul, Units.val_mul, map_sub, map_one, map_mul, hg₁, hh₁] at key ⊢
  exact key

/-- The unipotent radical `N_F` of `P_F` (Thesis §5.2): `P(g)` stabilizes the flag, acts trivially
on the graded pieces `Z_i / Z_{i-1}` and on `Z_lenᗮ / Z_len` (hence, by duality, on all pieces of
the self-dual flag `Z_• ⊆ Z_•ᗮ`), and `g − 1` is nilpotent in `C(V)` (which removes the central
scalars).  Closure under products is `isNilpotent_mul_sub_one_of_flagUnipSO`. -/
def flagUnip {Q : QuadraticForm K V} (F : IsotropicFlag Q) : Subgroup (GSpin Q) where
  carrier := {g | g ∈ flagStab F ∧
    (∀ i : Fin F.len, ∀ v ∈ F.sub i.succ, specP Q g v - v ∈ F.sub i.castSucc) ∧
    (∀ v ∈ (bform Q).orthogonal F.top, specP Q g v - v ∈ F.top) ∧
    IsNilpotent (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1)}
  one_mem' := by
    refine ⟨(flagStab F).one_mem, fun i v _ => by simp, fun v _ => by simp, ?_⟩
    simp
  mul_mem' := by
    rintro g h ⟨hg0, hg1, hg2, hg3⟩ ⟨hh0, hh1, hh2, hh3⟩
    have hgh := (flagUnipSO F).mul_mem (show g ∈ flagUnipSO F from ⟨hg0, hg1, hg2⟩)
      (show h ∈ flagUnipSO F from ⟨hh0, hh1, hh2⟩)
    exact ⟨hgh.1, hgh.2.1, hgh.2.2, isNilpotent_mul_sub_one_of_flagUnipSO ⟨hg0, hg1, hg2⟩
      ⟨hh0, hh1, hh2⟩ hg3 hh3⟩
  inv_mem' := by
    rintro g ⟨hg0, hg1, hg2, hg3⟩
    have hgi := (flagUnipSO F).inv_mem (show g ∈ flagUnipSO F from ⟨hg0, hg1, hg2⟩)
    refine ⟨hgi.1, hgi.2.1, hgi.2.2, ?_⟩
    -- `g⁻¹ − 1 = −g⁻¹ (g − 1)`, and `g⁻¹` commutes with `g − 1`
    set a : CliffordAlgebra Q := ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
    set b : CliffordAlgebra Q := (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q)
    have hba : b * a = 1 := Units.inv_mul _
    have hab : a * b = 1 := Units.mul_inv _
    have : (((g⁻¹ : GSpin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1 = -(b * (a - 1)) := by
      rw [mul_sub, hba, mul_one]
      simp [b]
    rw [this]
    refine (Commute.isNilpotent_mul_left ?_ hg3).neg
    show b * (a - 1) = (a - 1) * b
    rw [mul_sub, sub_mul, hba, hab, mul_one, one_mul]

theorem flagUnip_le_flagUnipSO {Q : QuadraticForm K V} (F : IsotropicFlag Q) :
    flagUnip F ≤ flagUnipSO F := fun _ hg => ⟨hg.1, hg.2.1, hg.2.2.1⟩

/-- `N_F` is normalized by `P_F` (Thesis §5.2: `N` is the unipotent radical of `P`). -/
theorem flagUnip_conj {Q : QuadraticForm K V} {F : IsotropicFlag Q} {c n : GSpin Q}
    (hc : c ∈ flagStab F) (hn : n ∈ flagUnip F) : c * n * c⁻¹ ∈ flagUnip F := by
  obtain ⟨hn0, hn1, hn2, hn3⟩ := hn
  have hci := (flagStab F).inv_mem hc
  -- with `w = P(c⁻¹)v`: `P(c n c⁻¹)v - v = P(c)(P(n)w - w)`
  have key : ∀ v, specP Q (c * n * c⁻¹) v - v =
      specP Q c (specP Q n (specP Q c⁻¹ v) - specP Q c⁻¹ v) := fun v => by
    rw [specP_mul_apply, specP_mul_apply, map_sub, specP_inv_apply_apply]
  refine ⟨(flagStab F).mul_mem ((flagStab F).mul_mem hc hn0) hci, fun i v hv => ?_,
    fun v hv => ?_, ?_⟩
  · rw [key]
    exact flagStab_mapsTo hc _ (hn1 i _ (flagStab_mapsTo hci _ hv))
  · rw [key]
    exact flagStab_mapsTo hc _ (hn2 _ (flagStab_mapsTo_orthogonal hci hv))
  · set a : CliffordAlgebra Q := ((c : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
    set b : CliffordAlgebra Q := (((c : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q)
    have hba : b * a = 1 := Units.inv_mul _
    have hab : a * b = 1 := Units.mul_inv _
    have h : (((c * n * c⁻¹ : GSpin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1 =
        a * ((((n : GSpin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1) * b := by
      rw [mul_sub, sub_mul, mul_one, hab]
      simp [a, b]
    rw [h]
    obtain ⟨k, hk⟩ := hn3
    refine ⟨k, ?_⟩
    have hpow : ∀ x : CliffordAlgebra Q, ∀ m : ℕ, (a * x * b) ^ m = a * x ^ m * b := by
      intro x m
      induction m with
      | zero => simp [hab]
      | succ m ih =>
        rw [pow_succ, ih, pow_succ]
        calc a * x ^ m * b * (a * x * b) = a * x ^ m * (b * a) * x * b := by
              simp only [mul_assoc]
          _ = a * (x ^ m * x) * b := by rw [hba, mul_one, mul_assoc a]
    rw [hpow, hk, mul_zero, zero_mul]

theorem flagUnip_le_flagStab {Q : QuadraticForm K V} (F : IsotropicFlag Q) :
    flagUnip F ≤ flagStab F := fun _ hg => hg.1

section Closed

variable [TopologicalSpace K] [IsTopologicalRing K]

/-- Conjugation `g ↦ g x g⁻¹` is continuous on `GSpin(V)`. -/
theorem continuous_conj_GSpin [Module.Finite K V] (Q : QuadraticForm K V) (x : CliffordAlgebra Q) :
    Continuous fun g : GSpin Q => ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * x *
      (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) :=
  ((Units.continuous_val.comp continuous_subtype_val).mul continuous_const).mul
    (Units.continuous_coe_inv.comp continuous_subtype_val)

variable [T2Space K]

/-- `{g | P(g)v - w ∈ S}` is closed in `GSpin(V)`: via `ι`, it is the preimage of the closed
subspace `ι(S)` under the continuous map `g ↦ g ι(v) g⁻¹ - ι(w)`. -/
theorem isClosed_setOf_specP_sub_mem [Module.Finite K V] {Q : QuadraticForm K V} (v w : V)
    (S : Submodule K V) : IsClosed {g : GSpin Q | specP Q g v - w ∈ S} := by
  have h : {g : GSpin Q | specP Q g v - w ∈ S} =
      (fun g : GSpin Q => ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q v *
        (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - ι Q w) ⁻¹'
        (S.map (ι Q) : Set (CliffordAlgebra Q)) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, ← ι_specP, ← map_sub]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨u, hu, he⟩ => ι_injective Q he ▸ hu⟩
  rw [h]
  exact (isClosed_submodule_of_moduleTopology _).preimage
    ((continuous_conj_GSpin Q _).sub continuous_const)

/-- The parabolic subgroup `P_F(K)` is closed in `GSpin(V)(K)` (Thesis §5.1.2). -/
theorem isClosed_flagStab [Module.Finite K V] {Q : QuadraticForm K V} (F : IsotropicFlag Q) :
    IsClosed (flagStab F : Set (GSpin Q)) := by
  have h : (flagStab F : Set (GSpin Q)) =
      ⋂ i, ⋂ v ∈ F.sub i, {g : GSpin Q | specP Q g v ∈ F.sub i} := by
    ext g
    simp only [SetLike.mem_coe, mem_flagStab_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [h]
  exact isClosed_iInter fun i => isClosed_biInter fun v _ => by
    simpa using isClosed_setOf_specP_sub_mem (Q := Q) v 0 (F.sub i)

/-- The unipotent radical `N_F(K)` is closed in `GSpin(V)(K)` (Thesis §5.1.2, §5.2).  This does
not use the open lemma `isNilpotent_mul_sub_one_of_flagUnipSO`. -/
theorem isClosed_flagUnip [Module.Finite K V] {Q : QuadraticForm K V} (F : IsotropicFlag Q) :
    IsClosed (flagUnip F : Set (GSpin Q)) := by
  have hnil : IsClosed {g : GSpin Q |
      IsNilpotent (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1)} := by
    have h0 : IsClosed ({0} : Set (CliffordAlgebra Q)) := by
      simpa using isClosed_submodule_of_moduleTopology (⊥ : Submodule K (CliffordAlgebra Q))
    have : {g : GSpin Q | IsNilpotent (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1)} =
        (fun g : GSpin Q => (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1) ^
          finrank K (CliffordAlgebra Q)) ⁻¹' {0} := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      exact isNilpotent_iff_pow_finrank (K := K) _
    rw [this]
    exact h0.preimage
      (((Units.continuous_val.comp continuous_subtype_val).sub continuous_const).pow _)
  have h : (flagUnip F : Set (GSpin Q)) = (flagStab F : Set (GSpin Q)) ∩
      ((⋂ i : Fin F.len, ⋂ v ∈ F.sub i.succ,
          {g : GSpin Q | specP Q g v - v ∈ F.sub i.castSucc}) ∩
      ((⋂ v ∈ (bform Q).orthogonal F.top, {g : GSpin Q | specP Q g v - v ∈ F.top}) ∩
      {g : GSpin Q | IsNilpotent (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1)})) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [h]
  exact (isClosed_flagStab F).inter ((isClosed_iInter fun i => isClosed_biInter fun v _ =>
    isClosed_setOf_specP_sub_mem _ _ _).inter ((isClosed_biInter fun v _ =>
    isClosed_setOf_specP_sub_mem _ _ _).inter hnil))

end Closed

end Flags

/-! ## GGP data and the GGP triple `(G, H, ξ)` -/

/-- The data of an admissible pair `(W, V)` with `V = W ⊕^⊥ Z`, `Z` split of dimension `2r+1`
with basis `z_{-r}, …, z_r`, `b(z_i,z_j) = ν δ_{i,-j}` (Thesis §5.2).
`W = K^m` with the form `QW`. -/
structure GGPData (K : Type*) [Field K] [Invertible (2 : K)] where
  m : ℕ
  QW : QuadraticForm K (Fin m → K)
  nondeg : IsNondeg QW
  r : ℕ
  ν : Kˣ

namespace GGPData

variable {K : Type*} [Field K] [Invertible (2 : K)] (d : GGPData K)

/-- The space `Z` (Thesis (5.2.1)). -/
abbrev Z : Type _ := Fin (2 * d.r + 1) → K

/-- The form on `Z`. -/
abbrev QZ : QuadraticForm K d.Z := splitOddForm d.r (d.ν : K)

/-- `V = W ⊕^⊥ Z` (Thesis §5.2). -/
abbrev V : Type _ := (Fin d.m → K) × (Fin (2 * d.r + 1) → K)

/-- The form on `V = W ⊕^⊥ Z`. -/
abbrev QV : QuadraticForm K d.V := d.QW.prod d.QZ

/-- The ambient algebra `C(W) × C(V)` of `G = GSpin(W) × GSpin(V)`. -/
abbrev ambient : Type _ := CliffordAlgebra d.QW × CliffordAlgebra d.QV

/-- `G = GSpin(W) × GSpin(V)` (Thesis §5.2), as a subgroup of `(C(W) × C(V))^×`. -/
def G : Subgroup d.ambientˣ :=
  ((GSpin d.QW).prod (GSpin d.QV)).comap (MulEquiv.prodUnits).toMonoidHom

/-- First projection `G → GSpin(W)`. -/
def fst : d.G →* GSpin d.QW :=
  (((MonoidHom.fst _ _).comp (MulEquiv.prodUnits).toMonoidHom).comp d.G.subtype).codRestrict _
    (fun g => (Subgroup.mem_prod.mp g.2).1)

/-- Second projection `G → GSpin(V)`. -/
def snd : d.G →* GSpin d.QV :=
  (((MonoidHom.snd _ _).comp (MulEquiv.prodUnits).toMonoidHom).comp d.G.subtype).codRestrict _
    (fun g => (Subgroup.mem_prod.mp g.2).2)

/-- Pairing `GSpin(W) × GSpin(V) → G`. -/
def pair : GSpin d.QW × GSpin d.QV →* d.G :=
  (((MulEquiv.prodUnits).symm.toMonoidHom).comp
    (((GSpin d.QW).subtype).prodMap ((GSpin d.QV).subtype))).codRestrict _
    (fun p => by
      show _ ∈ ((GSpin d.QW).prod (GSpin d.QV))
      simp [Subgroup.mem_prod])

/-- The embedding `GSpin(W) ⊆ GSpin(V)` induced by `W ⊆ V` (Thesis Prop. 5.1.2.1). -/
def incl : GSpin d.QW →* GSpin d.QV :=
  GSpin.map (QuadraticMap.Isometry.inl d.QW d.QZ) d.nondeg

/-- The diagonal embedding `GSpin(W) → G`, `x ↦ (x, x)` (Thesis §5.2). -/
def diag : GSpin d.QW →* d.G :=
  d.pair.comp ((MonoidHom.id _).prod d.incl)

/-- `GSpin(V) → G`, `y ↦ (1, y)`. -/
def inr : GSpin d.QV →* d.G :=
  d.pair.comp (MonoidHom.inr _ _)

/-- The vector `z_k ∈ V` (`k ∈ {-r, …, r}`) (Thesis (5.2.1)). -/
def zV (k : ℤ) : d.V := (0, zvec d.r k)

/-- Vectors of `V` with `W`-component `0` and vanishing on the coordinates `z_k`, `k < t - r`
(helper for `flag`). -/
def coordVanish (t : ℕ) : Submodule K d.V where
  carrier := {u | u.1 = 0 ∧ ∀ n : Fin (2 * d.r + 1), (n : ℕ) < t → u.2 n = 0}
  add_mem' := fun ha hb => ⟨by simp [ha.1, hb.1], fun n hn => by simp [ha.2 n hn, hb.2 n hn]⟩
  zero_mem' := ⟨rfl, fun _ _ => rfl⟩
  smul_mem' := fun c _ ha => ⟨by simp [ha.1], fun n hn => by simp [ha.2 n hn]⟩

theorem coordVanish_anti {t t' : ℕ} (h : t ≤ t') : d.coordVanish t' ≤ d.coordVanish t :=
  fun _ hu => ⟨hu.1, fun n hn => hu.2 n (lt_of_lt_of_le hn h)⟩

/-- `⟨z_r, …, z_{r-m+1}⟩` lives on the last `m` coordinates. -/
theorem span_flag_le (m : ℕ) :
    Submodule.span K (Set.range fun j : Fin m => d.zV ((d.r : ℤ) - (j : ℕ))) ≤
      d.coordVanish (2 * d.r + 1 - m) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  refine ⟨rfl, fun n hn => ?_⟩
  simp only [zV, zvec]
  split_ifs with h
  · omega
  · rfl

/-- `q` vanishes on vectors supported on `z_1, …, z_r`. -/
theorem QV_eq_zero_of_mem_coordVanish {u : d.V} (hu : u ∈ d.coordVanish (d.r + 1)) :
    d.QV u = 0 := by
  obtain ⟨h1, h2⟩ := hu
  show d.QW u.1 + d.QZ u.2 = 0
  rw [h1, map_zero, zero_add]
  simp only [QZ, splitOddForm, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec, splitOddMatrix]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases ha : (a : ℕ) < d.r + 1
  · rw [h2 a ha, zero_mul]
  · rw [Finset.sum_eq_zero, mul_zero]
    intro b _
    by_cases hb : (b : ℕ) < d.r + 1
    · rw [h2 b hb, mul_zero]
    · split_ifs with h
      · omega
      · rw [zero_mul]

/-- The isotropic flag `⟨z_r⟩ ⊂ ⟨z_r, z_{r-1}⟩ ⊂ ⋯ ⊂ ⟨z_r, …, z_1⟩` of `V` (Thesis §5.2):
`Z_i = ⟨z_r, …, z_{r-i+1}⟩`. -/
def flag : IsotropicFlag d.QV where
  len := d.r
  sub i := Submodule.span K (Set.range fun j : Fin (i : ℕ) => d.zV ((d.r : ℤ) - (j : ℕ)))
  sub_zero := by simp
  strictMono := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    refine lt_of_le_of_ne (Submodule.span_mono ?_) fun h => ?_
    · rintro _ ⟨j, rfl⟩
      exact ⟨⟨j, by simp only [Fin.val_succ, Fin.val_castSucc] at j ⊢; omega⟩, rfl⟩
    · have hmem : d.zV ((d.r : ℤ) - (i : ℕ)) ∈ Submodule.span K
          (Set.range fun j : Fin ((i.succ : Fin (d.r + 1)) : ℕ) =>
            d.zV ((d.r : ℤ) - (j : ℕ))) :=
        Submodule.subset_span ⟨⟨i, by simp⟩, rfl⟩
      rw [← h] at hmem
      have h2 := (d.span_flag_le _ hmem).2 ⟨2 * d.r - i, by omega⟩ (by simp; omega)
      simp only [zV, zvec] at h2
      split_ifs at h2 with h3
      · exact one_ne_zero h2
      · omega
  isotropic := fun i u hu => d.QV_eq_zero_of_mem_coordVanish
    (d.coordVanish_anti (by omega) (d.span_flag_le _ hu))

/-- `N`, the unipotent radical of the stabilizer `P_V` of `d.flag` in `GSpin(V)`
(Thesis §5.2). -/
def N : Subgroup (GSpin d.QV) := flagUnip d.flag

/-- Elements of `G` are determined by their two components. -/
theorem G_ext {g h : d.G} (h1 : d.fst g = d.fst h) (h2 : d.snd g = d.snd h) : g = h := by
  apply Subtype.ext
  apply (MulEquiv.prodUnits : d.ambientˣ ≃* _).injective
  exact Prod.ext congr(($h1 : (CliffordAlgebra d.QW)ˣ)) congr(($h2 : (CliffordAlgebra d.QV)ˣ))

/-- `GSpin(W)` acts trivially on `Z` (Thesis §5.2): even elements of `C(W)` commute with
`Z = Wᗮ` in `C(V)`. -/
theorem specP_incl_inr (a : GSpin d.QW) (z : d.Z) :
    specP d.QV (d.incl a) (0, z) = (0, z) := by
  apply ι_injective d.QV
  have hu : ∀ w, QuadraticMap.polar d.QV (QuadraticMap.Isometry.inl d.QW d.QZ w) (0, z) = 0 :=
    fun w => by simp
  have h0 : ((a : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) ∈ evenOdd d.QW 0 := by
    rw [← even_toSubmodule]; exact a.2.1
  have e2 : ((((d.incl a : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ)⁻¹ : (CliffordAlgebra d.QV)ˣ) :
      CliffordAlgebra d.QV) = CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
        (((a⁻¹ : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) := by
    rw [← Subgroup.coe_inv, ← map_inv]; rfl
  rw [ι_specP, e2, incl, GSpin.coe_map, map_even_commute_ι _ h0 hu, mul_assoc, ← map_mul]
  rw [show ((a : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) *
      (((a⁻¹ : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) = 1 by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl, map_one, mul_one]

/-- `GSpin(W) ⊆ P_V`: it fixes the flag `Z_•` pointwise. -/
theorem incl_mem_flagStab (a : GSpin d.QW) : d.incl a ∈ flagStab d.flag := by
  intro i
  have fix : ∀ v ∈ d.flag.sub i, specP d.QV (d.incl a) v = v := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => specP d.QV (d.incl a) v = v) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨j, rfl⟩
      exact d.specP_incl_inr a _
    · simp
    · intro x y _ _ hx hy; rw [map_add, hx, hy]
    · intro c x _ hx; rw [map_smul, hx]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show specP d.QV (d.incl a) y ∈ _
    rw [fix y hy]; exact hy
  · intro hx
    exact ⟨x, hx, fix x hx⟩

/-- For `g = (a, b) ∈ G`, the element `n = a⁻¹ b ∈ GSpin(V)` (with `a` embedded in `GSpin(V)`);
`g ∈ H` iff `n ∈ N`, and then `g = diag(a) · (1, n)`. -/
def nPart (g : d.G) : GSpin d.QV := (d.incl (d.fst g))⁻¹ * d.snd g

/-- `H = GSpin(W) ⋉ N ⊆ G` (Thesis §5.2): the pairs `(a, a n)` with `n ∈ N`.
Closure under products uses that `GSpin(W)` normalizes `N`. -/
def H : Subgroup d.G where
  carrier := {g | d.nPart g ∈ d.N}
  one_mem' := by simp [nPart]
  mul_mem' := by
    intro g h hg hh
    have e : d.nPart (g * h) =
        (d.incl (d.fst h))⁻¹ * d.nPart g * ((d.incl (d.fst h))⁻¹)⁻¹ * d.nPart h := by
      simp only [nPart, map_mul, mul_inv_rev, inv_inv]
      group
    show d.nPart (g * h) ∈ d.N
    rw [e]
    exact d.N.mul_mem (flagUnip_conj ((flagStab _).inv_mem (d.incl_mem_flagStab _)) hg) hh
  inv_mem' := by
    intro g hg
    have e : d.nPart g⁻¹ = d.incl (d.fst g) * (d.nPart g)⁻¹ * (d.incl (d.fst g))⁻¹ := by
      simp only [nPart, map_inv, mul_inv_rev, inv_inv]
      group
    show d.nPart g⁻¹ ∈ d.N
    rw [e]
    exact flagUnip_conj (d.incl_mem_flagStab _) (d.N.inv_mem hg)

/-- `H` is generated by the diagonal `GSpin(W)` and `1 × N` (Thesis §5.2). -/
theorem H_eq_sup : d.H = d.diag.range ⊔ d.N.map d.inr := by
  apply le_antisymm
  · intro g hg
    have e : g = d.diag (d.fst g) * d.inr (d.nPart g) := by
      apply d.G_ext
      · simp [diag, inr, fst, pair]
      · simp only [map_mul]
        show d.snd g = d.incl (d.fst g) * (d.incl (d.fst g)⁻¹ * d.snd g)
        rw [map_inv, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, rfl⟩)
      (Subgroup.mem_sup_right ⟨_, hg, rfl⟩)
  · refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      show d.nPart _ ∈ d.N
      have : d.nPart (d.diag a) = 1 := by
        show (d.incl a)⁻¹ * d.incl a = 1
        exact inv_mul_cancel _
      rw [this]; exact d.N.one_mem
    · rintro _ ⟨n, hn, rfl⟩
      show d.nPart _ ∈ d.N
      have : d.nPart (d.inr n) = n := by
        show (d.incl 1)⁻¹ * n = n
        rw [map_one, inv_one, one_mul]
      rw [this]; exact hn

theorem bform_QV_zV (k l : ℤ) :
    bform d.QV (d.zV k) (d.zV l) = bform d.QZ (zvec d.r k) (zvec d.r l) := by
  simp [zV]

/-- `z_{-i-1} ⊥ Z_m` for `m ≤ r - i - 1`. -/
theorem bform_zV_neg_flag (i : Fin d.r) (m : ℕ) (hm : m + i + 1 ≤ d.r) {v : d.V}
    (hv : v ∈ Submodule.span K (Set.range fun j : Fin m => d.zV ((d.r : ℤ) - (j : ℕ)))) :
    bform d.QV (d.zV (-(i : ℤ) - 1)) v = 0 := by
  have hle : Submodule.span K (Set.range fun j : Fin m => d.zV ((d.r : ℤ) - (j : ℕ))) ≤
      LinearMap.ker (bform d.QV (d.zV (-(i : ℤ) - 1))) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    rw [bform_QV_zV, bform_splitOddForm_zvec _ _ (by rw [abs_le]; omega)
      (by rw [abs_le]; omega)]
    split_ifs with h
    · omega
    · rfl
  exact hle hv

/-- For `n ∈ N` and `0 ≤ i < r`: `P(n) z_i − z_i ∈ Z_{r-i} = ⟨z_r, …, z_{i+1}⟩`. -/
theorem specP_zV_sub_mem (i : Fin d.r) {n : GSpin d.QV} (hn : n ∈ d.N) :
    specP d.QV n (d.zV (i : ℕ)) - d.zV (i : ℕ) ∈
      Submodule.span K (Set.range fun j : Fin (d.r - i) => d.zV ((d.r : ℤ) - (j : ℕ))) := by
  obtain ⟨-, hn1, hn2, -⟩ := hn
  have hlen : d.flag.len = d.r := rfl
  by_cases hi : (i : ℕ) = 0
  · -- `z_0 ∈ Z_rᗮ`
    have h0 : d.zV ((i : ℕ) : ℤ) ∈ (bform d.QV).orthogonal d.flag.top := by
      intro t ht
      change t ∈ Submodule.span K (Set.range fun j : Fin d.r => d.zV ((d.r : ℤ) - (j : ℕ))) at ht
      refine Submodule.span_induction (p := fun t _ => bform d.QV t (d.zV ((i : ℕ) : ℤ)) = 0)
        ?_ (by simp) (fun x y _ _ hx hy => by rw [map_add, LinearMap.add_apply, hx, hy, add_zero])
        (fun c x _ hx => by rw [map_smul, LinearMap.smul_apply, hx, smul_zero]) ht
      rintro _ ⟨j, rfl⟩
      have hj : (j : ℕ) < d.r := j.2
      rw [bform_QV_zV, bform_splitOddForm_zvec _ _ (by rw [abs_le]; omega)
        (by rw [abs_le]; omega)]
      split_ifs with h
      · omega
      · rfl
    have := hn2 _ h0
    rw [show d.r - (i : ℕ) = d.r by omega]
    exact this
  · have := hn1 ⟨d.r - i, by rw [hlen]; omega⟩ (d.zV ((i : ℕ) : ℤ)) (Submodule.subset_span
      ⟨⟨d.r - i, show d.r - (i : ℕ) < d.r - i + 1 by omega⟩, by simp only [zV]; congr 2; omega⟩)
    exact this

/-- The `i`-th summand of `λ` is additive on `N` (Thesis §5.2). -/
theorem lamTerm_mul (i : Fin d.r) {n n' : GSpin d.QV} (hn : n ∈ d.N) (hn' : n' ∈ d.N) :
    bform d.QV (d.zV (-(i : ℤ) - 1)) (specP d.QV (n * n') (d.zV (i : ℕ))) =
      bform d.QV (d.zV (-(i : ℤ) - 1)) (specP d.QV n (d.zV (i : ℕ))) +
        bform d.QV (d.zV (-(i : ℤ) - 1)) (specP d.QV n' (d.zV (i : ℕ))) := by
  set y := specP d.QV n' (d.zV (i : ℕ)) - d.zV (i : ℕ)
  have hy := d.specP_zV_sub_mem i hn'
  -- `P(n) y − y ∈ Z_{r-i-1} ⊥ z_{-i-1}`
  have hny : specP d.QV n y - y ∈
      Submodule.span K (Set.range fun j : Fin (d.r - i - 1) => d.zV ((d.r : ℤ) - (j : ℕ))) := by
    have := hn.2.1 ⟨d.r - i - 1, by change _ < d.r; omega⟩ y (by
      change y ∈ Submodule.span K
        (Set.range fun j : Fin (d.r - i - 1 + 1) => d.zV ((d.r : ℤ) - (j : ℕ)))
      rw [show d.r - (i : ℕ) - 1 + 1 = d.r - i by omega]
      exact hy)
    exact this
  have h0 : bform d.QV (d.zV (-(i : ℤ) - 1)) (d.zV (i : ℕ)) = 0 := by
    rw [bform_QV_zV, bform_splitOddForm_zvec _ _ (by rw [abs_le]; omega)
      (by rw [abs_le]; omega)]
    split_ifs with h
    · omega
    · rfl
  have h1 := d.bform_zV_neg_flag i (d.r - i - 1) (by omega) hny
  have e : specP d.QV (n * n') (d.zV (i : ℕ)) =
      specP d.QV n (d.zV (i : ℕ)) + (specP d.QV n y - y) +
        (specP d.QV n' (d.zV (i : ℕ)) - d.zV (i : ℕ)) := by
    rw [specP_mul_apply]
    simp only [y, map_sub]
    abel
  rw [e, map_add, map_add, h1, map_sub, h0]
  ring

/-- The summands of `λ` are invariant under conjugation by elements fixing `Z` pointwise
(e.g. `GSpin(W)`). -/
theorem lamTerm_conj (i : Fin d.r) (x : GSpin d.QV) (c : GSpin d.QV)
    (hc : ∀ z : d.Z, specP d.QV c (0, z) = (0, z)) :
    bform d.QV (d.zV (-(i : ℤ) - 1)) (specP d.QV (c * x * c⁻¹) (d.zV (i : ℕ))) =
      bform d.QV (d.zV (-(i : ℤ) - 1)) (specP d.QV x (d.zV (i : ℕ))) := by
  have hci : ∀ z : d.Z, specP d.QV c⁻¹ (0, z) = (0, z) := fun z => by
    conv_lhs => rw [← hc z]
    rw [← specP_mul_apply, inv_mul_cancel, map_one]; rfl
  simp only [specP_mul_apply, zV]
  rw [hci]
  conv_lhs => rw [← hc (zvec d.r (-(i : ℤ) - 1))]
  rw [bform_specP]

/-- `λ(h) = Σ_{i=0}^{r-1} b(z_{-i-1}, P(n) z_i)`, where `n = diag(h_W)⁻¹ h ∈ N`; it is trivial on
the diagonal `GSpin(W)` (Thesis §5.2). -/
def lam (h : d.H) : K :=
  ∑ i : Fin d.r, bform d.QV (d.zV (-(i : ℤ) - 1)) (specP d.QV (d.nPart h) (d.zV (i : ℕ)))

/-- `ξ(h) = ψ(λ(h))` (Thesis §5.2). -/
def xi (ψ : AddChar K Circle) (h : d.H) : ℂ := ((ψ (d.lam h) : Circle) : ℂ)

/-- `λ` is a homomorphism `H → G_a` (Thesis §5.2). -/
theorem lam_mul (h h' : d.H) : d.lam (h * h') = d.lam h + d.lam h' := by
  have e : d.nPart ((h : d.G) * h') = (d.incl (d.fst h'))⁻¹ * d.nPart h *
      ((d.incl (d.fst h'))⁻¹)⁻¹ * d.nPart h' := by
    simp only [nPart, map_mul, mul_inv_rev, inv_inv]
    group
  have hc : ∀ z : d.Z, specP d.QV (d.incl (d.fst h'))⁻¹ (0, z) = (0, z) := fun z => by
    rw [← map_inv]; exact d.specP_incl_inr _ z
  have hX : (d.incl (d.fst h'))⁻¹ * d.nPart h * ((d.incl (d.fst h'))⁻¹)⁻¹ ∈ d.N :=
    flagUnip_conj ((flagStab _).inv_mem (d.incl_mem_flagStab _)) h.2
  unfold lam
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ((h * h' : d.H) : d.G) = (h : d.G) * h' from rfl, e,
    d.lamTerm_mul i hX h'.2, d.lamTerm_conj i (d.nPart h) _ hc]



/-- `ξ` is a character of `H` (Thesis §5.2). -/
theorem xi_mul (ψ : AddChar K Circle) (h h' : d.H) : d.xi ψ (h * h') = d.xi ψ h * d.xi ψ h' := by
  simp [xi, lam_mul, AddChar.map_add_eq_mul]

/-- `V = W ⊕^⊥ Z` is nondegenerate (Thesis §5.2). -/
theorem nondeg_QV : IsNondeg d.QV :=
  isNondeg_prod d.nondeg (isNondeg_splitOddForm d.r d.ν.ne_zero)

/-- `G(K)` is closed in `(C(W) × C(V))^×`. -/
theorem isClosed_G [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] :
    IsClosed (d.G : Set d.ambientˣ) := by
  have hc : Continuous (MulEquiv.prodUnits : d.ambientˣ ≃* _) :=
    (Units.continuous_map continuous_fst).prodMk (Units.continuous_map continuous_snd)
  exact ((isClosed_GSpin d.QW).prod (isClosed_GSpin d.QV)).preimage hc

/-- `H(K)`, viewed in `(C(W) × C(V))^×`, is closed. -/
theorem isClosed_H [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] :
    IsClosed ((d.H.map d.G.subtype : Subgroup d.ambientˣ) : Set d.ambientˣ) := by
  classical
  -- the components `u_W`, `u_V` of `u`, and `n(u) = u_W⁻¹ u_V`, `n(u)⁻¹ = u_V⁻¹ u_W`
  let uW : d.ambientˣ → (CliffordAlgebra d.QW)ˣ := fun u => (MulEquiv.prodUnits u).1
  let uV : d.ambientˣ → (CliffordAlgebra d.QV)ˣ := fun u => (MulEquiv.prodUnits u).2
  let ιW := QuadraticMap.Isometry.inl d.QW d.QZ
  let M1 : d.ambientˣ → CliffordAlgebra d.QV := fun u =>
    CliffordAlgebra.map ιW (((uW u)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) *
      (uV u : CliffordAlgebra d.QV)
  let M2 : d.ambientˣ → CliffordAlgebra d.QV := fun u =>
    (((uV u)⁻¹ : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) *
      CliffordAlgebra.map ιW (uW u : CliffordAlgebra d.QW)
  let Φ : d.ambientˣ → d.V → d.V := fun u v => ιInv d.QV (M1 u * ι d.QV v * M2 u)
  have hW : Continuous uW := Units.continuous_map continuous_fst
  have hV : Continuous uV := Units.continuous_map continuous_snd
  have hmap : Continuous (CliffordAlgebra.map ιW) :=
    IsModuleTopology.continuous_of_linearMap (CliffordAlgebra.map ιW).toLinearMap
  have hM1 : Continuous M1 :=
    (hmap.comp (Units.continuous_coe_inv.comp hW)).mul (Units.continuous_val.comp hV)
  have hM2 : Continuous M2 :=
    (Units.continuous_coe_inv.comp hV).mul (hmap.comp (Units.continuous_val.comp hW))
  have hΦ : ∀ v, Continuous fun u => Φ u v := fun v =>
    (IsModuleTopology.continuous_of_linearMap (ιInv d.QV)).comp
      ((hM1.mul continuous_const).mul hM2)
  have hcl : ∀ S : Submodule K d.V, IsClosed (S : Set d.V) :=
    fun S => isClosed_submodule_of_moduleTopology S
  have hcl0 : IsClosed ({0} : Set (CliffordAlgebra d.QV)) := by
    simpa using isClosed_submodule_of_moduleTopology (⊥ : Submodule K (CliffordAlgebra d.QV))
  -- for `g ∈ G`, `n(g) = nPart g`
  have hn1 : ∀ g : d.G, (((d.nPart g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) :
      CliffordAlgebra d.QV) = M1 g := fun g => by
    simp only [nPart, Subgroup.coe_mul, Units.val_mul, ← map_inv, incl, GSpin.coe_map]
    rfl
  have hn2 : ∀ g : d.G, ((((d.nPart g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ))⁻¹ :
      (CliffordAlgebra d.QV)ˣ) = M2 g := fun g => by
    rw [← Subgroup.coe_inv]
    simp only [nPart, mul_inv_rev, inv_inv, Subgroup.coe_mul, Units.val_mul, incl, GSpin.coe_map]
    rfl
  have hspec : ∀ g : d.G, ∀ v, specP d.QV (d.nPart g) v = Φ g v := fun g v => by
    rw [specP_apply_eq, ← mul_assoc, hn1, hn2]
  -- the closed set
  let C : Set d.ambientˣ := (d.G : Set d.ambientˣ) ∩
    ((⋂ i, ⋂ v ∈ d.flag.sub i, (fun u => Φ u v) ⁻¹' (d.flag.sub i : Set d.V)) ∩
     (⋂ i : Fin d.flag.len, ⋂ v ∈ d.flag.sub i.succ,
        (fun u => Φ u v - v) ⁻¹' (d.flag.sub i.castSucc : Set d.V)) ∩
     (⋂ v ∈ (bform d.QV).orthogonal d.flag.top,
        (fun u => Φ u v - v) ⁻¹' (d.flag.top : Set d.V)) ∩
     ((fun u => (M1 u - 1) ^ finrank K (CliffordAlgebra d.QV)) ⁻¹' {0}))
  have hC : IsClosed C := by
    refine (d.isClosed_G).inter (IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_)
    · exact isClosed_iInter fun i => isClosed_biInter fun v _ => (hcl _).preimage (hΦ v)
    · exact isClosed_iInter fun i => isClosed_biInter fun v _ =>
        (hcl _).preimage ((hΦ v).sub continuous_const)
    · exact isClosed_biInter fun v _ => (hcl _).preimage ((hΦ v).sub continuous_const)
    · exact hcl0.preimage ((hM1.sub continuous_const).pow _)
  convert hC using 1
  ext u
  simp only [Subgroup.coe_map, Subgroup.coe_subtype, Set.mem_image, SetLike.mem_coe, C,
    Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hs, h1, h2, h3⟩ := hg
    rw [mem_flagStab_iff] at hs
    refine ⟨g.2, ⟨⟨⟨fun i v hv => ?_, fun i v hv => ?_⟩, fun v hv => ?_⟩, ?_⟩⟩
    · rw [← hspec]; exact hs i v hv
    · rw [← hspec]; exact h1 i v hv
    · rw [← hspec]; exact h2 v hv
    · rw [← hn1]; exact (isNilpotent_iff_pow_finrank (K := K) _).mp h3
  · rintro ⟨hu, ⟨⟨hs, h1⟩, h2⟩, h3⟩
    refine ⟨⟨u, hu⟩, ?_, rfl⟩
    show d.nPart ⟨u, hu⟩ ∈ d.N
    refine ⟨mem_flagStab_iff.mpr fun i v hv => ?_, fun i v hv => ?_, fun v hv => ?_, ?_⟩
    · rw [hspec]; exact hs i v hv
    · rw [hspec]; exact h1 i v hv
    · rw [hspec]; exact h2 v hv
    · rw [isNilpotent_iff_pow_finrank (K := K), hn1]; exact h3

/-- `fst ∘ pair = Prod.fst` (`rfl`). -/
theorem fst_pair (p : GSpin d.QW × GSpin d.QV) : d.fst (d.pair p) = p.1 := rfl

/-- `snd ∘ pair = Prod.snd` (`rfl`). -/
theorem snd_pair (p : GSpin d.QW × GSpin d.QV) : d.snd (d.pair p) = p.2 := rfl

/-- `A_G(K)`, the `K`-points of the maximal split central torus of `G = GSpin(W) × GSpin(V)`
(Thesis §2.1 "split component", §7.1): `A_{GSpin(W)} × A_{GSpin(V)}`, where
`A_{GSpin(U)}` is all of `GSpin(U)` for a hyperbolic plane `U` and the scalars otherwise
(`splitCentralGSpin`).  The pair of scalars alone would be too small when `W` or `V` is a
hyperbolic plane, a case the induction on `dim G` reaches. -/
def AG : Subgroup d.G :=
  ((splitCentralGSpin d.QW).prod (splitCentralGSpin d.QV)).map d.pair

/-- `A_{G,H}`: the diagonal central scalars `{(c, c)}`. -/
def AGH : Subgroup d.G :=
  (d.diag.comp (scalarGSpin d.QW)).range

/-- `GSpin(W)` acts on `W ⊆ V` through `P_W` (Thesis Prop. 5.1.2.1). -/
theorem specP_incl_inl (a : GSpin d.QW) (w : Fin d.m → K) :
    specP d.QV (d.incl a) (w, 0) = (specP d.QW a w, 0) := by
  apply ι_injective d.QV
  have e1 : (w, (0 : d.Z)) = QuadraticMap.Isometry.inl d.QW d.QZ w := rfl
  have e2 : ((specP d.QW a w, (0 : d.Z)) : d.V) =
      QuadraticMap.Isometry.inl d.QW d.QZ (specP d.QW a w) := rfl
  have e3 : ((((d.incl a : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ)⁻¹ : (CliffordAlgebra d.QV)ˣ) :
      CliffordAlgebra d.QV) = CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
        (((a⁻¹ : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) := by
    rw [← Subgroup.coe_inv, ← map_inv]; rfl
  rw [ι_specP, e3, e1, e2, ← CliffordAlgebra.map_apply_ι, ← CliffordAlgebra.map_apply_ι, ι_specP,
    incl, GSpin.coe_map, ← map_mul, ← map_mul]
  rfl

/-- `z₀ ⊥ Z_r`, the top of the flag. -/
theorem zV_zero_mem_orthogonal_top : d.zV 0 ∈ (bform d.QV).orthogonal d.flag.top := by
  intro t ht
  change t ∈ Submodule.span K (Set.range fun j : Fin d.r => d.zV ((d.r : ℤ) - (j : ℕ))) at ht
  refine Submodule.span_induction (p := fun t _ => bform d.QV t (d.zV 0) = 0)
    ?_ (by simp) (fun x y _ _ hx hy => by rw [map_add, LinearMap.add_apply, hx, hy, add_zero])
    (fun c x _ hx => by rw [map_smul, LinearMap.smul_apply, hx, smul_zero]) ht
  rintro _ ⟨j, rfl⟩
  have hj : (j : ℕ) < d.r := j.2
  rw [bform_QV_zV, bform_splitOddForm_zvec _ _ (by rw [abs_le]; omega) (by rw [abs_le]; omega)]
  split_ifs with h
  · omega
  · rfl

/-- `W ⊥ Z_r`. -/
theorem inl_mem_orthogonal_top (w : Fin d.m → K) :
    ((w, 0) : d.V) ∈ (bform d.QV).orthogonal d.flag.top := by
  intro t ht
  have ht1 : t.1 = 0 := (d.span_flag_le _ ht).1
  change bform d.QV t (w, 0) = 0
  rw [bform_prod, ht1]; simp

/-- `q(z₀) = ν`. -/
theorem QV_zV_zero : d.QV (d.zV 0) = d.ν := by
  rw [← QuadraticMap.associated_eq_self_apply K, ← bform, bform_QV_zV,
    bform_splitOddForm_zvec _ _ (by simp) (by simp)]
  simp

/-- `snd ∘ inr = id`. -/
theorem snd_inr (y : GSpin d.QV) : d.snd (d.inr y) = y := rfl

/-- The embedding `GSpin(W) → GSpin(V)` maps scalars to scalars. -/
theorem incl_scalarGSpin (c : Kˣ) : d.incl (scalarGSpin d.QW c) = scalarGSpin d.QV c := by
  apply Subtype.ext; apply Units.ext
  show ((d.incl (scalarGSpin d.QW c) : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ).val = _
  rw [incl, GSpin.coe_map]
  simp [scalarGSpin]

/-- `Z_{G,H} = Z_G ∩ H = A_{G,H}` is the diagonal `G_m`.
Proof: for `g = (a, b)` central with `n = a⁻¹ b ∈ N`: if `dim V ≥ 3`, `P(b)` is a scalar `c`
(`specP_eq_smul_of_mem_center`), and `P(n) z₀ − z₀ = (c − 1) z₀ ∈ Z_r` (isotropic) forces `c = 1`;
if `dim V ≤ 2` then `r = 0`, `dim W ≤ 1`, `P_W(a) = 1` by `det_specP`, and `N` acts trivially.
Then `P(n)` fixes `W` (as `P(n) w − w ∈ W ∩ Z_r = 0`), so `a`, `b` are scalars (`ker_specP`), and
`n − 1` nilpotent forces them equal.  This handles the even-dimensional volume element and the
abelian `GSpin(W)` (`dim W = 2`): neither needs a
separate argument, because only `b` is used to be central. -/
theorem center_inf_H_eq_AGH : Subgroup.center d.G ⊓ d.H = d.AGH := by
  apply le_antisymm
  · rintro g ⟨hgc, hgH⟩
    change g ∈ Subgroup.center d.G at hgc
    change g ∈ d.H at hgH
    rw [Subgroup.mem_center_iff] at hgc
    set a := d.fst g
    set b := d.snd g
    have hn : (d.incl a)⁻¹ * b ∈ d.N := hgH
    obtain ⟨-, -, hn2, hn3⟩ := hn
    have hbc : ∀ y : GSpin d.QV, b * y = y * b := by
      intro y
      have h2 := congrArg d.snd (hgc (d.inr y))
      rw [map_mul, map_mul, snd_inr] at h2
      exact h2.symm
    -- step 1: `P(b) = 1` and `P_W(a) = 1`
    have hPn : ∀ v, specP d.QV ((d.incl a)⁻¹ * b) v =
        specP d.QV (d.incl a⁻¹) (specP d.QV b v) := fun v => by
      rw [specP_mul_apply, map_inv d.incl a]
    have hPb_PW : specP d.QV b = 1 → specP d.QW a = 1 := by
      intro hb1
      have hinv : specP d.QW a⁻¹ = 1 := by
        refine LinearEquiv.ext fun w => ?_
        show specP d.QW a⁻¹ w = w
        have h := hn2 _ (d.inl_mem_orthogonal_top w)
        rw [hPn, hb1] at h
        change specP d.QV (d.incl a⁻¹) (w, 0) - (w, 0) ∈ _ at h
        rw [specP_incl_inl] at h
        have h1 := (d.span_flag_le _ h).1
        simp only [Prod.fst_sub] at h1
        exact sub_eq_zero.mp h1
      rw [map_inv, inv_eq_one] at hinv
      exact hinv
    have hboth : specP d.QV b = 1 ∧ specP d.QW a = 1 := by
      by_cases hV : 3 ≤ finrank K d.V
      · obtain ⟨c, hc⟩ := specP_eq_smul_of_mem_center hV d.nondeg_QV hbc
        have hz := hn2 _ d.zV_zero_mem_orthogonal_top
        rw [hPn, hc, map_smul] at hz
        have hz' : specP d.QV (d.incl a⁻¹) (d.zV 0) = d.zV 0 := d.specP_incl_inr _ _
        rw [hz', show c • d.zV 0 - d.zV 0 = (c - 1) • d.zV 0 by rw [sub_smul, one_smul]] at hz
        have hq := d.flag.isotropic (Fin.last _) _ hz
        rw [QuadraticMap.map_smul, QV_zV_zero, smul_eq_mul] at hq
        have hc1 : c = 1 := by
          have := (mul_eq_zero.mp hq).resolve_right (Units.ne_zero _)
          exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp (by rw [sq]; exact this))
        have hb1 : specP d.QV b = 1 := LinearEquiv.ext fun v => by
          rw [hc, hc1, one_smul]; rfl
        exact ⟨hb1, hPb_PW hb1⟩
      · have hr : d.r = 0 := by
          have : finrank K d.V = d.m + (2 * d.r + 1) := by simp
          omega
        have hm : finrank K (Fin d.m → K) ≤ 1 := by
          have : finrank K d.V = d.m + (2 * d.r + 1) := by simp
          rw [Module.finrank_fin_fun]; omega
        have ha1 : specP d.QW a = 1 := by
          have := eq_id_of_det_eq_one_of_finrank_le_one hm (det_specP a)
          exact LinearEquiv.ext fun w => congr($this w)
        -- `Z_r = 0`, so `P(n) = 1`
        have htop : d.flag.top = ⊥ := by
          change Submodule.span K (Set.range fun j : Fin d.r => d.zV ((d.r : ℤ) - (j : ℕ))) = ⊥
          rw [Submodule.span_eq_bot]
          rintro _ ⟨j, rfl⟩
          exact absurd j.2 (by omega)
        have hPn1 : ∀ v, specP d.QV ((d.incl a)⁻¹ * b) v = v := by
          intro v
          have h := hn2 v (by rw [htop]; intro t ht; rw [(Submodule.mem_bot K).mp ht]; simp)
          rw [htop, Submodule.mem_bot, sub_eq_zero] at h
          exact h
        have hb1 : specP d.QV b = 1 := by
          refine LinearEquiv.ext fun v => ?_
          show specP d.QV b v = v
          have hbe : b = d.incl a * ((d.incl a)⁻¹ * b) := by group
          rw [hbe, specP_mul_apply, hPn1]
          obtain ⟨w, z⟩ := v
          rw [show ((w, z) : d.V) = (w, 0) + (0, z) by simp, map_add, specP_incl_inl,
            d.specP_incl_inr, ha1]
          rfl
        exact ⟨hb1, ha1⟩
    obtain ⟨hb1, ha1⟩ := hboth
    -- step 2: both components are scalars, and equal
    obtain ⟨c, hc⟩ : b ∈ (scalarGSpin d.QV).range := by
      rw [← ker_specP d.nondeg_QV]; exact hb1
    obtain ⟨c', hc'⟩ : a ∈ (scalarGSpin d.QW).range := by
      rw [← ker_specP d.nondeg]; exact ha1
    have hcc : c = c' := by
      have e : ((((d.incl a)⁻¹ * b : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) :
          CliffordAlgebra d.QV) - 1 = algebraMap K _ (((c'⁻¹ * c : Kˣ) : K) - 1) := by
        rw [← hc, ← hc', incl_scalarGSpin, ← map_inv, ← map_mul, map_sub, map_one]
        rfl
      rw [e, IsNilpotent.map_iff (algebraMap K (CliffordAlgebra d.QV)).injective,
        isNilpotent_iff_eq_zero, sub_eq_zero, Units.val_eq_one, inv_mul_eq_one] at hn3
      exact hn3.symm
    refine ⟨c', d.G_ext ?_ ?_⟩
    · show scalarGSpin d.QW c' = a
      exact hc'
    · show d.incl (scalarGSpin d.QW c') = b
      rw [incl_scalarGSpin, ← hc, hcc]
  · rintro _ ⟨c, rfl⟩
    rw [MonoidHom.comp_apply]
    refine ⟨?_, ?_⟩
    · change _ ∈ Subgroup.center d.G
      rw [Subgroup.mem_center_iff]
      intro h
      have hx : (((d.diag (scalarGSpin d.QW c) : d.G) : d.ambientˣ) : d.ambient) =
          algebraMap K d.ambient c := by
        refine Prod.ext ?_ ?_
        · rfl
        · show (((d.incl (scalarGSpin d.QW c) : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) :
            CliffordAlgebra d.QV) = _
          rw [incl_scalarGSpin]; rfl
      apply Subtype.ext; apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, hx, Algebra.commutes]
    · show d.nPart _ ∈ d.N
      have : d.nPart (d.diag (scalarGSpin d.QW c)) = 1 := inv_mul_cancel _
      rw [this]; exact d.N.one_mem

/-- `A_{G,H} ⊆ A_G`. -/
theorem AGH_le_AG : d.AGH ≤ d.AG := by
  rintro _ ⟨c, rfl⟩
  refine ⟨(scalarGSpin d.QW c, scalarGSpin d.QV c),
    ⟨scalarGSpin_mem_splitCentralGSpin _ c, scalarGSpin_mem_splitCentralGSpin _ c⟩, ?_⟩
  apply d.G_ext
  · rfl
  · show scalarGSpin d.QV c = d.incl (scalarGSpin d.QW c)
    rw [incl_scalarGSpin]

/-- `A_G` is central in `G` (Thesis §2.1: `A_G ⊆ Z_G`). -/
theorem AG_le_center : d.AG ≤ Subgroup.center d.G := by
  rintro _ ⟨p, hp, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 := Subgroup.mem_center_iff.mp (splitCentralGSpin_le_center d.QW hp.1) (d.fst g)
  have h2 := Subgroup.mem_center_iff.mp (splitCentralGSpin_le_center d.QV hp.2) (d.snd g)
  apply d.G_ext
  · rw [map_mul, map_mul, fst_pair, h1]
  · rw [map_mul, map_mul, snd_pair, h2]

instance AG_normal : d.AG.Normal := Subgroup.normal_of_le_center d.AG_le_center

/-- `A_G ∩ H = A_{G,H}` (`A_{G,H} := A_G ∩ H = Z_{G,H}`), from `A_G ⊆ Z_G` and
`Z_G ∩ H = A_{G,H}` (`center_inf_H_eq_AGH`). -/
theorem AG_inf_H : d.AG ⊓ d.H = d.AGH := by
  apply le_antisymm
  · rw [← d.center_inf_H_eq_AGH]
    exact inf_le_inf_right _ d.AG_le_center
  · refine le_inf d.AGH_le_AG ?_
    rw [← d.center_inf_H_eq_AGH]; exact inf_le_right

/-- `dim GSpin(U) = n(n-1)/2 + 1` for `dim U = n` (`dim SO(n) + 1`, Thesis §5.1.2). -/
def dimGSpin (n : ℕ) : ℕ := n * (n - 1) / 2 + 1

/-- `dim G = dim GSpin(W) + dim GSpin(V)`, with `dim W = m`, `dim V = m + 2r + 1`: the measure of
the induction on `dim G` in the proof of Thesis Thm 7.2.1/7.2.2
(Thesis §7.2, before (HYP)). -/
def dimG : ℕ := dimGSpin d.m + dimGSpin (d.m + 2 * d.r + 1)

/-- `dimG` in closed form. -/
theorem dimG_eq : d.dimG =
    d.m * (d.m - 1) / 2 + 1 + (d.m + 2 * d.r + 1) * (d.m + 2 * d.r + 1 - 1) / 2 + 1 := by
  simp only [dimG, dimGSpin]; ring

/-- The Lie algebra `𝔤 = gspin(W) × gspin(V)` of `G` (Thesis §5.1.3). -/
def lie : LieSubalgebra K d.ambient where
  carrier := {X | X.1 ∈ gspin d.QW ∧ X.2 ∈ gspin d.QV}
  add_mem' := fun hX hY => ⟨add_mem hX.1 hY.1, add_mem hX.2 hY.2⟩
  zero_mem' := ⟨zero_mem _, zero_mem _⟩
  smul_mem' := fun c _ hX => ⟨(gspin d.QW).smul_mem c hX.1, (gspin d.QV).smul_mem c hX.2⟩
  lie_mem' := by
    rintro X Y hX hY
    refine ⟨?_, ?_⟩
    · have := (gspin d.QW).lie_mem hX.1 hY.1
      simpa [Ring.lie_def] using this
    · have := (gspin d.QV).lie_mem hX.2 hY.2
      simpa [Ring.lie_def] using this

/-- The `G`-invariant symmetric bilinear form on the ambient algebra used for `𝔤`: the trace form
`(X, Y) ↦ tr(L_{XY})` of `C(W) × C(V)` (`Algebra.traceForm` needs commutativity); the Thesis only
requires *some* `G`-invariant nondegenerate form (Thesis §2.4 / BP §1.6). -/
def bilin : LinearMap.BilinForm K d.ambient :=
  (LinearMap.mul K d.ambient).compr₂
    ((LinearMap.trace K d.ambient).comp (Algebra.lmul K d.ambient).toLinearMap)

theorem bilin_apply (X Y : d.ambient) :
    d.bilin X Y = LinearMap.trace K d.ambient (LinearMap.mulLeft K (X * Y)) :=
  rfl

/-- `bilin` is invariant under conjugation by `G`. -/
theorem bilin_conj (g : d.G) (X Y : d.ambient) :
    d.bilin ((g : d.ambientˣ) * X * ((g⁻¹ : d.G) : d.ambientˣ))
      ((g : d.ambientˣ) * Y * ((g⁻¹ : d.G) : d.ambientˣ)) = d.bilin X Y := by
  set a : d.ambient := ((g : d.ambientˣ) : d.ambient)
  set b : d.ambient := (((g⁻¹ : d.G) : d.ambientˣ) : d.ambient)
  have hba : b * a = 1 := by
    simp only [a, b, Subgroup.coe_inv, Units.inv_mul]
  have e : a * X * b * (a * Y * b) = a * (X * Y * b) := by
    calc a * X * b * (a * Y * b) = a * X * (b * a) * Y * b := by simp only [mul_assoc]
      _ = a * (X * Y * b) := by rw [hba, mul_one]; simp only [mul_assoc]
  rw [bilin_apply, bilin_apply, e, LinearMap.mulLeft_mul, ← Module.End.mul_eq_comp,
    LinearMap.trace_mul_comm, Module.End.mul_eq_comp, ← LinearMap.mulLeft_mul, mul_assoc, hba,
    mul_one]

omit [Invertible (2 : K)] in
/-- The trace of left multiplication on a product algebra. -/
theorem trace_mulLeft_prod {A B : Type*} [Ring A] [Algebra K A] [Module.Finite K A] [Ring B]
    [Algebra K B] [Module.Finite K B] (x : A × B) :
    LinearMap.trace K (A × B) (LinearMap.mulLeft K x) =
      LinearMap.trace K A (LinearMap.mulLeft K x.1) + LinearMap.trace K B (LinearMap.mulLeft K x.2) := by
  have : LinearMap.mulLeft K x = (LinearMap.mulLeft K x.1).prodMap (LinearMap.mulLeft K x.2) := by
    ext <;> simp
  rw [this, LinearMap.trace_prodMap']

/-- `bilin` is nondegenerate on `𝔤`. -/
theorem bilin_nondegenerate_lie (X : d.ambient) (hX : X ∈ d.lie)
    (h : ∀ Y ∈ d.lie, d.bilin X Y = 0) : X = 0 := by
  have h1 : X.1 = 0 := by
    refine trace_nondegenerate_gspin d.nondeg hX.1 fun Y hY => ?_
    have := h (Y, 0) ⟨hY, zero_mem _⟩
    rw [bilin_apply, trace_mulLeft_prod] at this
    simpa using this
  have h2 : X.2 = 0 := by
    refine trace_nondegenerate_gspin d.nondeg_QV hX.2 fun Y hY => ?_
    have := h (0, Y) ⟨zero_mem _, hY⟩
    rw [bilin_apply, trace_mulLeft_prod] at this
    simpa using this
  exact Prod.ext h1 h2


/-- `G` is quasi-split iff `W` and `V` are (Thesis §6.4). -/
def IsQuasiSplit : Prop := IsQuasiSplitQF d.QW ∧ IsQuasiSplitQF d.QV

end GGPData

/-! ## Inner twists -/

section InnerTwists

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- `2` is invertible in `K̄`. -/
instance invertibleTwoAlgebraicClosure : Invertible (2 : AlgebraicClosure K) :=
  (Invertible.map (algebraMap K (AlgebraicClosure K)) 2).copy 2 (map_ofNat _ 2).symm

/-- The basis of `K̄ ⊗ K^m` coming from the standard basis of `K^m`. -/
def bcBasis (K : Type*) [Field K] (m : ℕ) :
    Basis (Fin m) (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] (Fin m → K)) :=
  (Pi.basisFun K (Fin m)).baseChange (AlgebraicClosure K)

/-- The Galois conjugate `σf = (σ ⊗ 1) ∘ f ∘ (σ⁻¹ ⊗ 1)` of a `K̄`-linear endomorphism of
`K̄ ⊗ K^m`: in the rational basis its matrix is `σ` applied entrywise. -/
def galoisConj {m : ℕ} (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (f : (AlgebraicClosure K ⊗[K] (Fin m → K)) →ₗ[AlgebraicClosure K]
      (AlgebraicClosure K ⊗[K] (Fin m → K))) :
    (AlgebraicClosure K ⊗[K] (Fin m → K)) →ₗ[AlgebraicClosure K]
      (AlgebraicClosure K ⊗[K] (Fin m → K)) :=
  Matrix.toLin (bcBasis K m) (bcBasis K m)
    ((LinearMap.toMatrix (bcBasis K m) (bcBasis K m) f).map σ)

/-- An inner twist of `GSpin(W)`.  This differs from Thesis §6.2: the inner forms are indexed by
`H¹(F, SO(W))`, not `H¹(F, PGSpin(W))`.  A
quadratic space `W' = (K^m, Q')` of the same dimension and discriminant, with a *fixed*
`K̄`-isometry `φ : W_{K̄} ≃ W'_{K̄}` such that `φ⁻¹ ∘ σφ ∈ SO(W)(K̄)` for all `σ`.  The twist is
data: different `φ` can change stable conjugacy by an outer automorphism when `m` is even. -/
structure InnerTwist {m : ℕ} (Q : QuadraticForm K (Fin m → K)) where
  Q' : QuadraticForm K (Fin m → K)
  nondeg' : IsNondeg Q'
  sameDisc : SameDisc Q Q'
  φ : (Q.baseChange (AlgebraicClosure K)).IsometryEquiv (Q'.baseChange (AlgebraicClosure K))
  cocycle : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
    LinearMap.det (φ.toLinearEquiv.symm.toLinearMap ∘ₗ galoisConj σ φ.toLinearEquiv.toLinearMap)
      = 1

/-- The trivial inner twist (`α = 1`). -/
def InnerTwist.refl {m : ℕ} (Q : QuadraticForm K (Fin m → K)) (hQ : IsNondeg Q) :
    InnerTwist Q where
  Q' := Q
  nondeg' := hQ
  sameDisc := ⟨1, one_ne_zero, by simp⟩
  φ := QuadraticMap.IsometryEquiv.refl _
  cocycle σ := by
    have h1 : ((QuadraticMap.IsometryEquiv.refl
        (Q.baseChange (AlgebraicClosure K))).toLinearEquiv :
        (AlgebraicClosure K ⊗[K] (Fin m → K)) →ₗ[AlgebraicClosure K] (AlgebraicClosure K ⊗[K] (Fin m → K))) =
        LinearMap.id := rfl
    have h2 : ((QuadraticMap.IsometryEquiv.refl
        (Q.baseChange (AlgebraicClosure K))).toLinearEquiv.symm :
        (AlgebraicClosure K ⊗[K] (Fin m → K)) →ₗ[AlgebraicClosure K] (AlgebraicClosure K ⊗[K] (Fin m → K))) =
        LinearMap.id := rfl
    simp only [galoisConj, h1, h2, LinearMap.toMatrix_id, LinearMap.id_comp]
    rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.toLin_one, LinearMap.det_id]

/-- The trivial inner twist of a GGP datum. -/
abbrev GGPData.reflTwist (d : GGPData K) : InnerTwist d.QW := InnerTwist.refl d.QW d.nondeg

/-- The inner form `(W_α, V_α = W_α ⊕ Z)` of a GGP datum: same `r`, `ν`. -/
abbrev GGPData.twist (d : GGPData K) (τ : InnerTwist d.QW) : GGPData K where
  m := d.m
  QW := τ.Q'
  nondeg := τ.nondeg'
  r := d.r
  ν := d.ν

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The base-change embedding `C(Q) → C(Q_{K̄}) ≅ K̄ ⊗ C(Q)`
(`CliffordAlgebra.equivBaseChange`). -/
def bcHom (Q : QuadraticForm K V) :
    CliffordAlgebra Q →+* CliffordAlgebra (Q.baseChange (AlgebraicClosure K)) :=
  (CliffordAlgebra.ofBaseChange (AlgebraicClosure K) Q).toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := K) (A := AlgebraicClosure K)).toRingHom

/-- `C(Q)^× → C(Q_{K̄})^×`. -/
def bcUnits (Q : QuadraticForm K V) :
    (CliffordAlgebra Q)ˣ →* (CliffordAlgebra (Q.baseChange (AlgebraicClosure K)))ˣ :=
  Units.map (bcHom Q).toMonoidHom

/-- The Galois action `σ ⊗ 1` on `C(Q_{K̄}) ≅ K̄ ⊗ C(Q)`. -/
def galC (Q : QuadraticForm K V) (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    CliffordAlgebra (Q.baseChange (AlgebraicClosure K)) →+*
      CliffordAlgebra (Q.baseChange (AlgebraicClosure K)) :=
  (CliffordAlgebra.ofBaseChange (AlgebraicClosure K) Q).toRingHom.comp
    ((Algebra.TensorProduct.map (σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K)
      (AlgHom.id K (CliffordAlgebra Q))).toRingHom.comp
      (CliffordAlgebra.toBaseChange (AlgebraicClosure K) Q).toRingHom)

/-- `(Q₁ ⊕ Q₂)_{K̄} ≅ (Q₁)_{K̄} ⊕ (Q₂)_{K̄}`. -/
def prodBaseChange {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
    [Module K V₂] (Q₁ : QuadraticForm K V₁) (Q₂ : QuadraticForm K V₂) :
    (QuadraticForm.baseChange (AlgebraicClosure K) (Q₁.prod Q₂)).IsometryEquiv
      ((Q₁.baseChange (AlgebraicClosure K)).prod (Q₂.baseChange (AlgebraicClosure K))) where
  toLinearEquiv := TensorProduct.prodRight K (AlgebraicClosure K) (AlgebraicClosure K) V₁ V₂
  map_app' x := by
    have h := _root_.baseChange_ext (Q₁ :=
      ((Q₁.baseChange (AlgebraicClosure K)).prod (Q₂.baseChange (AlgebraicClosure K))).comp
        (TensorProduct.prodRight K (AlgebraicClosure K) (AlgebraicClosure K) V₁ V₂).toLinearMap)
      (Q₂ := QuadraticForm.baseChange (AlgebraicClosure K) (Q₁.prod Q₂)) (fun m => by
        simp [QuadraticForm.baseChange_tmul, add_smul])
    exact congr($h x)

/-- The extension `φ ⊕ id_Z : V_{K̄} ≃ V_{α,K̄}` of the twist. -/
def GGPData.twistV (d : GGPData K) (τ : InnerTwist d.QW) :
    (d.QV.baseChange (AlgebraicClosure K)).IsometryEquiv
      ((d.twist τ).QV.baseChange (AlgebraicClosure K)) :=
  (prodBaseChange d.QW d.QZ).trans
    ((τ.φ.prod (QuadraticMap.IsometryEquiv.refl _)).trans (prodBaseChange τ.Q' d.QZ).symm)

/-- `C(φ)` on units, for an isometry `φ` over `K̄` (`C(φ) : GSpin(V)_{K̄} ≃
GSpin(V')_{K̄}`). -/
def cliffUnits {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (φ : (Q₁.baseChange (AlgebraicClosure K)).IsometryEquiv
      (Q₂.baseChange (AlgebraicClosure K))) :
    (CliffordAlgebra (Q₁.baseChange (AlgebraicClosure K)))ˣ →*
      (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure K)))ˣ :=
  Units.map (CliffordAlgebra.map φ.toIsometry).toMonoidHom

/-- Stable conjugacy through `φ`: `∃ g ∈ GSpin(V')(K̄)` with `g · C(φ)(x) · g⁻¹ = y`
(Thesis §6.1 with `g` moved to the target via `ψ`). -/
def StablyConjVia {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
    [Module K V₂] {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (φ : (Q₁.baseChange (AlgebraicClosure K)).IsometryEquiv
      (Q₂.baseChange (AlgebraicClosure K)))
    (x : (CliffordAlgebra Q₁)ˣ) (y : (CliffordAlgebra Q₂)ˣ) : Prop :=
  ∃ g ∈ GSpin (Q₂.baseChange (AlgebraicClosure K)),
    g * cliffUnits φ (bcUnits Q₁ x) * g⁻¹ = bcUnits Q₂ y

/-- Strong stable conjugacy through `φ` (Thesis §6.1): stable conjugacy by some
`g` such that `Ad(g) ∘ C(φ)` restricted to the centralizer of `x` in `GSpin(V)(K̄)` commutes with
the Galois action, i.e. `Ad(g) ∘ ψ : G_x ≃ G'_y` is defined over `K`. -/
def StronglyStablyConjVia {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
    [Module K V₂] {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (φ : (Q₁.baseChange (AlgebraicClosure K)).IsometryEquiv
      (Q₂.baseChange (AlgebraicClosure K)))
    (x : (CliffordAlgebra Q₁)ˣ) (y : (CliffordAlgebra Q₂)ˣ) : Prop :=
  ∃ g ∈ GSpin (Q₂.baseChange (AlgebraicClosure K)),
    g * cliffUnits φ (bcUnits Q₁ x) * g⁻¹ = bcUnits Q₂ y ∧
    ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
    ∀ z ∈ GSpin (Q₁.baseChange (AlgebraicClosure K)),
      Commute z (bcUnits Q₁ x) →
      galC Q₂ σ ((g * cliffUnits φ z * g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
        (g : CliffordAlgebra _) * CliffordAlgebra.map φ.toIsometry (galC Q₁ σ (z : CliffordAlgebra _)) *
          ((g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _)

namespace GGPData

variable (d : GGPData K)

/-- Stable conjugacy between `G` and its inner form `G_α` through `ψ_α = C(φ) × C(φ ⊕ id_Z)`,
componentwise. -/
def StablyConjG (τ : InnerTwist d.QW) (x : d.G) (y : (d.twist τ).G) : Prop :=
  StablyConjVia τ.φ (d.fst x : (CliffordAlgebra d.QW)ˣ)
      ((d.twist τ).fst y : (CliffordAlgebra (d.twist τ).QW)ˣ) ∧
    StablyConjVia (d.twistV τ) (d.snd x : (CliffordAlgebra d.QV)ˣ)
      ((d.twist τ).snd y : (CliffordAlgebra (d.twist τ).QV)ˣ)

/-- Stable conjugacy within `G` (`τ` trivial): conjugacy over `K̄`, componentwise. -/
def StablyConj (x y : d.G) : Prop :=
  StablyConjVia (QuadraticMap.IsometryEquiv.refl _) (d.fst x : (CliffordAlgebra d.QW)ˣ)
      (d.fst y : (CliffordAlgebra d.QW)ˣ) ∧
    StablyConjVia (QuadraticMap.IsometryEquiv.refl _) (d.snd x : (CliffordAlgebra d.QV)ˣ)
      (d.snd y : (CliffordAlgebra d.QV)ˣ)

/-- Strong stable conjugacy between `x ∈ G` and `y ∈ G_α` (Thesis §6.1). -/
def StronglyStablyConjG (τ : InnerTwist d.QW) (x : d.G) (y : (d.twist τ).G) : Prop :=
  StronglyStablyConjVia τ.φ (d.fst x : (CliffordAlgebra d.QW)ˣ)
      ((d.twist τ).fst y : (CliffordAlgebra (d.twist τ).QW)ˣ) ∧
    StronglyStablyConjVia (d.twistV τ) (d.snd x : (CliffordAlgebra d.QV)ˣ)
      ((d.twist τ).snd y : (CliffordAlgebra (d.twist τ).QV)ˣ)

/-- Strong stable conjugacy of `x ∈ GSpin(W)` and `y ∈ GSpin(W_α)`, both embedded diagonally in
`G`, `G_α` (Thesis §6.1, §6.6). -/
def StronglyStablyConjW (τ : InnerTwist d.QW) (x : GSpin d.QW) (y : GSpin (d.twist τ).QW) :
    Prop :=
  d.StronglyStablyConjG τ (d.diag x) ((d.twist τ).diag y)

end GGPData

end InnerTwists

/-! ## Whittaker data (Thesis §4.4) -/

section Whittaker

variable {K : Type*} [Field K] [Invertible (2 : K)]

namespace GGPData

variable (d : GGPData K)

/-- The Borel subgroup `B = P_{F_W} × P_{F_V}` of `G` attached to full isotropic flags. -/
def whittB (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) : Subgroup d.G :=
  (flagStab FW).comap d.fst ⊓ (flagStab FV).comap d.snd

/-- Its unipotent radical `U_B = N_{F_W} × N_{F_V}`. -/
def whittU (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) : Subgroup d.G :=
  (flagUnip FW).comap d.fst ⊓ (flagUnip FV).comap d.snd

/-- `P_{F_W} × P_{F_V}` is a *proper* parabolic subgroup of `G`: it is not all of `G`
(Thesis §4.5: "proper parabolic"; §5.1.2: every parabolic subgroup of `G` is a product of flag
stabilizers). This is the thesis's definition verbatim. A nonempty flag does *not* suffice: when
`W` (or `V`) is a hyperbolic plane, `GSpin` of it is a torus and stabilizes each of its two
isotropic lines, so a one-line flag there has stabilizer everything and trivial unipotent radical.
Conversely a proper pair has a nonempty flag (`IsProperFlagPair.len_pos`). -/
def IsProperFlagPair (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) : Prop :=
  d.whittB FW FV ≠ ⊤

/-- The stabilizer of an empty flag (`len = 0`, the flag `0 = Z₀`) is all of `GSpin`. -/
theorem _root_.GSpinGGP.flagStab_eq_top_of_len_eq_zero {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (F : IsotropicFlag Q) (h : F.len = 0) : flagStab F = ⊤ := by
  ext g
  simp only [Subgroup.mem_top, iff_true]
  intro i
  have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
  subst hi
  rw [F.sub_zero, Submodule.map_bot]

/-- A proper flag pair has a nonempty flag (the converse fails for hyperbolic planes). -/
theorem IsProperFlagPair.len_pos {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV}
    (h : d.IsProperFlagPair FW FV) : 0 < FW.len ∨ 0 < FV.len := by
  rcases Nat.eq_zero_or_pos FW.len with hW | hW
  · rcases Nat.eq_zero_or_pos FV.len with hV | hV
    · refine absurd ?_ h
      rw [whittB, flagStab_eq_top_of_len_eq_zero FW hW, flagStab_eq_top_of_len_eq_zero FV hV,
        Subgroup.comap_top, Subgroup.comap_top, inf_top_eq]
    · exact Or.inr hV
  · exact Or.inl hW

section Closed

variable [TopologicalSpace K]

/-- The projection `G → GSpin(W)` is continuous. -/
theorem continuous_fst : Continuous d.fst :=
  continuous_induced_rng.2 ((Units.continuous_map _root_.continuous_fst).comp continuous_subtype_val)

/-- The projection `G → GSpin(V)` is continuous. -/
theorem continuous_snd : Continuous d.snd :=
  continuous_induced_rng.2 ((Units.continuous_map _root_.continuous_snd).comp continuous_subtype_val)

variable [IsTopologicalRing K] [T2Space K]

/-- The parabolic subgroup `P = P_{F_W} × P_{F_V}` is closed in `G(K)` (Thesis §5.1.2). -/
theorem isClosed_whittB (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) :
    IsClosed (d.whittB FW FV : Set ↥d.G) :=
  ((isClosed_flagStab FW).preimage d.continuous_fst).inter
    ((isClosed_flagStab FV).preimage d.continuous_snd)

/-- Its unipotent radical `U = N_{F_W} × N_{F_V}` is closed in `G(K)` (Thesis §5.1.2). -/
theorem isClosed_whittU (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) :
    IsClosed (d.whittU FW FV : Set ↥d.G) :=
  ((isClosed_flagUnip FW).preimage d.continuous_fst).inter
    ((isClosed_flagUnip FV).preimage d.continuous_snd)

end Closed

end GGPData

/-- A Whittaker datum for `G` (Thesis §4.4): a Borel subgroup `B` (the
stabilizer of full maximal isotropic flags of `W` and `V`) with unipotent radical `U`, and a
continuous unitary character `χ` of `U(K)` which is *generic*: its stabilizer in `B(K)` is
`Z_G(K) U(K)`.  (The thesis takes `G(K)`-conjugacy classes of such pairs.) -/
structure WhittakerDatum [TopologicalSpace K] (d : GGPData K) where
  flagW : IsotropicFlag d.QW
  flagV : IsotropicFlag d.QV
  fullW : flagW.IsFull
  fullV : flagV.IsFull
  χ : d.whittU flagW flagV → ℂ
  χ_one : χ 1 = 1
  χ_mul : ∀ u v, χ (u * v) = χ u * χ v
  χ_norm : ∀ u, ‖χ u‖ = 1
  χ_cont : Continuous χ
  generic : ∀ b ∈ d.whittB flagW flagV,
    ((∀ u u' : d.whittU flagW flagV, b * (u : d.G) * b⁻¹ = u' → χ u' = χ u) ↔
      ∃ z ∈ Subgroup.center d.G, ∃ u ∈ d.whittU flagW flagV, b = z * u)

/-- The unipotent subgroup `U` of a Whittaker datum. -/
abbrev WhittakerDatum.U [TopologicalSpace K] {d : GGPData K} (w : WhittakerDatum d) :
    Subgroup d.G :=
  d.whittU w.flagW w.flagV

end Whittaker

/-! ## The central character `χ` of `A_G(F)` (Thesis §7.1) -/

section CentralChar

variable {K : Type*} [Field K] [Invertible (2 : K)] [TopologicalSpace K]

/-- A continuous unitary character `χ : A_G(F) → 𝕊¹` trivial on `A_{G,H}(F)` (Thesis §7.1).
Fixed throughout the trace formula. -/
@[ext]
structure CentralCharOn (d : GGPData K) where
  /-- the character `χ` of `A_G(F)` -/
  toHom : ↥d.AG →* Circle
  continuous : Continuous toHom
  /-- `χ` is trivial on `A_{G,H}(F) ⊆ A_G(F)` -/
  trivial_AGH : ∀ a (ha : a ∈ d.AGH), toHom ⟨a, d.AGH_le_AG ha⟩ = 1

namespace CentralCharOn

variable {d : GGPData K}

/-- The inverse character `χ⁻¹` (the test functions of the trace formula transform by `χ⁻¹`;
Thesis §7.1). -/
def inv (χ : CentralCharOn d) : CentralCharOn d where
  toHom := χ.toHom⁻¹
  continuous := continuous_inv.comp χ.continuous
  trivial_AGH a ha := by simp [χ.trivial_AGH a ha]

/-- The trivial character. -/
def one (d : GGPData K) : CentralCharOn d where
  toHom := 1
  continuous := continuous_const
  trivial_AGH _ _ := rfl

@[simp] theorem inv_toHom (χ : CentralCharOn d) : χ.inv.toHom = χ.toHom⁻¹ := rfl

@[simp] theorem inv_apply (χ : CentralCharOn d) (a : ↥d.AG) : χ.inv.toHom a = (χ.toHom a)⁻¹ := rfl

@[simp] theorem one_toHom : (one d).toHom = 1 := rfl

@[simp] theorem inv_inv (χ : CentralCharOn d) : χ.inv.inv = χ := by
  ext a; simp

@[simp] theorem one_inv : (one d).inv = one d := by
  ext a; simp

end CentralCharOn

end CentralChar

end GSpinGGP
