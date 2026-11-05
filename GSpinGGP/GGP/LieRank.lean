/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.SemisimpleRank
import GSpinGGP.Literature.NilpotentOrbits

/-!
# The rank of `gspin(V)`

For a nondegenerate quadratic space `V` of dimension `n` over a field of characteristic `0`,
`lieRank (gspin V) = ⌊n/2⌋ + 1` (`lieRank_gspin`).

The lower bound `le_lieRank_gspin` comes from `le_finrank_soCent`: `dim so(V)_N ≥ ⌊dim V/2⌋` for
every `N ∈ so(V)`, by Jantzen's bound over `F̄` (`jantzen_finrank_soCentMat_ge`) and the invariance
of `dim so(V)_N` under extension of scalars (`finrank_soCentMat_map`). For the upper bound we
build a skew `Z` with `dim so(V)_Z ≤ ⌊n/2⌋` (`exists_skew_finrank_soCent_le`): split off an anisotropic orthogonal plane
`P = ⟨a, b⟩`, take `Z = c J ⊕ Z'` with `J = wedge(a, b)` (so `J² = −q(a) q(b)` on `P`) and `Z'`
given by induction on `P^⊥`, and choose `c` so that `c² J²` is not an eigenvalue of `Z'²`. Then
`P` is an eigenspace of `Z²`, every element of `so(V)_Z` preserves it, and
`dim so(V)_Z = dim so(P)_Z + dim so(P^⊥)_{Z'} ≤ 1 + ⌊(n-2)/2⌋`. A lift of `Z` to `gspin(V)`
(`exists_mem_gspin_adV_eq`) has centralizer of dimension `dim so(V)_Z + 1`.

The last section describes centralizers in `𝔤 = gspin(W) × gspin(V)` factorwise
(`mem_lieCentralizer_lieCentralizer_lie`, `finrank_lieCentralizer_lieCentralizer_lie`).
-/

noncomputable section

open Module LinearMap CliffordAlgebra

namespace GSpinGGP

universe u

section LowerBound

variable {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [CharZero K] in
/-- **Transport of a skew endomorphism to the algebraic closure**: for `N` skew for `bform Q`
(`Q` nondegenerate), the matrices of `bform Q` and `N` in a basis, mapped to `K̄`, are an invertible
symmetric `Φ` and a `Φ`-skew `A` with `dim so(Φ)_A = dim so(V)_N` (`finrank_soCentMat_map`) and
`A^m = 0 ↔ N^m = 0`. -/
theorem exists_algebraicClosure_soCentMat {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    {N : Module.End K V} (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w)) :
    ∃ Φ A : Matrix (Fin (finrank K V)) (Fin (finrank K V)) (AlgebraicClosure K),
      Φ.transpose = Φ ∧ Φ.det ≠ 0 ∧ A ∈ skewAdjointMatricesSubmodule Φ ∧
      finrank (AlgebraicClosure K) (soCentMat Φ A) = finrank K (soCent Q N) ∧
      ∀ m, A ^ m = 0 ↔ N ^ m = 0 := by
  have hNmem : N ∈ soCent Q N := mem_soCent.2 ⟨hN, rfl⟩
  have hsymm : ∀ x y, bform Q x y = bform Q y x := fun x y => QuadraticMap.associated_isSymm K Q x y
  let b := Module.finBasis K V
  set J := LinearMap.toMatrix₂ b b (bform Q)
  set A := LinearMap.toMatrix b b N
  let φ := algebraMap K (AlgebraicClosure K)
  have hA : A ∈ soCentMat J A := by
    rw [soCentMat_toMatrix]; exact Submodule.mem_map_of_mem hNmem
  have hJ : J.transpose = J := by
    ext i j; simp [J, LinearMap.toMatrix₂_apply, hsymm]
  have hdet : J.det ≠ 0 := (LinearMap.nondegenerate_iff_det_ne_zero b).1 hQ
  refine ⟨J.map φ, A.map φ, ?_, ?_, ?_, ?_, fun m => ?_⟩
  · rw [← Matrix.transpose_map, hJ]
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero φ).2 hdet
  · have hsk := (Submodule.mem_inf.mp hA).1
    rw [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] at hsk ⊢
    rw [← Matrix.transpose_map]
    simp only [← RingHom.mapMatrix_apply, ← map_mul, ← map_neg, hsk]
  · rw [finrank_soCentMat_map, soCentMat_toMatrix, LinearEquiv.finrank_map_eq]
  · rw [← RingHom.mapMatrix_apply, ← map_pow, LinearMap.toMatrix_pow,
      map_eq_zero_iff _ (Matrix.map_injective φ.injective), LinearEquiv.map_eq_zero_iff]

/-- **`dim so(V)_N ≥ ⌊dim V/2⌋`** for every skew `N` (Thesis §5.1.4; the rank of `SO(V)`). For
`dim V ≥ 3` this is Jantzen's bound over the algebraic closure, transported by
`exists_algebraicClosure_soCentMat`; for `dim V ≤ 2` it is checked directly. -/
theorem le_finrank_soCent {Q : QuadraticForm K V} (hQ : IsNondeg Q) {N : Module.End K V}
    (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w)) :
    finrank K V / 2 ≤ finrank K (soCent Q N) := by
  have hNmem : N ∈ soCent Q N := mem_soCent.2 ⟨hN, rfl⟩
  by_cases hn : 3 ≤ finrank K V
  · obtain ⟨Φ, A, hΦ, hdet, hA, he, -⟩ := exists_algebraicClosure_soCentMat hQ hN
    rw [← he]
    exact jantzen_finrank_soCentMat_ge hn Φ hΦ hdet A hA
  · interval_cases h : finrank K V
    · simp
    · simp
    · -- `dim V = 2`
      show 1 ≤ finrank K (soCent Q N)
      rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
      intro hbot
      by_cases hN0 : N = 0
      · let b := Module.finBasis K V
        rw [h] at b
        set a := b ⟨0, by omega⟩
        set c := b ⟨1, by omega⟩
        have hc : c ≠ 0 := b.ne_zero _
        obtain ⟨v, hv⟩ : ∃ v, bform Q c v ≠ 0 := by
          by_contra hne
          push Not at hne
          exact hc ((isNondeg_iff Q).mp hQ c hne)
        have hmem : adV Q (ι Q a * ι Q c) ∈ soCent Q N :=
          mem_soCent.2 ⟨bform_adV (ι_mul_ι_mem_gspin Q a c), by rw [hN0, mul_zero, zero_mul]⟩
        rw [hbot, Submodule.mem_bot] at hmem
        have h0 := congrArg (fun M : Module.End K V => M v) hmem
        simp only [adV_ι_mul_ι, LinearMap.zero_apply] at h0
        have hli : LinearIndependent K ![a, c] := by
          have := b.linearIndependent
          convert this using 1
          ext i; fin_cases i <;> rfl
        have := (LinearIndependent.pair_iff.mp hli) _ _ (by rw [sub_eq_add_neg, ← neg_smul] at h0; exact h0)
        rw [polar_eq_two_mul_bform] at this
        exact hv ((mul_eq_zero.mp this.1).resolve_left (Invertible.ne_zero 2))
      · rw [hbot, Submodule.mem_bot] at hNmem
        exact hN0 hNmem

end LowerBound


variable {K : Type*} [Field K] [Invertible (2 : K)] [CharZero K]

/-- **A skew endomorphism with small centralizer**: every nondegenerate `V` of dimension `n` has
a `b`-skew `Z` (i.e. `Z ∈ so(V) = soCent Q 1`) with `dim so(V)_Z ≤ ⌊n/2⌋`. -/
theorem exists_skew_finrank_soCent_le (n : ℕ) : ∀ {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V), finrank K V = n → IsNondeg Q →
    ∃ Z : Module.End K V, Z ∈ soCent Q 1 ∧ finrank K (soCent Q Z) ≤ n / 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ Q hn hQ
  by_cases hn2 : n < 2
  · refine ⟨0, zero_mem _, ?_⟩
    rw [soCent_of_scalar (c := 0) fun v => by simp, finrank_soCent_one_of_le_two hQ (by omega),
      hn]
  push Not at hn2
  -- an anisotropic orthogonal plane `P = ⟨a, b⟩`
  obtain ⟨e, he⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm (S := K) Q)
  have hani := LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate he hQ
  have h01 : (⟨0, by omega⟩ : Fin (finrank K V)) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  set a := e ⟨0, by omega⟩
  set b := e ⟨1, by omega⟩
  have hab : bform Q a b = 0 := he h01
  have hba : bform Q b a = 0 := he h01.symm
  have haa : bform Q a a ≠ 0 := hani _
  have hbb : bform Q b b ≠ 0 := hani _
  set P := Submodule.span K {a, b}
  set P' := (bform Q).orthogonal P
  have horth : ∀ x ∈ P, ∀ y ∈ P', bform Q x y = 0 := fun x hx y hy =>
    (LinearMap.BilinForm.mem_orthogonal_iff.1 hy) x hx
  have horth' : ∀ y ∈ P', ∀ x ∈ P, bform Q y x = 0 := fun y hy x hx =>
    bform_orth' horth ⟨y, hy⟩ ⟨x, hx⟩
  have haP : a ∈ P := Submodule.subset_span (by simp)
  have hbP : b ∈ P := Submodule.subset_span (by simp)
  have hdisj : Disjoint P P' := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hx
    have h1 := horth a haP _ hx'
    have h2 := horth b hbP _ hx'
    simp only [map_add, map_smul, smul_eq_mul, hab, hba, mul_zero, zero_add, add_zero] at h1 h2
    rw [(mul_eq_zero.1 h1).resolve_right haa, (mul_eq_zero.1 h2).resolve_right hbb, zero_smul,
      zero_smul, add_zero]
  have hB : (bform Q).IsSymm := ⟨bform_comm Q⟩
  have hcompl : IsCompl P P' :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl
      (LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal _ hB.isRefl hdisj)
  have hP2 : finrank K P = 2 := by
    have hli : LinearIndependent K ![a, b] := LinearIndependent.pair_iff.2 fun s t hst => by
      have h1 := congrArg (bform Q a) hst
      have h2 := congrArg (bform Q b) hst
      exact ⟨by simpa [hab, bform_comm Q a b ▸ hab, haa] using h1,
        by simpa [hba, bform_comm Q b a ▸ hba, hbb] using h2⟩
    have := finrank_span_eq_card hli
    rwa [Matrix.range_cons_cons_empty a b ![], Fintype.card_fin] at this
  have hd := Submodule.finrank_add_eq_of_isCompl hcompl
  -- `Z'` on `P^⊥` by induction
  obtain ⟨Z', hZ'so, hZ'⟩ := ih (finrank K P') (by omega) (Q.comp P'.subtype) rfl
    (isNondeg_comp_subtype horth' hQ hcompl.symm)
  -- `J = wedge(a, b)`, with `J² = κ` on `P`
  set J := IsomCent.wedge (bform Q) a b
  set κ : K := -(bform Q a a * bform Q b b)
  have hκ : κ ≠ 0 := neg_ne_zero.2 (mul_ne_zero haa hbb)
  have hJa : J a = -bform Q a a • b := by simp [J, IsomCent.wedge_apply, hba]
  have hJb : J b = bform Q b b • a := by simp [J, IsomCent.wedge_apply, hab]
  have hJP : ∀ x ∈ P, J x ∈ P := by
    intro x hx
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hx
    exact Submodule.mem_span_pair.2 ⟨t * bform Q b b, -(s * bform Q a a), by
      simp only [map_add, map_smul, hJa, hJb, smul_smul, neg_smul, smul_neg]; abel⟩
  have hJJ : ∀ x ∈ P, J (J x) = κ • x := by
    intro x hx
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hx
    simp only [map_add, map_smul, hJa, hJb, κ]
    module
  have hJso : J ∈ soCent Q 1 :=
    mem_soCent.2 ⟨IsomCent.isSkew_wedge hB _ _, by rw [mul_one, one_mul]⟩
  -- choose `c` with `c² κ` not an eigenvalue of `Z'²`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ¬ (Z' * Z').HasEigenvalue (((m : K) + 1) ^ 2 * κ) := by
    have hinj : Function.Injective fun m : ℕ => ((m : K) + 1) ^ 2 * κ := by
      intro m m' h
      have h' : (((m + 1) ^ 2 : ℕ) : K) = (((m' + 1) ^ 2 : ℕ) : K) := by
        push_cast; exact mul_right_cancel₀ hκ h
      have := Nat.pow_left_injective two_ne_zero (Nat.cast_injective h')
      omega
    obtain ⟨_, ⟨m, rfl⟩, hm⟩ := (Set.infinite_range_of_injective hinj).exists_notMem_finset
      (Module.End.finite_hasEigenvalue (Z' * Z')).toFinset
    exact ⟨m, by simpa using hm⟩
  set c : K := (m : K) + 1
  have hcJP : Set.MapsTo (c • J) P P := fun x hx => P.smul_mem c (hJP x hx)
  set Z := sumEnd hcompl ((c • J).restrict hcJP) Z'
  have hZP : ∀ x : P, Z x = c • J x := fun x => sumEnd_left hcompl _ _ x
  have hZP' : ∀ x : P', Z x = Z' x := fun x => sumEnd_right hcompl _ _ x
  have h1P : Set.MapsTo (1 : Module.End K V) P P := fun x hx => hx
  have h1P' : Set.MapsTo (1 : Module.End K V) P' P' := fun x hx => hx
  have hZso : Z ∈ soCent Q 1 := by
    refine sumEnd_mem_soCent horth hcompl h1P h1P'
      (restrict_mem_soCent h1P (Submodule.smul_mem _ c hJso) hcJP) ?_
    have : (1 : Module.End K V).restrict h1P' = 1 := LinearMap.ext fun _ => rfl
    rw [this]
    exact hZ'so
  refine ⟨Z, hZso, ?_⟩
  have hXU : Set.MapsTo Z P P := fun x hx => by
    rw [hZP ⟨x, hx⟩]; exact P.smul_mem c (hJP x hx)
  have hXU' : Set.MapsTo Z P' P' := fun x hx => by rw [hZP' ⟨x, hx⟩]; exact (Z' ⟨x, hx⟩).2
  have hZZ : ∀ y ∈ P, Z (Z y) = (c ^ 2 * κ) • y := by
    intro y hy
    rw [hZP ⟨y, hy⟩, hZP ⟨_, P.smul_mem c (hJP y hy)⟩]
    simp only [map_smul, hJJ y hy, smul_smul]
    ring_nf
  have hM : ∀ M ∈ soCent Q Z, Set.MapsTo M P P := by
    intro M hM x hx
    have hc : ∀ y, Z (M y) = M (Z y) := fun y =>
      (congrArg (fun F : Module.End K V => F y) (mem_soCent.1 hM).2).symm
    obtain ⟨p, p', hpp, -⟩ := Submodule.existsUnique_add_of_isCompl hcompl (M x)
    have e1 : Z (Z (M x)) = (c ^ 2 * κ) • M x := by
      rw [hc, hc, hZZ x hx, map_smul]
    rw [← hpp, map_add, map_add, hZZ p p.2, hZP' p', hZP' (Z' p'), smul_add] at e1
    have hp' : ((Z' * Z') p' : V) = (c ^ 2 * κ) • (p' : V) := add_left_cancel e1
    have h0 : p' = 0 := by
      by_contra hne
      exact hm (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.2 (Subtype.ext (by rw [hp']; rfl)), hne⟩)
    rw [← hpp, h0, Submodule.coe_zero, add_zero]
    exact p.2
  rw [finrank_soCent_eq_add horth hcompl hXU hXU' hM fun M hM' =>
    mapsTo_orthogonal_of_skew (mem_soCent.1 hM').1 (hM M hM')]
  have hP1 : finrank K (soCent (Q.comp P.subtype) (Z.restrict hXU)) ≤ 1 := by
    calc _ ≤ finrank K (soCent (Q.comp P.subtype) 1) := Submodule.finrank_mono fun N hN =>
          mem_soCent.2 ⟨(mem_soCent.1 hN).1, by rw [mul_one, one_mul]⟩
      _ = 1 := by
          rw [finrank_soCent_one_of_le_two (isNondeg_comp_subtype horth hQ hcompl) (by omega), hP2]
  have hres : Z.restrict hXU' = Z' := LinearMap.ext fun x => Subtype.ext (hZP' x)
  rw [hres]
  omega

section Rank

variable {F : Type*} [NontriviallyNormedField F] [CharZero F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- **`rank gspin(V) ≥ ⌊dim V/2⌋ + 1`**: every centralizer `gspin(V)_X` has dimension
`1 + dim so(V)_{adV X} ≥ 1 + ⌊dim V/2⌋`. -/
theorem le_lieRank_gspin {Q : QuadraticForm F V} (hQ : IsNondeg Q) :
    finrank F V / 2 + 1 ≤ lieRank (gspin Q) := by
  have : Nonempty ↥(gspin Q) := ⟨0⟩
  refine le_ciInf fun X => ?_
  rw [finrank_lieCentralizer_gspin hQ X.2]
  exact Nat.add_le_add_right (le_finrank_soCent hQ (bform_adV X.2)) 1


/-- `rank gspin(V) ≤ ⌊dim V/2⌋ + 1`: a lift of the skew `Z` of
`exists_skew_finrank_soCent_le` has a centralizer of dimension `≤ ⌊dim V/2⌋ + 1`. -/
theorem lieRank_gspin_le {Q : QuadraticForm F V} (hQ : IsNondeg Q) :
    lieRank (gspin Q) ≤ finrank F V / 2 + 1 := by
  obtain ⟨Z, hZ, hle⟩ := exists_skew_finrank_soCent_le _ Q rfl hQ
  obtain ⟨Y, hYg, hadV⟩ := exists_mem_gspin_adV_eq hQ Z (mem_soCent.1 hZ).1
  calc lieRank (gspin Q) ≤ finrank F (lieCentralizer (gspin Q) Y) :=
        ciInf_le' (fun X : gspin Q => finrank F (lieCentralizer (gspin Q) (X : CliffordAlgebra Q)))
          ⟨Y, hYg⟩
    _ = finrank F (soCent Q (adV Q Y)) + 1 := finrank_lieCentralizer_gspin hQ hYg
    _ ≤ finrank F V / 2 + 1 := by rw [hadV]; omega

/-- **`rank gspin(V) = ⌊dim V/2⌋ + 1`**, the absolute rank (dimension of a Cartan subalgebra)
of `GSpin(V)`: `le_antisymm` of `lieRank_gspin_le` and `le_lieRank_gspin`. -/
theorem lieRank_gspin {Q : QuadraticForm F V} (hQ : IsNondeg Q) :
    lieRank (gspin Q) = finrank F V / 2 + 1 :=
  le_antisymm (lieRank_gspin_le hQ) (le_lieRank_gspin hQ)

end Rank

/-! ## Centralizers in `𝔤 = gspin(W) × gspin(V)` -/

section LieProd

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- `𝔤_{a,Y} = gspin(W)_{a₁,Y₁} × gspin(V)_{a₂,Y₂}`. -/
theorem mem_lieCentralizer_lieCentralizer_lie (d : GGPData K) {a Y X : d.ambient} :
    X ∈ lieCentralizer (lieCentralizer d.lie a) Y ↔
      X.1 ∈ lieCentralizer (lieCentralizer (gspin d.QW) a.1) Y.1 ∧
        X.2 ∈ lieCentralizer (lieCentralizer (gspin d.QV) a.2) Y.2 := by
  have hl : ∀ Z : d.ambient, Z ∈ d.lie ↔ Z.1 ∈ gspin d.QW ∧ Z.2 ∈ gspin d.QV := fun Z => Iff.rfl
  simp only [mem_lieCentralizer, hl, Prod.ext_iff, Prod.fst_mul, Prod.snd_mul]
  tauto

/-- `𝔤_{a,Y}` is abelian iff both factors are. -/
theorem isLieAbelian_lieCentralizer_lieCentralizer_lie_iff (d : GGPData K) {a Y : d.ambient} :
    IsLieAbelian (lieCentralizer (lieCentralizer d.lie a) Y) ↔
      IsLieAbelian (lieCentralizer (lieCentralizer (gspin d.QW) a.1) Y.1) ∧
        IsLieAbelian (lieCentralizer (lieCentralizer (gspin d.QV) a.2) Y.2) := by
  rw [isLieAbelian_iff_forall_commute, isLieAbelian_iff_forall_commute,
    isLieAbelian_iff_forall_commute]
  have h0W : (0 : CliffordAlgebra d.QW) ∈ lieCentralizer (lieCentralizer (gspin d.QW) a.1) Y.1 :=
    zero_mem _
  have h0V : (0 : CliffordAlgebra d.QV) ∈ lieCentralizer (lieCentralizer (gspin d.QV) a.2) Y.2 :=
    zero_mem _
  constructor
  · intro h
    refine ⟨fun X₁ h₁ X₂ h₂ => ?_, fun X₁ h₁ X₂ h₂ => ?_⟩
    · have := h (X₁, 0) ((mem_lieCentralizer_lieCentralizer_lie d).2 ⟨h₁, h0V⟩) (X₂, 0)
        ((mem_lieCentralizer_lieCentralizer_lie d).2 ⟨h₂, h0V⟩)
      exact congrArg Prod.fst this
    · have := h (0, X₁) ((mem_lieCentralizer_lieCentralizer_lie d).2 ⟨h0W, h₁⟩) (0, X₂)
        ((mem_lieCentralizer_lieCentralizer_lie d).2 ⟨h0W, h₂⟩)
      exact congrArg Prod.snd this
  · rintro ⟨hW, hV⟩ X₁ h₁ X₂ h₂
    rw [mem_lieCentralizer_lieCentralizer_lie] at h₁ h₂
    exact Prod.ext (hW _ h₁.1 _ h₂.1) (hV _ h₁.2 _ h₂.2)

/-- `𝔤_{a,Y} = gspin(W)_{a₁,Y₁} × gspin(V)_{a₂,Y₂}`. -/
theorem finrank_lieCentralizer_lieCentralizer_lie (d : GGPData K) (a Y : d.ambient) :
    finrank K (lieCentralizer (lieCentralizer d.lie a) Y) =
      finrank K (lieCentralizer (lieCentralizer (gspin d.QW) a.1) Y.1) +
        finrank K (lieCentralizer (lieCentralizer (gspin d.QV) a.2) Y.2) := by
  have h : (lieCentralizer (lieCentralizer d.lie a) Y).toSubmodule =
      (lieCentralizer (lieCentralizer (gspin d.QW) a.1) Y.1).toSubmodule.prod
        (lieCentralizer (lieCentralizer (gspin d.QV) a.2) Y.2).toSubmodule := by
    ext Z
    exact mem_lieCentralizer_lieCentralizer_lie d
  show finrank K ↥(lieCentralizer (lieCentralizer d.lie a) Y).toSubmodule =
    finrank K ↥(lieCentralizer (lieCentralizer (gspin d.QW) a.1) Y.1).toSubmodule +
      finrank K ↥(lieCentralizer (lieCentralizer (gspin d.QV) a.2) Y.2).toSubmodule
  rw [h, (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]

end LieProd

end GSpinGGP
