/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.MatrixBaseChange
import GSpinGGP.Foundations.IsometryCentralizer
import GSpinGGP.Foundations.Determinant

/-!
# Endomorphisms with commutative commutant

For an endomorphism `f` of a finite-dimensional space over a field `K` of characteristic `0`:

* `commute_of_squarefree_charpoly`: if the characteristic polynomial of `f` is squarefree, any
  two endomorphisms commuting with `f` commute;
* `squarefree_charpoly_of_commute`: conversely, if `f` is semisimple and any two endomorphisms
  commuting with `f` commute, its characteristic polynomial is squarefree;
* `commute_of_commute_of_isSkewAdjoint`: for `f` invertible and skew for a nondegenerate symmetric
  form, it suffices that any two *skew* endomorphisms commuting with `f` commute
  (`g = ½(g + g*) + ½(g − g*)`, and `f (g + g*)` is skew).

Proof of the first two: over `K̄`, `f` is diagonalizable and the characteristic polynomial is
squarefree iff every eigenspace is a line (`squarefree_charpoly_iff_finrank_eigenspace_le_one`);
an eigenspace of dimension `≥ 2` carries two noncommuting endomorphisms commuting with `f`
(`exists_not_commute_of_one_lt_finrank_eigenspace`, through the projection along
`range (f − μ)`), while on lines everything commutes. The commutant over `K̄` is spanned by the
commutant over `K` (`ker_map_matrix_eq_span`).
-/

noncomputable section

open Module Polynomial

namespace GSpinGGP

section Eigen

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **An eigenspace of dimension `≥ 2` gives a noncommutative commutant**: for `f` semisimple and
`u₀, u₁` independent in `E_μ`, with `π` the projection onto `E_μ` along `range (f − μ)` and
`c₀, c₁` the coordinates in a basis of `E_μ`, the maps `v ↦ c₀(π v) u₁` and `v ↦ c₁(π v) u₀`
commute with `f` but not with each other. -/
theorem exists_not_commute_of_one_lt_finrank_eigenspace {f : Module.End K V}
    (hf : f.IsSemisimple) {μ : K} (h : 1 < finrank K (f.eigenspace μ)) :
    ∃ g g' : Module.End K V, Commute f g ∧ Commute f g' ∧ ¬ Commute g g' := by
  classical
  set φ := f - algebraMap K (Module.End K V) μ with hφ
  have hφss : φ.IsSemisimple := Module.End.isSemisimple_sub_algebraMap_iff.mpr hf
  have hE : f.eigenspace μ = LinearMap.ker φ := by
    rw [Module.End.eigenspace_def, hφ, Module.algebraMap_end_eq_smul_id]
    rfl
  have hc := isCompl_ker_range_of_isSemisimple hφss
  set π := Submodule.projectionOnto _ _ hc
  -- `π` commutes with `f`
  have hπ : ∀ v, ((π (f v) : V)) = f (π v) := by
    intro v
    obtain ⟨k, hk, r, hr, rfl⟩ := Submodule.mem_sup.mp (hc.codisjoint.eq_top ▸ Submodule.mem_top :
      v ∈ LinearMap.ker φ ⊔ LinearMap.range φ)
    have hfk : f k ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker] at hk ⊢
      rw [show φ (f k) = f (φ k) by simp [hφ, Module.algebraMap_end_eq_smul_id], hk, map_zero]
    have hfr : f r ∈ LinearMap.range φ := by
      obtain ⟨w, rfl⟩ := hr
      exact ⟨f w, by simp [hφ, Module.algebraMap_end_eq_smul_id]⟩
    have e1 : π (f k) = ⟨f k, hfk⟩ := Submodule.projectionOnto_apply_left hc ⟨f k, hfk⟩
    have e2 : π (f r) = 0 := Submodule.projectionOnto_apply_right hc ⟨f r, hfr⟩
    have e3 : π k = ⟨k, hk⟩ := Submodule.projectionOnto_apply_left hc ⟨k, hk⟩
    have e4 : π r = 0 := Submodule.projectionOnto_apply_right hc ⟨r, hr⟩
    rw [map_add f, map_add π, map_add π, e1, e2, e3, e4]
    simp
  have hfπ : ∀ v, f (π v) = μ • (π v : V) := fun v => by
    have h' : (f - algebraMap K (Module.End K V) μ) (π v : V) = 0 := (π v).2
    rwa [LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at h'
  let b := Module.finBasis K (LinearMap.ker φ)
  have hn : 1 < finrank K (LinearMap.ker φ) := hE ▸ h
  let i₀ : Fin (finrank K (LinearMap.ker φ)) := ⟨0, by omega⟩
  let i₁ : Fin (finrank K (LinearMap.ker φ)) := ⟨1, hn⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  let g : Module.End K V := ((b.coord i₀).comp π).smulRight (b i₁ : V)
  let g' : Module.End K V := ((b.coord i₁).comp π).smulRight (b i₀ : V)
  have hcomm : ∀ (i j : Fin (finrank K (LinearMap.ker φ))),
      Commute f (((b.coord i).comp π).smulRight (b j : V)) := by
    intro i j
    refine LinearMap.ext fun v => ?_
    simp only [Module.End.mul_apply, LinearMap.smulRight_apply, LinearMap.comp_apply, map_smul]
    have h1 : f (b j : V) = μ • (b j : V) := by
      have h' : (f - algebraMap K (Module.End K V) μ) (b j : V) = 0 := (b j).2
      rwa [LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at h'
    have h2 : π (f v) = μ • π v := Subtype.ext (by rw [hπ, hfπ]; rfl)
    rw [h1, h2, map_smul, smul_eq_mul, smul_comm, mul_smul]
  refine ⟨g, g', hcomm _ _, hcomm _ _, fun hgg => ?_⟩
  have h := LinearMap.congr_fun hgg.eq (b i₁ : V)
  have hπb : ∀ j, π (b j : V) = b j := fun j =>
    Submodule.projectionOnto_apply_left hc (b j)
  simp only [g, g', Module.End.mul_apply, LinearMap.smulRight_apply, LinearMap.comp_apply,
    hπb, Module.Basis.coord_apply, Module.Basis.repr_self, map_smul] at h
  have h' : (b i₁ : V) = 0 := by simpa [h01] using h
  exact b.ne_zero i₁ (Subtype.ext h')

/-- **On lines, everything commutes**: over an algebraically closed field, if `f` is semisimple
and its eigenspaces have dimension `≤ 1`, then endomorphisms commuting with `f` commute (they
preserve each eigenspace, `V` is the sum of the eigenspaces). -/
theorem commute_of_finrank_eigenspace_le_one [IsAlgClosed K] {f : Module.End K V}
    (hf : f.IsSemisimple) (h1 : ∀ μ, finrank K (f.eigenspace μ) ≤ 1) {g g' : Module.End K V}
    (hg : Commute f g) (hg' : Commute f g') : Commute g g' := by
  have htop := hf.iSup_eigenspace_eq_top
  have hle : (⨆ μ, f.eigenspace μ) ≤ LinearMap.ker (g * g' - g' * g) := by
    refine iSup_le fun μ v hv => ?_
    have hm := IsomCent.mapsTo_eigenspace_of_commute hg μ
    have hm' := IsomCent.mapsTo_eigenspace_of_commute hg' μ
    have hc := IsomCent.commute_of_finrank_le_one (h1 μ) (g.restrict hm) (g'.restrict hm')
    have := congrArg Subtype.val (LinearMap.congr_fun hc.eq ⟨v, hv⟩)
    simp only [Module.End.mul_apply, LinearMap.restrict_apply] at this
    simp [this]
  rw [htop] at hle
  refine LinearMap.ext fun v => ?_
  have := hle (Submodule.mem_top (x := v))
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  exact this

/-- **Squarefree characteristic polynomial = eigenspaces are lines**, for a semisimple `f` over
an algebraically closed field: `dim E_μ = dim E_μ^{max} = mult_μ(χ_f)`
(`finrank_maxGenEigenspace_eq`), and a split polynomial is squarefree iff its roots are simple. -/
theorem squarefree_charpoly_iff_finrank_eigenspace_le_one [IsAlgClosed K] [CharZero K]
    {f : Module.End K V} (hf : f.IsSemisimple) :
    Squarefree f.charpoly ↔ ∀ μ, finrank K (f.eigenspace μ) ≤ 1 := by
  classical
  have hmult : ∀ μ, finrank K (f.eigenspace μ) = f.charpoly.rootMultiplicity μ := fun μ => by
    rw [← LinearMap.finrank_maxGenEigenspace_eq,
      (Module.End.isFinitelySemisimple_iff_isSemisimple.mpr hf).maxGenEigenspace_eq_eigenspace]
  have hne : f.charpoly ≠ 0 := f.charpoly_monic.ne_zero
  rw [← PerfectField.separable_iff_squarefree,
    ← nodup_roots_iff_of_splits hne (IsAlgClosed.splits _), Multiset.nodup_iff_count_le_one]
  simp only [count_roots, hmult]

end Eigen

section Descent

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- `X ↦ X M − M X` on matrices (one component). -/
def commMatMap {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (M : Matrix n n R) : Matrix n n R →ₗ[R] (Unit → Matrix n n R) :=
  LinearMap.pi fun _ => LinearMap.mulRight R M - LinearMap.mulLeft R M

theorem mem_ker_commMatMap {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    {M X : Matrix n n R} : X ∈ LinearMap.ker (commMatMap M) ↔ Commute M X := by
  rw [LinearMap.mem_ker, commMatMap, funext_iff]
  simp [sub_eq_zero, Commute, SemiconjBy, eq_comm]

theorem commute_toLin'_iff {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    {X Y : Matrix n n R} : Commute (Matrix.toLin' X) (Matrix.toLin' Y) ↔ Commute X Y := by
  have e : ∀ Z : Matrix n n R, Matrix.toLin' Z = Matrix.toLinAlgEquiv' Z := fun _ => rfl
  rw [e, e]
  exact ⟨fun h => by simpa using h.map Matrix.toLinAlgEquiv'.symm, fun h => h.map _⟩

/-- **A squarefree characteristic polynomial makes the commutant commutative** (characteristic
`0`): over `K̄`, `χ_f` stays squarefree, so `f` is semisimple with eigenspaces of dimension `≤ 1`
(`squarefree_charpoly_iff_finrank_eigenspace_le_one`), and endomorphisms commuting with `f`
commute (`commute_of_finrank_eigenspace_le_one`); descend through matrices. -/
theorem commute_of_squarefree_charpoly {f : Module.End K V} (hsq : Squarefree f.charpoly)
    {g g' : Module.End K V} (hg : Commute f g) (hg' : Commute f g') : Commute g g' := by
  classical
  let L := AlgebraicClosure K
  let φ := algebraMap K L
  have : CharZero L := charZero_of_injective_algebraMap φ.injective
  let b := Module.finBasis K V
  let T := LinearMap.toMatrixAlgEquiv b
  let Mp := φ.mapMatrix (m := Fin (finrank K V))
  have hMinj : Function.Injective Mp := fun X Y h => Matrix.map_injective φ.injective h
  set A := Matrix.toLin' (Mp (T f))
  have hχ : A.charpoly = f.charpoly.map φ := by
    rw [Matrix.charpoly_toLin', show Mp (T f) = (T f).map φ from rfl, Matrix.charpoly_map,
      show T f = LinearMap.toMatrix b b f from rfl, LinearMap.charpoly_toMatrix]
  have hsqL : Squarefree A.charpoly := by
    rw [hχ, ← PerfectField.separable_iff_squarefree]
    exact (PerfectField.separable_iff_squarefree.mpr hsq).map
  have hss : Module.End.IsSemisimple A :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsqL (LinearMap.aeval_self_charpoly A)
  have h1 := (squarefree_charpoly_iff_finrank_eigenspace_le_one hss).mp hsqL
  have hc : ∀ {X : Module.End K V}, Commute f X → Commute A (Matrix.toLin' (Mp (T X))) :=
    fun hX => commute_toLin'_iff.mpr ((hX.map T).map Mp)
  have key := commute_of_finrank_eigenspace_le_one hss h1 (hc hg) (hc hg')
  have key' : Commute (Mp (T g)) (Mp (T g')) := commute_toLin'_iff.mp key
  have : Commute (T g) (T g') := by
    exact hMinj (by rw [map_mul, map_mul]; exact key'.eq)
  simpa using this.map T.symm

/-- **A semisimple endomorphism with commutative commutant has a squarefree characteristic
polynomial** (characteristic `0`): the commutant of the matrix over `K̄` is spanned by that over `K`
(`ker_map_matrix_eq_span`), hence commutative; so every eigenspace over `K̄` is a line
(`exists_not_commute_of_one_lt_finrank_eigenspace`), and `χ_f` is squarefree over `K̄`
(`squarefree_charpoly_iff_finrank_eigenspace_le_one`), hence over `K`. -/
theorem squarefree_charpoly_of_commute {f : Module.End K V} (hf : f.IsSemisimple)
    (hcomm : ∀ g g' : Module.End K V, Commute f g → Commute f g' → Commute g g') :
    Squarefree f.charpoly := by
  classical
  let L := AlgebraicClosure K
  let φ := algebraMap K L
  have : CharZero L := charZero_of_injective_algebraMap φ.injective
  let b := Module.finBasis K V
  let T := LinearMap.toMatrixAlgEquiv b
  set M := T f
  set A := Matrix.toLin' (M.map φ)
  have hχ : A.charpoly = f.charpoly.map φ := by
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map,
      show M = LinearMap.toMatrix b b f from rfl, LinearMap.charpoly_toMatrix]
  have hss : Module.End.IsSemisimple A :=
    isSemisimple_toLin'_map (isSemisimple_toLin'_toMatrix b hf)
  -- the commutant of `M` over `K` is commutative
  have hcK : ∀ X₁ ∈ LinearMap.ker (commMatMap M), ∀ X₂ ∈ LinearMap.ker (commMatMap M),
      Commute X₁ X₂ := by
    intro X₁ h₁ X₂ h₂
    rw [mem_ker_commMatMap] at h₁ h₂
    have hM : T.symm M = f := T.symm_apply_apply f
    have := hcomm (T.symm X₁) (T.symm X₂) (by simpa [hM] using h₁.map T.symm)
      (by simpa [hM] using h₂.map T.symm)
    simpa using this.map T
  have hfg : ∀ X i, commMatMap (M.map φ) (X.map φ) i = (commMatMap M X i).map φ := by
    intro X i
    simp [commMatMap, Matrix.map_mul, Matrix.map_sub]
  have hspan := ker_map_matrix_eq_span _ _ hfg
  have hcL : ∀ g g' : Module.End L (Fin (finrank K V) → L), Commute A g → Commute A g' →
      Commute g g' := by
    intro g g' hg hg'
    have hX : ∀ {h : Module.End L (Fin (finrank K V) → L)}, Commute A h →
        LinearMap.toMatrix' h ∈ LinearMap.ker (commMatMap (M.map φ)) := fun {h} hh => by
      rw [mem_ker_commMatMap, ← commute_toLin'_iff, Matrix.toLin'_toMatrix']
      exact hh
    have h := commute_of_mem_span_map hcK (hspan ▸ hX hg) (hspan ▸ hX hg')
    rw [← commute_toLin'_iff, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix'] at h
    exact h
  have h1 : ∀ μ, finrank L (Module.End.eigenspace A μ) ≤ 1 := by
    intro μ
    by_contra hlt
    obtain ⟨g, g', hg, hg', hn⟩ :=
      exists_not_commute_of_one_lt_finrank_eigenspace hss (not_le.mp hlt)
    exact hn (hcL g g' hg hg')
  have hsqL := (squarefree_charpoly_iff_finrank_eigenspace_le_one hss).mpr h1
  rw [hχ, ← PerfectField.separable_iff_squarefree, separable_map] at hsqL
  exact PerfectField.separable_iff_squarefree.mp hsqL

end Descent

section Skew

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The skew part of the commutant decides commutativity**: for `f` invertible and skew for a
nondegenerate symmetric form `B` (`2 ≠ 0`), if any two `B`-skew endomorphisms commuting with `f`
commute, then any two endomorphisms commuting with `f` commute.  With `g*` the `B`-adjoint, `g − g*`
and `f (g + g*)` are skew and commute with `f`; `f` cancels since it is invertible. -/
theorem commute_of_commute_of_isSkewAdjoint (h2 : (2 : K) ≠ 0) {B : LinearMap.BilinForm K V}
    (hB : B.IsSymm) (hnd : B.Nondegenerate) {f : Module.End K V} (hf : B.IsSkewAdjoint f)
    (hinj : Function.Injective f)
    (hskew : ∀ S₁ S₂ : Module.End K V, B.IsSkewAdjoint S₁ → B.IsSkewAdjoint S₂ → Commute f S₁ →
      Commute f S₂ → Commute S₁ S₂)
    {g g' : Module.End K V} (hg : Commute f g) (hg' : Commute f g') : Commute g g' := by
  -- the adjoint
  let adj : Module.End K V → Module.End K V := fun h => B.leftAdjointOfNondegenerate hnd h
  have hadj : ∀ h x y, B (adj h x) y = B x (h y) := fun h =>
    B.isAdjointPairLeftAdjointOfNondegenerate hnd h
  have hcancel : ∀ X Y : Module.End K V, f * X = f * Y → X = Y := fun X Y h =>
    LinearMap.ext fun v => hinj (LinearMap.congr_fun h v)
  have hsk : ∀ x y, B (f x) y = -B x (f y) := fun x y => by
    have := hf x y
    simp only [Pi.neg_apply, map_neg] at this
    exact this
  -- the adjoint of an element of the commutant commutes with `f`
  have hadjc : ∀ h, Commute f h → Commute f (adj h) := fun h hh => by
    refine (LinearMap.ext fun x => sub_eq_zero.mp (hnd.1 _ fun y => ?_) :
      adj h * f = f * adj h).symm
    simp only [map_sub, LinearMap.sub_apply, Module.End.mul_apply, hadj, hsk]
    rw [← Module.End.mul_apply h f, ← hh.eq, Module.End.mul_apply]
    ring
  -- `h − h*` is skew, `f (h + h*)` is skew
  have hk : ∀ h, B.IsSkewAdjoint (h - adj h) := fun h x y => by
    change B ((h - adj h) x) y = B x (-((h - adj h) y))
    have e : B x (adj h y) = B (h x) y := by rw [hB.eq x, hadj, hB.eq]
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, LinearMap.sub_apply, map_neg, map_sub,
      hadj, e]
    ring
  have ha : ∀ h, Commute f h → B.IsSkewAdjoint (f * (h + adj h)) := fun h hh x y => by
    have hs : ∀ x y, B ((h + adj h) x) y = B x ((h + adj h) y) := fun x y => by
      have e : B x (adj h y) = B (h x) y := by rw [hB.eq x, hadj, hB.eq]
      rw [LinearMap.add_apply, LinearMap.add_apply, map_add, map_add, LinearMap.add_apply, hadj, e,
        add_comm]
    have hc : Commute f (h + adj h) := hh.add_right (hadjc h hh)
    change B ((f * (h + adj h)) x) y = B x (-((f * (h + adj h)) y))
    rw [Module.End.mul_apply, hsk, hs, map_neg, ← Module.End.mul_apply, hc.eq]
  have hkc : ∀ h, Commute f h → Commute f (h - adj h) := fun h hh => hh.sub_right (hadjc h hh)
  have hac : ∀ h, Commute f h → Commute f (f * (h + adj h)) := fun h hh =>
    (Commute.refl f).mul_right (hh.add_right (hadjc h hh))
  set s₁ := g + adj g
  set s₂ := g' + adj g'
  set k₁ := g - adj g
  set k₂ := g' - adj g'
  have hfs₁ : Commute f s₁ := hg.add_right (hadjc g hg)
  have hfs₂ : Commute f s₂ := hg'.add_right (hadjc g' hg')
  have hkk : Commute k₁ k₂ := hskew _ _ (hk g) (hk g') (hkc g hg) (hkc g' hg')
  have haa := hskew _ _ (ha g hg) (ha g' hg') (hac g hg) (hac g' hg')
  have hak := hskew _ _ (ha g hg) (hk g') (hac g hg) (hkc g' hg')
  have hka := hskew _ _ (hk g) (ha g' hg') (hkc g hg) (hac g' hg')
  have hss : Commute s₁ s₂ := by
    refine hcancel _ _ (hcancel _ _ ?_)
    have := haa.eq
    have e1 : s₁ * f = f * s₁ := hfs₁.eq.symm
    have e2 : s₂ * f = f * s₂ := hfs₂.eq.symm
    calc f * (f * (s₁ * s₂)) = f * ((f * s₁) * s₂) := by simp only [mul_assoc]
      _ = f * ((s₁ * f) * s₂) := by rw [e1]
      _ = f * s₁ * (f * s₂) := by simp only [mul_assoc]
      _ = f * s₂ * (f * s₁) := this
      _ = f * ((s₂ * f) * s₁) := by simp only [mul_assoc]
      _ = f * (f * (s₂ * s₁)) := by rw [e2, mul_assoc]
  have hsk₂ : Commute s₁ k₂ := by
    refine hcancel _ _ ?_
    have := hak.eq
    have hfk : Commute f k₂ := hkc g' hg'
    calc f * (s₁ * k₂) = f * s₁ * k₂ := (mul_assoc _ _ _).symm
      _ = k₂ * (f * s₁) := this
      _ = (k₂ * f) * s₁ := (mul_assoc _ _ _).symm
      _ = f * (k₂ * s₁) := by rw [← hfk.eq, mul_assoc]
  have hks₂ : Commute k₁ s₂ := by
    refine hcancel _ _ ?_
    have := hka.eq
    have hfk : Commute f k₁ := hkc g hg
    calc f * (k₁ * s₂) = (f * k₁) * s₂ := (mul_assoc _ _ _).symm
      _ = k₁ * (f * s₂) := by rw [hfk.eq, mul_assoc]
      _ = f * s₂ * k₁ := this
      _ = f * (s₂ * k₁) := mul_assoc _ _ _
  have htot : Commute (s₁ + k₁) (s₂ + k₂) :=
    (hss.add_right hsk₂).add_left (hks₂.add_right hkk)
  have e₁ : s₁ + k₁ = (2 : K) • g := by
    simp only [s₁, k₁, two_smul]; abel
  have e₂ : s₂ + k₂ = (2 : K) • g' := by
    simp only [s₂, k₂, two_smul]; abel
  rw [e₁, e₂] at htot
  have := (htot.smul_left (2 : K)⁻¹).smul_right (2 : K)⁻¹
  rwa [smul_smul, smul_smul, inv_mul_cancel₀ h2, one_smul, one_smul] at this

end Skew

end GSpinGGP
