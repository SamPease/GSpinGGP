/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LuoGamma

/-!
# The Lie algebras of the tori of `Γ(G,H)` and of Luo's `𝒯`

Ingredients of `torusIntegralLie_toSO` (Thesis §12.1–12.2; Luo §7.1): for a torus
`T ⊆ GSpin(W)(F)` and its image `T' = φ(T)` under `φ : t ↦ (P(t), P(t) ⊕ 1)`,

* `soSub_eq_quadraticLieSubalgebra`: `so_Cliff(W)` (the traceless part of `gspin(W)`) is the span
  of the bivectors (Tau Ceti's `quadraticLieSubalgebra`), so `C(W) → C(V)` maps it into
  `so_Cliff(V)` (`map_mem_soSub`) and `X ↦ (X, X)` maps it into `𝔤⁰` (`diagLie_mem_lieZero`);
* `toSOLin_diagLie`: `ad (X, X) = (ad X, ad X ⊕ 0)`;
* `deltaLie_eq_delta`, `weylDiscLie_toSOLin`: `Δ` and `D^G` are transported by `ad`;
* `commonFixed_eq_fixedOf_map`, `mem_lieTorus_map_iff`, `lieTorusEquiv`: `ad` maps
  `𝔱⁰ = lieTorus T` onto Luo's `𝔱 = lieTorus T'`;
* `LuoDatum.IsExpCompatT.unique`, `IsExpCompatT.unique`: the measure `ν(T) dX` is unique
  (`Measure.eq_of_isAddHaarMeasure_of_eqOn_nhds`);
* `exists_conj_eq_map_of_isNaturalTorusCorr`: a torus of `𝒯` naturally corresponding to `T` is the
  image of a `GSpin(W)(F)`-conjugate of `T`, so the `H̄(F)`-conjugator reduces to `GSpin(W)(F)`.
-/

noncomputable section

open CliffordAlgebra Module MeasureTheory Topology Filter

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

section SoQuadratic

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The bivectors lie in `so_Cliff(V)`: they are commutators of generators. -/
theorem quadraticLieSubalgebra_le_soSub (Q : QuadraticForm K V) :
    (quadraticLieSubalgebra Q).toSubmodule ≤ (soSub Q).toSubmodule :=
  quadraticLieSubalgebra_toSubmodule_le_of_bivector_mem Q fun a b => by
    rw [bivector_def]
    exact (soSub Q).smul_mem _ (commutator_ι_mem_soSub Q a b)

/-- **`so_Cliff(V)` is spanned by the bivectors** (for nondegenerate `Q`): an `X ∈ so_Cliff(V)` and
the quadratic lift `Y` of `ad X` (`exists_mem_quadratic_commutator_eq`) differ by a scalar
(`eq_algebraMap_of_adV_eq_zero`), which is traceless, hence `0`. -/
theorem soSub_eq_quadraticLieSubalgebra {Q : QuadraticForm K V} (hQ : IsNondeg Q) :
    (soSub Q).toSubmodule = (quadraticLieSubalgebra Q).toSubmodule := by
  refine le_antisymm (fun X hX => ?_) (quadraticLieSubalgebra_le_soSub Q)
  have hX' : X ∈ soSub Q := hX
  obtain ⟨Y, hYq, hY⟩ := exists_mem_quadratic_commutator_eq hQ (adV Q X) fun u w => by
    rw [bform_adV hX'.1]
  have hYs : Y ∈ soSub Q := quadraticLieSubalgebra_le_soSub Q hYq
  have hD : X - Y ∈ gspin Q := sub_mem hX'.1 hYs.1
  have hD0 : adV Q (X - Y) = 0 := by
    ext v
    apply ι_injective Q
    rw [map_sub, LinearMap.sub_apply, map_sub, ι_adV hYs.1, hY, sub_self, LinearMap.zero_apply,
      map_zero]
  obtain ⟨r, hr⟩ := eq_algebraMap_of_adV_eq_zero hQ hD hD0
  have htr : cliffTrace Q (X - Y) = 0 := by
    rw [sub_eq_add_neg, cliffTrace_add, ← neg_one_smul K Y, cliffTrace_smul, hX'.2, hYs.2]
    ring
  rw [hr, Algebra.algebraMap_eq_smul_one, cliffTrace_smul, cliffTrace_one] at htr
  have hr0 : r = 0 := (mul_eq_zero.mp htr).resolve_right (cast_finrank_cliffordAlgebra_ne_zero Q)
  rw [hr0, map_zero, sub_eq_zero] at hr
  rw [hr]
  exact hYq

/-- The algebra map `C(Q₁) → C(Q₂)` of an isometry maps `so_Cliff(Q₁)` into `so_Cliff(Q₂)`
(`soSub_eq_quadraticLieSubalgebra`, Tau Ceti's `map_mem_quadraticLieSubalgebra`). -/
theorem map_mem_soSub {V₂ : Type*} [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
    {Q : QuadraticForm K V} {Q₂ : QuadraticForm K V₂} (hQ : IsNondeg Q) (f : Q →qᵢ Q₂)
    {X : CliffordAlgebra Q} (hX : X ∈ soSub Q) : map f X ∈ soSub Q₂ := by
  have hXq : X ∈ quadraticLieSubalgebra Q := by
    have : X ∈ (soSub Q).toSubmodule := hX
    rw [soSub_eq_quadraticLieSubalgebra hQ] at this
    exact this
  exact quadraticLieSubalgebra_le_soSub Q₂ (map_mem_quadraticLieSubalgebra f hXq)

end SoQuadratic

section HaarLocal

/-- **Two additive Haar measures that agree near `0` are equal**: `ν = c • μ`
(`isAddLeftInvariant_eq_smul`), and a compact neighbourhood `K ⊆ U` of `0` has
`0 < μ K < ∞`, so `c = 1`. -/
theorem _root_.MeasureTheory.Measure.eq_of_isAddHaarMeasure_of_eqOn_nhds {E : Type*} [AddGroup E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [LocallyCompactSpace E]
    [SecondCountableTopology E] [T2Space E] [MeasurableSpace E] [BorelSpace E]
    (μ ν : Measure E) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] {U : Set E} (hU : U ∈ 𝓝 0)
    (h : ∀ S, MeasurableSet S → S ⊆ U → μ S = ν S) : μ = ν := by
  have hc : ν = Measure.addHaarScalarFactor ν μ • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  obtain ⟨K, hK, hKU, hKc⟩ := local_compact_nhds hU
  have h0 : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK).ne'
  have htop : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hK' := h K hKc.isClosed.measurableSet hKU
  rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hK'
  have h1 : ((Measure.addHaarScalarFactor ν μ : NNReal) : ENNReal) = 1 := by
    have := (ENNReal.mul_eq_right h0 htop).mp hK'.symm
    exact this
  rw [hc, ENNReal.coe_eq_one.mp h1, one_smul]

/-- A subspace `p` of a finite-dimensional `F`-algebra `A` (module topology) is a locally
compact, second countable, Hausdorff additive topological group. -/
theorem submodule_topology {F : Type*} [NontriviallyNormedField F] [PAdicField F] {A : Type*}
    [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A] [IsModuleTopology F A]
    (p : Submodule F A) :
    IsTopologicalAddGroup ↥p ∧ T2Space ↥p ∧ LocallyCompactSpace ↥p ∧
      SecondCountableTopology ↥p := by
  have := isTopologicalRing_of_moduleTopology F A
  have : ContinuousSMul F A := IsModuleTopology.toContinuousSMul F A
  have := t2Space_of_moduleTopology F A
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let e : ↥p ≃L[F] (Fin (Module.finrank F ↥p) → F) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  exact ⟨inferInstance, inferInstance, e.toHomeomorph.isClosedEmbedding.locallyCompactSpace,
    e.toHomeomorph.isEmbedding.secondCountableTopology⟩

end HaarLocal

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

/-- `X ↦ (X, X)` maps `so_Cliff(W)` into `𝔤⁰ = so_Cliff(W) ⊕ so_Cliff(V)`. -/
theorem diagLie_mem_lieZero {X : CliffordAlgebra d.QW} (hX : X ∈ soSub d.QW) :
    d.diagLie X ∈ d.lieZero :=
  ⟨hX, map_mem_soSub d.nondeg _ hX⟩

/-- `ad (map inl X) = ad X ⊕ 0` on `V = W ⊕ Z` for `X ∈ gspin(W)`: `X` is even, so its image
commutes with `Z = Wᗮ` (`map_even_commute_ι`). -/
theorem adV_map_inl {X : CliffordAlgebra d.QW} (hX : X ∈ gspin d.QW) (w : Fin d.m → F) (z : d.Z) :
    adV d.QV (map (QuadraticMap.Isometry.inl d.QW d.QZ) X) (w, z) = (adV d.QW X w, 0) := by
  have hu : ∀ w', QuadraticMap.polar d.QV (QuadraticMap.Isometry.inl d.QW d.QZ w') (0, z) = 0 :=
    fun w' => by simp
  have hz : map (QuadraticMap.Isometry.inl d.QW d.QZ) X * ι d.QV (0, z) =
      ι d.QV (0, z) * map (QuadraticMap.Isometry.inl d.QW d.QZ) X :=
    map_even_commute_ι _ (by rw [← even_toSubmodule]; exact hX.1) hu
  have e1 : ((w, z) : d.V) = QuadraticMap.Isometry.inl d.QW d.QZ w + (0, z) := by simp
  have e2 : ((adV d.QW X w, (0 : d.Z)) : d.V) =
      QuadraticMap.Isometry.inl d.QW d.QZ (adV d.QW X w) := rfl
  rw [adV_apply, e1, map_add, mul_add, add_mul, hz, ← CliffordAlgebra.map_apply_ι,
    add_sub_add_right_eq_sub, ← map_mul, ← map_mul, ← map_sub, ← ι_adV hX,
    CliffordAlgebra.map_apply_ι, ιInv_ι, e2]

/-- **`ad (X, X) = (ad X, ad X ⊕ 0)`** for `X ∈ gspin(W)`: `toSOLin ∘ diagLie` is Luo's diagonal
embedding `so(W) → so(W) ⊕ so(V)` after `ad`. -/
theorem toSOLin_diagLie {X : CliffordAlgebra d.QW} (hX : X ∈ gspin d.QW) :
    d.toSOLin (d.diagLie X) = d.luoOf.diagLie (adV d.QW X) := by
  refine Prod.ext rfl (LinearMap.ext fun ⟨w, z⟩ => ?_)
  exact d.adV_map_inl hX w z

/-- **`Δ` is transported by `ad`**: `Δ(X) = |det(ad X|_{ad X(W)})|_F` is Luo's `Δ(ad(X, X))`
(definitional, `fstA_toSOLin`). -/
theorem deltaLie_eq_delta (X : CliffordAlgebra d.QW) :
    d.deltaLie X = d.luoOf.delta (d.toSOLin (d.diagLie X)) := rfl

/-- **`D^G` is transported by `ad`**: for `X ∈ 𝔤⁰`, `ad` conjugates `ad X` on `𝔤⁰` to `ad (ad X)`
on `so(W) ⊕ so(V)` (`toSOLin_commutator`), so the characteristic polynomials agree
(`LinearEquiv.charpoly_conj`). -/
theorem weylDiscLie_toSOLin {X : d.ambient} (hX : X ∈ d.lieZero) :
    weylDiscLie d.lieZero X = weylDiscLie d.luoOf.lie (d.toSOLin X) := by
  have h1 : ∀ Y ∈ d.lieZero.toSubmodule,
      (LinearMap.mulLeft F X - LinearMap.mulRight F X) Y ∈ d.lieZero.toSubmodule := by
    intro Y hY
    have := d.lieZero.lie_mem hX hY
    rwa [Ring.lie_def] at this
  have h2 : ∀ Y ∈ d.luoOf.lie.toSubmodule,
      (LinearMap.mulLeft F (d.toSOLin X) - LinearMap.mulRight F (d.toSOLin X)) Y ∈
        d.luoOf.lie.toSubmodule := by
    intro Y hY
    have := d.luoOf.lie.lie_mem (d.toSO_mem ⟨X, hX⟩) hY
    rwa [Ring.lie_def] at this
  unfold weylDiscLie
  rw [dite_eq_left h1, dite_eq_left h2]
  congr 2
  rw [← LinearEquiv.charpoly_conj d.toSOLinEquiv]
  congr 1
  refine LinearMap.ext fun Y => Subtype.ext ?_
  obtain ⟨Y, rfl⟩ := d.toSOLinEquiv.surjective Y
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  change d.toSOLin (X * Y - Y * X) = d.toSOLin X * d.toSOLin Y - d.toSOLin Y * d.toSOLin X
  exact d.toSOLin_commutator hX Y.2

/-! ### `ad` maps `𝔱⁰` onto Luo's `𝔱` -/

/-- `φ(t) = (P(t), P(t) ⊕ 1)` has `W`-component `P(t)`. -/
theorem fstA_toGbarU_comp_diag (t : ↥(GSpin d.QW)) :
    d.luoOf.fstA ((d.toGbarU.comp d.diag t : d.luoOf.Ambˣ) : d.luoOf.Amb) =
      (specP d.QW t : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) := by
  rw [toGbarU_comp_diag]
  rfl

/-- The common fixed space of `T` in `W` is that of its image `T' = φ(T)` (`W'_T = W'_{T'}`). -/
theorem commonFixed_eq_fixedOf_map (T : Subgroup ↥(GSpin d.QW)) :
    commonFixed T = d.luoOf.fixedOf (T.map (d.toGbarU.comp d.diag)) := by
  have key : ∀ (t : ↥(GSpin d.QW)) (w : d.luoOf.W),
      w ∈ LinearMap.ker (d.luoOf.fstA ((d.toGbarU.comp d.diag t : d.luoOf.Ambˣ) : d.luoOf.Amb) - 1)
        ↔ w ∈ fixedSub t := by
    intro t w
    have e : d.luoOf.fstA ((d.toGbarU.comp d.diag t : d.luoOf.Ambˣ) : d.luoOf.Amb) - 1 =
        (specP d.QW t : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) - LinearMap.id := by
      rw [d.fstA_toGbarU_comp_diag]; rfl
    rw [e]; rfl
  apply le_antisymm
  · refine le_iInf fun t' => ?_
    obtain ⟨_, t, ht, rfl⟩ := t'
    intro w hw
    exact (key t w).mpr (iInf_le (fun t : ↥T => fixedSub (t : ↥(GSpin d.QW))) ⟨t, ht⟩ hw)
  · refine le_iInf fun t => ?_
    intro w hw
    exact (key t w).mp (iInf_le (fun t' : ↥(T.map (d.toGbarU.comp d.diag)) =>
      LinearMap.ker (d.luoOf.fstA ((t' : d.luoOf.Ambˣ) : d.luoOf.Amb) - 1)) ⟨_, t, t.2, rfl⟩ hw)

/-- **`ad` carries `𝔱⁰ = lieTorus T` into Luo's `𝔱 = lieTorus φ(T)`, and back**: for
`X ∈ so_Cliff(W)`, `X` commutes with `T` iff `ad X` commutes with `P(T)` (`commute_iff_adV`), and
the fixed spaces agree (`commonFixed_eq_fixedOf_map`). -/
theorem mem_lieTorus_map_iff (T : Subgroup ↥(GSpin d.QW)) {X : CliffordAlgebra d.QW}
    (hX : X ∈ soSub d.QW) :
    X ∈ d.lieTorus T ↔
      d.toSOLin (d.diagLie X) ∈ d.luoOf.lieTorus (T.map (d.toGbarU.comp d.diag)) := by
  rw [d.toSOLin_diagLie hX.1]
  have hfix := d.commonFixed_eq_fixedOf_map T
  constructor
  · rintro ⟨-, hc, hf⟩
    refine ⟨rfl, adV_mem_skewAdjoint hX.1, ?_, fun w hw => hf w (hfix ▸ hw)⟩
    rintro _ ⟨t, ht, rfl⟩
    rw [d.fstA_toGbarU_comp_diag]
    exact (commute_iff_adV d.nondeg t hX.1).mp (hc t ht)
  · rintro ⟨-, -, hc, hf⟩
    refine ⟨hX, fun t ht => ?_, fun w hw => hf w (hfix ▸ hw)⟩
    have := hc _ ⟨t, ht, rfl⟩
    rw [d.fstA_toGbarU_comp_diag] at this
    exact (commute_iff_adV d.nondeg t hX.1).mpr this

/-- Every `Y ∈ lieTorus φ(T)` is `ad (X, X)` for some `X ∈ lieTorus T`: lift `Y_W ∈ so(W)` along
the bijection `ad : 𝔤⁰ ≃ so(W) ⊕ so(V)` (`toSO`), applied to `(Y_W, 0)`. -/
theorem exists_mem_lieTorus_toSOLin_eq (T : Subgroup ↥(GSpin d.QW)) {Y : d.luoOf.Amb}
    (hY : Y ∈ d.luoOf.lieTorus (T.map (d.toGbarU.comp d.diag))) :
    ∃ X ∈ d.lieTorus T, d.toSOLin (d.diagLie X) = Y := by
  have h0 : d.luoOf.pair (d.luoOf.fstA Y) 0 ∈ d.luoOf.lie :=
    ⟨hY.2.1, (skewAdjointLieSubalgebra (bform d.luoOf.QV)).zero_mem⟩
  set Z := d.toSO.symm ⟨_, h0⟩
  have hZ : d.toSOLin (Z : d.ambient) = d.luoOf.pair (d.luoOf.fstA Y) 0 := d.toSOLin_toSO_symm _
  have hZW : adV d.QW (Z : d.ambient).1 = d.luoOf.fstA Y := congrArg Prod.fst hZ
  have hXs : (Z : d.ambient).1 ∈ soSub d.QW := Z.2.1
  have hY' : d.toSOLin (d.diagLie (Z : d.ambient).1) = Y := by
    rw [d.toSOLin_diagLie hXs.1, hZW]
    exact Prod.ext rfl hY.1.symm
  refine ⟨_, (d.mem_lieTorus_map_iff T hXs).mpr (hY' ▸ hY), hY'⟩

/-- `ad (X, X)` is injective on `so_Cliff(W)` (`toSO_bijective`). -/
theorem toSOLin_diagLie_injective {X X' : CliffordAlgebra d.QW} (hX : X ∈ soSub d.QW)
    (hX' : X' ∈ soSub d.QW) (h : d.toSOLin (d.diagLie X) = d.toSOLin (d.diagLie X')) : X = X' := by
  have := d.toSO_bijective.1 (a₁ := ⟨_, d.diagLie_mem_lieZero hX⟩)
    (a₂ := ⟨_, d.diagLie_mem_lieZero hX'⟩) (Subtype.ext h)
  exact congrArg (fun Y : ↥d.lieZero => (Y : d.ambient).1) this

/-- `ad (X, X)` as a linear map `𝔱⁰ → 𝔱`. -/
def lieTorusMap (T : Subgroup ↥(GSpin d.QW)) :
    ↥(d.lieTorus T) →ₗ[F] ↥(d.luoOf.lieTorus (T.map (d.toGbarU.comp d.diag))) where
  toFun X := ⟨d.toSOLin (d.diagLie X), (d.mem_lieTorus_map_iff T X.2.1).mp X.2⟩
  map_add' X Y := Subtype.ext (by
    change d.toSOLin (d.diagLie ((X : CliffordAlgebra d.QW) + Y)) = _
    rw [show d.diagLie ((X : CliffordAlgebra d.QW) + Y) = d.diagLie X + d.diagLie Y by
      simp [diagLie], map_add]
    rfl)
  map_smul' c X := Subtype.ext (by
    change d.toSOLin (d.diagLie (c • (X : CliffordAlgebra d.QW))) = _
    rw [show d.diagLie (c • (X : CliffordAlgebra d.QW)) = c • d.diagLie X by
      simp [diagLie], map_smul]
    rfl)

/-- **`ad : 𝔱⁰ ≃ 𝔱`**, `X ↦ ad (X, X)`, between `lieTorus T` and Luo's `lieTorus φ(T)`. -/
def lieTorusEquiv (T : Subgroup ↥(GSpin d.QW)) :
    ↥(d.lieTorus T) ≃ₗ[F] ↥(d.luoOf.lieTorus (T.map (d.toGbarU.comp d.diag))) :=
  LinearEquiv.ofBijective (d.lieTorusMap T)
    ⟨fun X X' h => Subtype.ext (d.toSOLin_diagLie_injective X.2.1 X'.2.1 (congrArg Subtype.val h)),
      fun Y => by
        obtain ⟨X, hX, hXY⟩ := d.exists_mem_lieTorus_toSOLin_eq T Y.2
        exact ⟨⟨X, hX⟩, Subtype.ext hXY⟩⟩

@[simp] theorem coe_lieTorusEquiv (T : Subgroup ↥(GSpin d.QW)) (X : ↥(d.lieTorus T)) :
    ((d.lieTorusEquiv T X : ↥(d.luoOf.lieTorus (T.map (d.toGbarU.comp d.diag)))) :
      d.luoOf.Amb) = d.toSOLin (d.diagLie X) := rfl

/-! ### Uniqueness of `ν(T) dX` -/

/-- **The measure `ν(T) dX` on Luo's `𝔱(F)` is unique**: two `exp`-compatible Haar measures agree
on the small measurable sets, hence everywhere (`Measure.eq_of_isAddHaarMeasure_of_eqOn_nhds`). -/
theorem _root_.GSpinGGP.LuoDatum.IsExpCompatT.unique {L : LuoDatum F} {T : Subgroup L.Ambˣ}
    {μ ν : Measure ↥(L.lieTorus T)} (hμ : L.IsExpCompatT T μ) (hν : L.IsExpCompatT T ν) :
    μ = ν := by
  obtain ⟨_, _, _, _⟩ := submodule_topology (L.lieTorus T)
  obtain ⟨hμH, U, hU, hμU⟩ := hμ
  obtain ⟨hνH, U', hU', hνU⟩ := hν
  exact Measure.eq_of_isAddHaarMeasure_of_eqOn_nhds μ ν (inter_mem hU hU') fun S hS hSU =>
    (hμU S hS (hSU.trans Set.inter_subset_left)).trans
      (hνU S hS (hSU.trans Set.inter_subset_right)).symm

/-- **The measure `ν(T) dX` on `𝔱⁰(F)` is unique** (as `LuoDatum.IsExpCompatT.unique`). -/
theorem IsExpCompatT.unique {T : Subgroup ↥(GSpin d.QW)} {μ ν : Measure ↥(d.lieTorus T)}
    (hμ : d.IsExpCompatT T μ) (hν : d.IsExpCompatT T ν) : μ = ν := by
  obtain ⟨_, _, _, _⟩ := submodule_topology (d.lieTorus T)
  obtain ⟨hμH, U, hU, hμU⟩ := hμ
  obtain ⟨hνH, U', hU', hνU⟩ := hν
  exact Measure.eq_of_isAddHaarMeasure_of_eqOn_nhds μ ν (inter_mem hU hU') fun S hS hSU =>
    (hμU S hS (hSU.trans Set.inter_subset_left)).trans
      (hνU S hS (hSU.trans Set.inter_subset_right)).symm

/-- If `𝔱⁰(F)` carries an `exp`-compatible measure, `measLieTorus T` is it. -/
theorem measLieTorus_eq {T : Subgroup ↥(GSpin d.QW)} {μ : Measure ↥(d.lieTorus T)}
    (hμ : d.IsExpCompatT T μ) : d.measLieTorus T = μ := by
  have h : ∃ μ, d.IsExpCompatT T μ := ⟨μ, hμ⟩
  rw [measLieTorus, dite_eq_left h]
  exact IsExpCompatT.unique d h.choose_spec hμ

/-! ### Reducing the `H̄(F)`-conjugator to `GSpin(W)(F)` -/

/-- `φ(t)` has `GL(W)`-component `P(t)`. -/
theorem unitFst_toGbarU_comp_diag (t : ↥(GSpin d.QW)) :
    d.luoOf.unitFst (d.toGbarU.comp d.diag t) = d.specPU t := by
  rw [toGbarU_comp_diag, MonoidHom.comp_apply, LuoDatum.unitFst_diagU]

/-- **A torus of `𝒯` naturally corresponding to `T` is the image of a `GSpin(W)(F)`-conjugate of
`T`**: if `T' = u φ(T) u⁻¹` with `u = (g, (g ⊕ 1) n) ∈ H̄(F)` (`mem_HbarU_iff`), then, as `T'` lies
in the image of `diagU`, `T'` is determined by its `GL(W)`-component `g P(T) g⁻¹`, and
`g = P(g̃)` lifts to `GSpin(W)(F)` (`exists_specP_eq_of_mem_SOu`): `T' = φ(g̃ T g̃⁻¹)`. -/
theorem exists_conj_eq_map_of_isNaturalTorusCorr {T : Subgroup ↥(GSpin d.QW)}
    (T' : d.luoOf.GammaTorus) (h : d.IsNaturalTorusCorr T T'.1) :
    ∃ g : ↥(GSpin d.QW),
      T'.1 = (T.map (MulAut.conj g).toMonoidHom).map (d.toGbarU.comp d.diag) := by
  obtain ⟨u, hu, hT'⟩ := h
  obtain ⟨s, hs, n, -, rfl⟩ := d.luoOf.mem_HbarU_iff.mp hu
  obtain ⟨g, hg⟩ := d.exists_specP_eq_of_mem_SOu hs
  have hgs : d.specPU g = s := Units.ext (by rw [coe_specPU, hg])
  -- elements of `T'` are determined by their `GL(W)`-component
  have hdiag : ∀ y ∈ T'.1, d.luoOf.diagU (d.luoOf.unitFst y) = y := by
    obtain ⟨X, -, hX⟩ := T'.2
    intro y hy
    rw [← hX] at hy
    obtain ⟨z, -, rfl⟩ := hy
    rw [LuoDatum.unitFst_diagU]
  have hfst : ∀ t : ↥(GSpin d.QW),
      d.luoOf.unitFst ((MulAut.conj (d.luoOf.diagU s * d.luoOf.inrU n)).toMonoidHom
        (d.toGbarU.comp d.diag t)) = d.specPU (g * t * g⁻¹) := by
    intro t
    change d.luoOf.unitFst ((d.luoOf.diagU s * d.luoOf.inrU n) * d.toGbarU.comp d.diag t *
      (d.luoOf.diagU s * d.luoOf.inrU n)⁻¹) = _
    rw [map_mul, map_mul, map_inv, d.unitFst_toGbarU_comp_diag,
      d.luoOf.unitFst_diagU_mul_inrU, map_mul, map_mul, map_inv, hgs]
  have hφ : ∀ t : ↥(GSpin d.QW), d.toGbarU.comp d.diag (g * t * g⁻¹) =
      d.luoOf.diagU (d.specPU (g * t * g⁻¹)) := by
    intro t
    rw [toGbarU_comp_diag, MonoidHom.comp_apply]
  refine ⟨g, ?_⟩
  ext x
  constructor
  · intro hx
    have hx' := hx
    rw [hT'] at hx'
    obtain ⟨_, ⟨t, ht, rfl⟩, rfl⟩ := hx'
    refine ⟨g * t * g⁻¹, ⟨t, ht, rfl⟩, ?_⟩
    rw [hφ, ← hfst t, hdiag _ (hT' ▸ ⟨_, ⟨t, ht, rfl⟩, rfl⟩)]
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    have hy : (MulAut.conj (d.luoOf.diagU s * d.luoOf.inrU n)).toMonoidHom
        (d.toGbarU.comp d.diag t) ∈ T'.1 := hT' ▸ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    change d.toGbarU.comp d.diag (g * t * g⁻¹) ∈ T'.1
    rw [hφ, ← hfst t, hdiag _ hy]
    exact hy

end GGPData

end GSpinGGP
