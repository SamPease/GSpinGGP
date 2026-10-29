/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
-/
import Mathlib

/-!
# Unitary representations of totally disconnected locally compact groups

Generic unitary representation theory needed to *state* the local GGP conjecture
(the `p`-adic case). Nothing here mentions fields or `GSpin`.

Sources:
* Thesis Ch. 1: tempered representations, `π^∞`, `m(π)`;
* Thesis §3.1: smooth and tempered representations;
* Thesis §4.4: Whittaker models;
* Thesis §5.5: the multiplicity `m(π)`.

## Main definitions

* `UnitaryRep G`: a strongly continuous unitary representation on a complex Hilbert space.
* `UnitaryRep.IsIrreducible`, `UnitaryRep.IsEquivalent`.
* `leftTranslate`, `leftRegular G`: the left regular representation on `L²(G, haar)`.
* `WeaklyContainedIn`, `IsTempered`.
* `IsTrivialOn`, `HasCentralChar`.
* `smoothVectors π` (= `π^∞`, `p`-adic: vectors with open stabilizer) and its `ρ`-stability.
* `equivariantForms π S ξ`, `multiplicity π S ξ`, `HasModel π S ξ`.
* `testFunctions G`, `fixedSpace`, `IsAdmissible`, `OpIntegrable`, `opOf`, `traceOf`,
  `IsCharacterOf`, `characterOn`.

## Main results

* `UnitaryRep.equivSetoid`: unitary equivalence is an equivalence relation.
* Invariance under unitary equivalence: `isIrreducible_congr`, `isTempered_congr`,
  `hasCentralChar_congr`, `isTrivialOn_congr`, `traceOf_congr`, `characterOn_congr`,
  `multiplicity_congr`, `hasModel_congr`.
* `HasCentralChar.mul`, `.norm_eq_one`, `.continuous` (for `π ≠ 0`, e.g. irreducible): a central
  character is a continuous unitary character.
* `ae_eq_zero_of_integral_testFunctions`: on a totally disconnected, locally compact,
  σ-compact group, test functions separate locally integrable functions (so characters are
  unique a.e., `IsCharacterOf.ae_eq`).

## Universe note

The Hilbert space of `π : UnitaryRep G` lives in the same universe as `G`
(`H : Type u` for `G : Type u`) so that `leftRegular G` (on `Lp ℂ 2 haar : Type u`) is a
`UnitaryRep G`. For `G : Type` this is exactly the §7 contract's `H : Type`.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal Pointwise

namespace GSpinGGP

universe u

/-- A strongly continuous unitary representation of a topological group `G` on a complex
Hilbert space `H` (Thesis §3.1). -/
structure UnitaryRep (G : Type u) [Group G] [TopologicalSpace G] where
  /-- The underlying Hilbert space. -/
  H : Type u
  [normed : NormedAddCommGroup H]
  [inner : InnerProductSpace ℂ H]
  [complete : CompleteSpace H]
  /-- The action. -/
  ρ : G →* (H →L[ℂ] H)
  /-- Each `ρ g` is unitary. -/
  unitary_ρ : ∀ g, ρ g ∈ unitary (H →L[ℂ] H)
  /-- Strong continuity: `g ↦ ρ g v` is continuous for every `v`. -/
  strongCont : ∀ v : H, Continuous fun g => ρ g v

attribute [instance] UnitaryRep.normed UnitaryRep.inner UnitaryRep.complete

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace UnitaryRep

/-- `π` is (topologically) irreducible: `H ≠ 0` and the only closed `ρ`-invariant subspaces are
`⊥` and `⊤` (Thesis §3.1). -/
def IsIrreducible (π : UnitaryRep G) : Prop :=
  Nontrivial π.H ∧
    ∀ W : Submodule ℂ π.H, IsClosed (W : Set π.H) → (∀ g, ∀ v ∈ W, π.ρ g v ∈ W) →
      W = ⊥ ∨ W = ⊤

/-- Unitary equivalence: there is a unitary (surjective linear isometry) intertwining
isomorphism (Thesis §3.1). -/
def IsEquivalent (π π' : UnitaryRep G) : Prop :=
  ∃ U : π.H ≃ₗᵢ[ℂ] π'.H, ∀ g v, U (π.ρ g v) = π'.ρ g (U v)

end UnitaryRep

section Regular

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

/-- Left translation `(λ(g) f)(x) = f(g⁻¹ x)` on `L²(G, haar)`. -/
noncomputable def leftTranslate (g : G) :
    Lp ℂ 2 (Measure.haar : Measure G) →L[ℂ] Lp ℂ 2 (Measure.haar : Measure G) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x : G => g⁻¹ * x)
    (measurePreserving_mul_left (Measure.haar : Measure G) g⁻¹)).toContinuousLinearMap

omit [T2Space G] in
private lemma compMeasurePreserving_congr {f f' : G → G} (h : f = f')
    (hf : MeasurePreserving f (Measure.haar : Measure G) Measure.haar)
    (hf' : MeasurePreserving f' (Measure.haar : Measure G) Measure.haar)
    (v : Lp ℂ 2 (Measure.haar : Measure G)) :
    Lp.compMeasurePreserving f hf v = Lp.compMeasurePreserving f' hf' v := by
  subst h; rfl

omit [T2Space G] in
lemma leftTranslate_one : leftTranslate (1 : G) = 1 :=
  ContinuousLinearMap.ext fun v => by
    change Lp.compMeasurePreserving _ _ v = v
    rw [compMeasurePreserving_congr (f' := id) (by funext x; simp) _ (MeasurePreserving.id _)]
    exact Lp.compMeasurePreserving_id_apply v

omit [T2Space G] in
lemma leftTranslate_mul (g h : G) : leftTranslate (g * h) = leftTranslate g * leftTranslate h :=
  ContinuousLinearMap.ext fun v => by
    change Lp.compMeasurePreserving _ _ v =
      Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ v)
    rw [compMeasurePreserving_congr (f' := (fun x => h⁻¹ * x) ∘ (fun x => g⁻¹ * x))
      (by funext x; simp [mul_assoc]) _
      ((measurePreserving_mul_left _ h⁻¹).comp (measurePreserving_mul_left _ g⁻¹))]
    exact Lp.compMeasurePreserving_comp_apply v _ _

omit [T2Space G] in
lemma leftTranslate_mem_unitary (g : G) :
    leftTranslate g ∈ unitary (Lp ℂ 2 (Measure.haar : Measure G) →L[ℂ] Lp ℂ 2 (Measure.haar : Measure G)) := by
  have hsurj : Function.Surjective (Lp.compMeasurePreservingₗᵢ ℂ (fun x : G => g⁻¹ * x)
      (measurePreserving_mul_left (Measure.haar : Measure G) g⁻¹)) := fun v =>
    ⟨leftTranslate g⁻¹ v, by
      change (leftTranslate g * leftTranslate g⁻¹) v = v
      rw [← leftTranslate_mul, mul_inv_cancel, leftTranslate_one]
      rfl⟩
  exact (Unitary.linearIsometryEquiv.symm (LinearIsometryEquiv.ofSurjective _ hsurj)).2

omit [T2Space G] in
/-- Strong continuity of the left regular representation (Mathlib's
`Continuous.compMeasurePreservingLp`, using that Haar measure is regular). -/
lemma continuous_leftTranslate_apply (v : Lp ℂ 2 (Measure.haar : Measure G)) :
    Continuous fun g : G => leftTranslate g v := by
  have hc : Continuous fun z : G => (⟨fun x => z⁻¹ * x, by fun_prop⟩ : C(G, G)) :=
    ContinuousMap.continuous_of_continuous_uncurry _
      (show Continuous fun p : G × G => p.1⁻¹ * p.2 by fun_prop)
  exact continuous_const.compMeasurePreservingLp hc
    (fun z => measurePreserving_mul_left (Measure.haar : Measure G) z⁻¹) (by norm_num)

/-- The left regular representation of `G` on `L²(G, haar)`: `(λ(g) f)(x) = f(g⁻¹ x)`
(Thesis Ch. 1, the "regular representation of `G(F)`"). -/
noncomputable def leftRegular (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] : UnitaryRep G where
  H := Lp ℂ 2 (Measure.haar : Measure G)
  ρ :=
    { toFun := leftTranslate
      map_one' := leftTranslate_one
      map_mul' := leftTranslate_mul }
  unitary_ρ := leftTranslate_mem_unitary
  strongCont := continuous_leftTranslate_apply

/-- Weak containment (Fell): `π` is weakly contained in `σ` if every diagonal matrix
coefficient of `π` is a limit, uniformly on compact sets, of finite sums of diagonal matrix
coefficients of `σ`. -/
def WeaklyContainedIn (π σ : UnitaryRep G) : Prop :=
  ∀ v : π.H, ∀ K : Set G, IsCompact K → ∀ ε : ℝ, 0 < ε →
    ∃ (n : ℕ) (w : Fin n → σ.H), ∀ g ∈ K,
      ‖⟪π.ρ g v, v⟫_ℂ - ∑ i, ⟪σ.ρ g (w i), w i⟫_ℂ‖ < ε

/-- `π` is an irreducible tempered representation (Thesis Ch. 1 and §3.1.2):
irreducible and weakly contained in the left regular representation of `G`.

The thesis defines temperedness by a growth condition on matrix coefficients and notes that
"an equivalent condition is that `π` belongs weakly to the regular representation". The
equivalence of the two is Cowling–Haagerup–Howe (1988); the weak-containment form is used here
because it remains valid when the centre of `G` is noncompact (as for `GSpin`),
where the growth condition must otherwise be stated modulo the centre. -/
def IsTempered (π : UnitaryRep G) : Prop :=
  π.IsIrreducible ∧ WeaklyContainedIn π (leftRegular G)

end Regular

/-- `π` is trivial on `S` (used for "central character trivial on `Z_{G,H}(F)`",
Thesis §6.3). -/
def IsTrivialOn (π : UnitaryRep G) (S : Set G) : Prop :=
  ∀ s ∈ S, π.ρ s = 1

/-- `π` has central character `χ` on the (central) subgroup `A`, i.e. `ρ a = χ a • 1`
(Thesis §7.1). -/
def HasCentralChar (π : UnitaryRep G) (A : Subgroup G) (χ : ↥A → ℂ) : Prop :=
  ∀ a : ↥A, π.ρ a = χ a • (1 : π.H →L[ℂ] π.H)

theorem isTrivialOn_iff_hasCentralChar_one (π : UnitaryRep G) (A : Subgroup G) :
    IsTrivialOn π (A : Set G) ↔ HasCentralChar π A (fun _ => 1) := by
  simp only [IsTrivialOn, HasCentralChar, one_smul, SetLike.mem_coe, Subtype.forall]

/-! ### Smooth vectors -/

/-- The smooth vectors `π^∞` of `π` in the `p`-adic case: the vectors whose stabilizer
contains an open subgroup (Thesis §3.1.2 and Ch. 1). -/
def smoothVectors (π : UnitaryRep G) : Submodule ℂ π.H where
  carrier := {v | ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π.ρ u v = v}
  zero_mem' := ⟨⊤, isOpen_univ, fun u _ => map_zero _⟩
  add_mem' := by
    rintro v w ⟨U, hU, hv⟩ ⟨U', hU', hw⟩
    refine ⟨U ⊓ U', hU.inter hU', fun u hu => ?_⟩
    rw [map_add, hv u hu.1, hw u hu.2]
  smul_mem' := by
    rintro c v ⟨U, hU, hv⟩
    exact ⟨U, hU, fun u hu => by rw [map_smul, hv u hu]⟩

section Smooth

variable [IsTopologicalGroup G]

/-- `π^∞` is `ρ`-stable (Thesis Ch. 1: "this subspace is `G(F)`-invariant"). -/
theorem smoothVectors_stable (π : UnitaryRep G) (g : G) {v : π.H}
    (hv : v ∈ smoothVectors π) : π.ρ g v ∈ smoothVectors π := by
  obtain ⟨U, hU, hfix⟩ := hv
  refine ⟨U.comap (MulAut.conj g⁻¹).toMonoidHom, ?_, fun x hx => ?_⟩
  · have hc : Continuous fun x : G => g⁻¹ * x * g⁻¹⁻¹ := by fun_prop
    exact hU.preimage hc
  · have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ U := hx
    have h1 := hfix _ hx'
    rw [inv_inv] at h1
    calc π.ρ x (π.ρ g v) = π.ρ (x * g) v := by rw [map_mul]; rfl
      _ = π.ρ (g * (g⁻¹ * x * g)) v := by rw [show g * (g⁻¹ * x * g) = x * g by group]
      _ = π.ρ g (π.ρ (g⁻¹ * x * g) v) := by rw [map_mul]; rfl
      _ = π.ρ g v := by rw [h1]

/-- The action of `G` on `π^∞`. -/
def smoothAction (π : UnitaryRep G) (g : G) :
    ↥(smoothVectors π) →ₗ[ℂ] ↥(smoothVectors π) :=
  ((π.ρ g).toLinearMap.restrict fun _ hv => smoothVectors_stable π g hv)

@[simp]
theorem smoothAction_apply (π : UnitaryRep G) (g : G) (v : ↥(smoothVectors π)) :
    (smoothAction π g v : π.H) = π.ρ g v := rfl

/-! ### Equivariant forms and multiplicities -/

/-- The space `Hom_S(π^∞, ξ)` of `(S, ξ)`-equivariant linear forms on `π^∞`:
`ℓ(ρ s v) = ξ(s) ℓ(v)` (Thesis Ch. 1, §5.5).

In the `p`-adic case, `π^∞` is given its finest locally convex topology, for which *every*
linear form is continuous (Thesis Ch. 1), so we use the full algebraic dual. -/
def equivariantForms (π : UnitaryRep G) (S : Subgroup G) (ξ : ↥S → ℂ) :
    Submodule ℂ (Module.Dual ℂ ↥(smoothVectors π)) where
  carrier := {ℓ | ∀ s : ↥S, ∀ v, ℓ (smoothAction π s v) = ξ s * ℓ v}
  zero_mem' := by intro s v; simp
  add_mem' := by
    intro ℓ ℓ' hℓ hℓ' s v
    simp only [LinearMap.add_apply, hℓ s v, hℓ' s v, mul_add]
  smul_mem' := by
    intro c ℓ hℓ s v
    simp only [LinearMap.smul_apply, hℓ s v, smul_eq_mul]
    ring

/-- The multiplicity `m(π) = dim Hom_S(π^∞, ξ)` (Thesis Ch. 1, §5.5), valued in
`ℕ∞` (`⊤` if infinite-dimensional). -/
noncomputable def multiplicity (π : UnitaryRep G) (S : Subgroup G) (ξ : ↥S → ℂ) : ℕ∞ :=
  Cardinal.toENat (Module.rank ℂ ↥(equivariantForms π S ξ))

/-- `π` has an `(S, ξ)`-model (a Whittaker model when `(S, ξ)` is a Whittaker datum, Thesis
§4.4; a Bessel model for a GGP triple): there is a nonzero `(S, ξ)`-equivariant form on
`π^∞`. -/
def HasModel (π : UnitaryRep G) (S : Subgroup G) (ξ : ↥S → ℂ) : Prop :=
  equivariantForms π S ξ ≠ ⊥

theorem hasModel_iff_multiplicity_ne_zero (π : UnitaryRep G) (S : Subgroup G) (ξ : ↥S → ℂ) :
    HasModel π S ξ ↔ multiplicity π S ξ ≠ 0 := by
  rw [HasModel, multiplicity, Ne, Ne, Cardinal.toENat_eq_zero, Submodule.rank_eq_zero]

end Smooth

/-! ### Test functions, admissibility and characters -/

/-- `C_c^∞(G)`: locally constant compactly supported functions (Thesis §2.3, `p`-adic
case). -/
def testFunctions (G : Type u) [Group G] [TopologicalSpace G] : Submodule ℂ (G → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := fun c _ hf =>
    ⟨hf.1.comp (c • ·), hf.2.comp_left (g := (c • · : ℂ → ℂ)) (smul_zero c)⟩

/-- The `K`-fixed vectors `π^K` (Thesis §3.1). -/
def fixedSpace (π : UnitaryRep G) (K : Subgroup G) : Submodule ℂ π.H where
  carrier := {v | ∀ k ∈ K, π.ρ k v = v}
  zero_mem' := fun _ _ => map_zero _
  add_mem' := fun hv hw k hk => by rw [map_add, hv k hk, hw k hk]
  smul_mem' := fun c _ hv k hk => by rw [map_smul, hv k hk]

theorem fixedSpace_le_smoothVectors (π : UnitaryRep G) {K : Subgroup G}
    (hK : IsOpen (K : Set G)) : fixedSpace π K ≤ smoothVectors π :=
  fun _ hv => ⟨K, hK, hv⟩

/-- `π` is admissible: `π^K` is finite-dimensional for every compact open subgroup `K`
(Thesis §3.1; tempered irreducible representations of `p`-adic groups are admissible). -/
def IsAdmissible (π : UnitaryRep G) : Prop :=
  ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) →
    FiniteDimensional ℂ ↥(fixedSpace π K)

/-- `f` is bi-`K`-invariant. -/
def IsBiInvariant (K : Subgroup G) (f : G → ℂ) : Prop :=
  ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g

section Characters

attribute [local instance] Classical.propDecidable

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

/-- The condition under which `π(f)` is defined by a Bochner integral: `g ↦ f(g) ρ(g) v` is
Haar-integrable for every `v`. It holds for test functions (`opIntegrable_of_mem_testFunctions`)
and, when `G` is second countable, for every `f ∈ L¹(G)`. -/
def OpIntegrable (π : UnitaryRep G) (f : G → ℂ) : Prop :=
  ∀ v : π.H, Integrable (fun g => f g • π.ρ g v) (Measure.haar : Measure G)

/-- The operator `π(f) v = ∫_G f(g) ρ(g) v dg` (Haar measure), as a strong integral
(Thesis §3.1), with `‖π(f)‖ ≤ ‖f‖₁`. It is defined to be `0` unless `OpIntegrable π f`
(without that guard `v ↦ ∫ f(g) ρ(g) v dg` need not be additive, by the Bochner-integral
convention `∫ = 0` for non-integrable integrands). -/
noncomputable def opOf (π : UnitaryRep G) (f : G → ℂ) : π.H →L[ℂ] π.H :=
  LinearMap.mkContinuous
    { toFun := fun v =>
        if OpIntegrable π f then ∫ g, f g • π.ρ g v ∂(Measure.haar : Measure G) else 0
      map_add' := by
        intro v w
        split_ifs with h
        · simp only [map_add, smul_add]
          exact integral_add (h v) (h w)
        · simp
      map_smul' := by
        intro c v
        split_ifs with h
        · simp only [map_smul, RingHom.id_apply]
          rw [← integral_smul]
          congr 1
          funext g
          exact smul_comm _ _ _
        · simp }
    (∫ g, ‖f g‖ ∂(Measure.haar : Measure G))
    (by
      intro v
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      split_ifs with h
      · refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        rw [← integral_mul_const]
        congr 1
        funext g
        rw [norm_smul, ContinuousLinearMap.norm_map_of_mem_unitary (π.unitary_ρ g)]
      · simpa using mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (norm_nonneg v))

omit [T2Space G] in
theorem opOf_apply (π : UnitaryRep G) {f : G → ℂ} (hf : OpIntegrable π f) (v : π.H) :
    opOf π f v = ∫ g, f g • π.ρ g v ∂(Measure.haar : Measure G) := by
  simp [opOf, hf]

omit [T2Space G] in
theorem opOf_of_not_opIntegrable (π : UnitaryRep G) {f : G → ℂ} (hf : ¬ OpIntegrable π f) :
    opOf π f = 0 :=
  ContinuousLinearMap.ext fun v => by simp [opOf, hf]

omit [T2Space G] in
/-- Test functions are `OpIntegrable`: `g ↦ f(g) ρ(g) v` is continuous with compact support. -/
theorem opIntegrable_of_mem_testFunctions (π : UnitaryRep G) {f : G → ℂ}
    (hf : f ∈ testFunctions G) : OpIntegrable π f := fun v =>
  (hf.1.continuous.smul (π.strongCont v)).integrable_of_hasCompactSupport hf.2.smul_right

omit [T2Space G] in
/-- If `f` is left `K`-invariant, then `ρ(k) π(f) = π(f)` for `k ∈ K`: the range of `π(f)` lies
in `π^K`. -/
theorem rho_opOf_of_leftInvariant (π : UnitaryRep G) {f : G → ℂ} {K : Subgroup G}
    (hK : ∀ k ∈ K, ∀ g, f (k * g) = f g) {k : G} (hk : k ∈ K) (v : π.H) :
    π.ρ k (opOf π f v) = opOf π f v := by
  by_cases h : OpIntegrable π f
  · rw [opOf_apply π h, ← ContinuousLinearMap.integral_comp_comm _ (h v)]
    have hfun : (fun g => π.ρ k (f g • π.ρ g v)) =
        fun g => (fun x => f (k⁻¹ * x) • π.ρ x v) (k * g) := by
      funext g
      simp only [map_smul, map_mul, inv_mul_cancel_left]
      rfl
    rw [hfun, integral_mul_left_eq_self (fun x => f (k⁻¹ * x) • π.ρ x v) k]
    congr 1
    funext x
    rw [hK k⁻¹ (K.inv_mem hk) x]
  · simp [opOf_of_not_opIntegrable π h]

/-- The datum used to compute `tr π(f)`: a compact open subgroup `K` with `f` bi-`K`-invariant,
`π^K` finite-dimensional, and `π(f)` preserving `π^K`. -/
def TraceDatum (π : UnitaryRep G) (f : G → ℂ) (K : Subgroup G) : Prop :=
  IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ IsBiInvariant K f ∧
    FiniteDimensional ℂ ↥(fixedSpace π K) ∧
    ∀ v ∈ fixedSpace π K, opOf π f v ∈ fixedSpace π K

/-- `tr π(f)` for an admissible `π` and a test function `f` (Thesis §3.1): for `f` bi-`K`-
invariant, `π(f) = e_K π(f) e_K` has range in `π^K` and vanishes on `(π^K)^⊥`, so its trace is
the trace of its restriction to the finite-dimensional `π^K`. Defined by the epsilon pattern
(`0` if no such `K` exists); independence of `K` is `traceOf_eq`. -/
noncomputable def traceOf (π : UnitaryRep G) (f : G → ℂ) : ℂ :=
  if h : ∃ K : Subgroup G, TraceDatum π f K then
    LinearMap.trace ℂ ↥(fixedSpace π h.choose)
      ((opOf π f).toLinearMap.restrict h.choose_spec.2.2.2.2)
  else 0

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G]
  [BorelSpace G] in
/-- Linear algebra: if `T` maps everything into `W ≤ M` with `M` finite-dimensional, then the
traces of `T` on `M` and on `W` agree. -/
theorem trace_restrict_eq_of_forall_mem {E : Type*} [AddCommGroup E] [Module ℂ E]
    (T : E →ₗ[ℂ] E) {M W : Submodule ℂ E} (hWM : W ≤ M) [FiniteDimensional ℂ ↥M]
    (hT : ∀ x, T x ∈ W) :
    LinearMap.trace ℂ ↥M (T.restrict fun x _ => hWM (hT x)) =
      LinearMap.trace ℂ ↥W (T.restrict fun x _ => hT x) := by
  have : FiniteDimensional ℂ ↥W :=
    Module.Finite.of_injective (Submodule.inclusion hWM) (Submodule.inclusion_injective hWM)
  let S : ↥M →ₗ[ℂ] ↥W := LinearMap.codRestrict W (T ∘ₗ M.subtype) fun x => hT x
  have h1 : T.restrict (fun x _ => hWM (hT x)) = Submodule.inclusion hWM ∘ₗ S := by
    ext x; rfl
  have h2 : T.restrict (fun x _ => hT x) = S ∘ₗ Submodule.inclusion hWM := by
    ext x; rfl
  rw [h1, h2, LinearMap.trace_comp_comm']

omit [T2Space G] in
/-- The trace does not depend on the choice of `K`: for two data `K, K'`, `π(f)` has range in
`π^K ∩ π^{K'}` (left invariance), and both traces equal the trace on that subspace. -/
theorem traceOf_eq (π : UnitaryRep G) (f : G → ℂ) (K : Subgroup G) (hK : TraceDatum π f K) :
    traceOf π f =
      LinearMap.trace ℂ ↥(fixedSpace π K) ((opOf π f).toLinearMap.restrict hK.2.2.2.2) := by
  unfold traceOf
  split_ifs with h
  swap
  · exact absurd ⟨K, hK⟩ h
  set K₀ := h.choose
  have hK₀ : TraceDatum π f K₀ := h.choose_spec
  have : FiniteDimensional ℂ ↥(fixedSpace π K₀) := hK₀.2.2.2.1
  have : FiniteDimensional ℂ ↥(fixedSpace π K) := hK.2.2.2.1
  have hmem : ∀ (L : Subgroup G), TraceDatum π f L → ∀ v, opOf π f v ∈ fixedSpace π L :=
    fun L hL v k hk => rho_opOf_of_leftInvariant π (fun k hk g => (hL.2.2.1 k hk g).1) hk v
  have hW : ∀ v, (opOf π f).toLinearMap v ∈ fixedSpace π K₀ ⊓ fixedSpace π K :=
    fun v => ⟨hmem K₀ hK₀ v, hmem K hK v⟩
  rw [trace_restrict_eq_of_forall_mem (opOf π f).toLinearMap inf_le_left hW,
    trace_restrict_eq_of_forall_mem (opOf π f).toLinearMap inf_le_right hW]

omit [T2Space G] in
/-- For `f` bi-`K`-invariant, `π(f)` preserves `π^K` (indeed maps all of `H` into `π^K`). -/
theorem opOf_mem_fixedSpace (π : UnitaryRep G) {f : G → ℂ} {K : Subgroup G}
    (_hf : f ∈ testFunctions G) (hK : IsBiInvariant K f) {v : π.H} (_hv : v ∈ fixedSpace π K) :
    opOf π f v ∈ fixedSpace π K :=
  fun _ hk => rho_opOf_of_leftInvariant π (fun k hk g => (hK k hk g).1) hk v

omit [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- A test function is invariant under left translation by a neighbourhood of `1`: each nonzero
fibre `f⁻¹{c}` is compact open, so `V_c · f⁻¹{c} ⊆ f⁻¹{c}` for some `V_c ∈ 𝓝 1`, and only finitely
many `c` occur. -/
theorem exists_nhds_one_leftInvariant {f : G → ℂ} (hf : f ∈ testFunctions G) :
    ∃ V ∈ nhds (1 : G), ∀ u ∈ V, ∀ x, f (u * x) = f x := by
  have hcpt : IsCompact (tsupport f) := hf.2
  have : CompactSpace ↥(tsupport f) := isCompact_iff_compactSpace.mp hcpt
  have hfin : (f '' tsupport f).Finite := by
    rw [Set.image_eq_range]
    exact (hf.1.comp_continuous continuous_subtype_val).range_finite
  have hfib : ∀ c : ℂ, ∃ V ∈ nhds (1 : G), c ≠ 0 → V * (f ⁻¹' {c}) ⊆ f ⁻¹' {c} := by
    intro c
    by_cases hc : c = 0
    · exact ⟨Set.univ, Filter.univ_mem, fun h => (h hc).elim⟩
    have hopen : IsOpen (f ⁻¹' {c}) := hf.1.isOpen_fiber c
    have hcomp : IsCompact (f ⁻¹' {c}) :=
      hcpt.of_isClosed_subset (isClosed_singleton.preimage hf.1.continuous) fun x hx =>
        subset_tsupport f (by
          rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
          simp [Function.mem_support, hx, hc])
    obtain ⟨V, hV, hVsub⟩ := compact_open_separated_mul_left hcomp hopen subset_rfl
    exact ⟨V, hV, fun _ => hVsub⟩
  choose V hV hVsub using hfib
  refine ⟨⋂ c ∈ f '' tsupport f, (V c ∩ (V c)⁻¹), ?_, ?_⟩
  · exact (Filter.biInter_mem hfin).mpr fun c _ => Filter.inter_mem (hV c) (inv_mem_nhds_one G (hV c))
  intro u hu x
  have hmemS : ∀ y, f y ≠ 0 → f y ∈ f '' tsupport f := fun y hy =>
    ⟨y, subset_tsupport f (Function.mem_support.mpr hy), rfl⟩
  by_cases hx : f x = 0
  · by_contra hne
    have hne' : f (u * x) ≠ 0 := by rwa [hx] at hne
    have hd := Set.mem_iInter₂.mp hu _ (hmemS _ hne')
    have hinv : u⁻¹ ∈ V (f (u * x)) := Set.mem_inv.mp hd.2
    have := hVsub _ hne' (Set.mul_mem_mul hinv (show u * x ∈ f ⁻¹' {f (u * x)} from rfl))
    simp only [inv_mul_cancel_left, Set.mem_preimage, Set.mem_singleton_iff] at this
    exact hne' (by rw [← this, hx])
  · have hc := Set.mem_iInter₂.mp hu _ (hmemS _ hx)
    have := hVsub _ hx (Set.mul_mem_mul hc.1 (show x ∈ f ⁻¹' {f x} from rfl))
    simpa using this

omit [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- Every test function is bi-invariant under some compact open subgroup (needs `G` totally
disconnected, e.g. by van Dantzig; stated with an explicit hypothesis that compact open
subgroups form a neighbourhood basis of `1`). -/
theorem exists_biInvariant (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G,
      IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {f : G → ℂ} (hf : f ∈ testFunctions G) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ IsBiInvariant K f := by
  obtain ⟨V₁, hV₁, h₁⟩ := exists_nhds_one_leftInvariant hf
  have hf' : (fun x => f x⁻¹) ∈ testFunctions G :=
    ⟨hf.1.comp_continuous continuous_inv, hf.2.comp_homeomorph (Homeomorph.inv G)⟩
  obtain ⟨V₂, hV₂, h₂⟩ := exists_nhds_one_leftInvariant hf'
  obtain ⟨K, hKo, hKc, hKU⟩ := hG (V₁ ∩ V₂⁻¹) (Filter.inter_mem hV₁ (inv_mem_nhds_one G hV₂))
  refine ⟨K, hKo, hKc, fun k hk g => ⟨h₁ k (hKU hk).1 g, ?_⟩⟩
  have := h₂ k⁻¹ (Set.mem_inv.mp (hKU hk).2) g⁻¹
  simpa [mul_inv_rev] using this

/-- `θ` is a (Harish-Chandra) character of `π` (Thesis Ch. 1): `θ` is locally
integrable and `∫_G θ(g) f(g) dg = tr π(f)` for every test function `f`. -/
def IsCharacterOf (π : UnitaryRep G) (θ : G → ℂ) : Prop :=
  LocallyIntegrable θ (Measure.haar : Measure G) ∧
    ∀ f ∈ testFunctions G, ∫ g, θ g * f g ∂(Measure.haar : Measure G) = traceOf π f

/-- The character `θ_π` as a function, normalised to be continuous on `S` (Thesis Ch. 1).
`S` is intended to be the regular semisimple set, where Harish-Chandra's regularity theorem
(a Literature axiom, not assumed here) gives a unique locally constant representative.
Defined by the epsilon pattern; `0` if no such representative exists. -/
noncomputable def characterOn (π : UnitaryRep G) (S : Set G) : G → ℂ :=
  if h : ∃ θ, IsCharacterOf π θ ∧ ContinuousOn θ S then h.choose else 0

omit [T2Space G] in
theorem characterOn_spec (π : UnitaryRep G) (S : Set G)
    (h : ∃ θ, IsCharacterOf π θ ∧ ContinuousOn θ S) :
    IsCharacterOf π (characterOn π S) ∧ ContinuousOn (characterOn π S) S := by
  unfold characterOn
  split_ifs
  exact h.choose_spec

end Characters

/-! ### Unitary equivalence

Everything attached to a representation (irreducibility, temperedness, central characters,
`π(f)`, traces, characters, smooth vectors, equivariant forms, multiplicities) depends only on
its unitary equivalence class. These are the "congr lemmas" used to pass between a tempered
representation and the chosen representative of its class. -/

namespace UnitaryRep

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem IsEquivalent.refl (π : UnitaryRep G) : IsEquivalent π π :=
  ⟨LinearIsometryEquiv.refl ℂ π.H, fun _ _ => rfl⟩

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem IsEquivalent.symm {π π' : UnitaryRep G} (h : IsEquivalent π π') : IsEquivalent π' π := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U.symm, fun g v => U.injective ?_⟩
  rw [hU, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem IsEquivalent.trans {π π' π'' : UnitaryRep G} (h : IsEquivalent π π')
    (h' : IsEquivalent π' π'') : IsEquivalent π π'' := by
  obtain ⟨U, hU⟩ := h
  obtain ⟨U', hU'⟩ := h'
  exact ⟨U.trans U', fun g v => by simp [hU, hU']⟩

/-- Unitary equivalence is an equivalence relation (Thesis §3.1); the classes are the points of
the unitary dual. -/
instance equivSetoid : Setoid (UnitaryRep G) :=
  ⟨IsEquivalent, ⟨IsEquivalent.refl, IsEquivalent.symm, IsEquivalent.trans⟩⟩

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem equiv_iff {π π' : UnitaryRep G} : π ≈ π' ↔ IsEquivalent π π' := Iff.rfl

/-- The inverse of an intertwiner is an intertwiner. -/
theorem symm_intertwines {π π' : UnitaryRep G} (U : π.H ≃ₗᵢ[ℂ] π'.H)
    (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) (g : G) (w : π'.H) :
    U.symm (π'.ρ g w) = π.ρ g (U.symm w) := by
  apply U.injective
  rw [hU, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem IsIrreducible.of_equiv {π π' : UnitaryRep G} (hπ : π.IsIrreducible)
    (h : IsEquivalent π π') : π'.IsIrreducible := by
  obtain ⟨U, hU⟩ := h
  obtain ⟨hnt, hirr⟩ := hπ
  refine ⟨U.symm.toEquiv.nontrivial, fun W hW hinv => ?_⟩
  let W₀ : Submodule ℂ π.H := W.comap (U.toLinearEquiv : π.H →ₗ[ℂ] π'.H)
  have hW₀ : IsClosed (W₀ : Set π.H) := hW.preimage U.continuous
  have hinv₀ : ∀ g, ∀ v ∈ W₀, π.ρ g v ∈ W₀ := fun g v hv => by
    change U (π.ρ g v) ∈ W
    rw [hU]
    exact hinv g _ hv
  rcases hirr W₀ hW₀ hinv₀ with h0 | h0
  · left
    rw [Submodule.eq_bot_iff] at h0 ⊢
    intro w hw
    have : U.symm w ∈ W₀ := by
      change U (U.symm w) ∈ W
      simpa using hw
    have := h0 _ this
    simpa using congrArg U this
  · right
    rw [Submodule.eq_top_iff'] at h0 ⊢
    intro w
    have : U (U.symm w) ∈ W := h0 (U.symm w)
    simpa using this

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem isIrreducible_congr {π π' : UnitaryRep G} (h : IsEquivalent π π') :
    π.IsIrreducible ↔ π'.IsIrreducible :=
  ⟨fun hπ => hπ.of_equiv h, fun hπ => hπ.of_equiv h.symm⟩

end UnitaryRep

open UnitaryRep

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem WeaklyContainedIn.of_equiv {π π' σ : UnitaryRep G} (h : WeaklyContainedIn π σ)
    (he : IsEquivalent π π') : WeaklyContainedIn π' σ := by
  obtain ⟨U, hU⟩ := he
  intro v K hK ε hε
  obtain ⟨n, w, hw⟩ := h (U.symm v) K hK ε hε
  refine ⟨n, w, fun g hg => ?_⟩
  have : ⟪π'.ρ g v, v⟫_ℂ = ⟪π.ρ g (U.symm v), U.symm v⟫_ℂ := by
    rw [← LinearIsometryEquiv.inner_map_map U, hU, LinearIsometryEquiv.apply_symm_apply]
  rw [this]
  exact hw g hg

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem weaklyContainedIn_congr {π π' σ : UnitaryRep G} (he : IsEquivalent π π') :
    WeaklyContainedIn π σ ↔ WeaklyContainedIn π' σ :=
  ⟨fun h => h.of_equiv he, fun h => h.of_equiv he.symm⟩

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem isTempered_congr [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] {π π' : UnitaryRep G} (he : IsEquivalent π π') :
    IsTempered π ↔ IsTempered π' := by
  unfold IsTempered
  rw [isIrreducible_congr he, weaklyContainedIn_congr he]

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem HasCentralChar.of_equiv {π π' : UnitaryRep G} {A : Subgroup G} {χ : ↥A → ℂ}
    (h : HasCentralChar π A χ) (he : IsEquivalent π π') : HasCentralChar π' A χ := by
  obtain ⟨U, hU⟩ := he
  intro a
  refine ContinuousLinearMap.ext fun w => ?_
  have := symm_intertwines U hU (a : G) w
  apply U.symm.injective
  rw [this, h a]
  simp

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem hasCentralChar_congr {π π' : UnitaryRep G} {A : Subgroup G} {χ : ↥A → ℂ}
    (he : IsEquivalent π π') : HasCentralChar π A χ ↔ HasCentralChar π' A χ :=
  ⟨fun h => h.of_equiv he, fun h => h.of_equiv he.symm⟩

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem isTrivialOn_congr {π π' : UnitaryRep G} {S : Set G} (he : IsEquivalent π π') :
    IsTrivialOn π S ↔ IsTrivialOn π' S := by
  have key : ∀ {σ σ' : UnitaryRep G}, IsEquivalent σ σ' → IsTrivialOn σ S → IsTrivialOn σ' S := by
    rintro σ σ' ⟨U, hU⟩ h s hs
    refine ContinuousLinearMap.ext fun w => ?_
    apply U.symm.injective
    rw [symm_intertwines U hU s w, h s hs]
    rfl
  exact ⟨key he, key he.symm⟩

/-! ### Central characters of irreducible representations -/

namespace HasCentralChar

variable {π : UnitaryRep G} {A : Subgroup G} {χ : ↥A → ℂ}

private lemma smul_eq (h : HasCentralChar π A χ) (a : ↥A) (v : π.H) : π.ρ a v = χ a • v := by
  rw [h a]; rfl

/-- On a nonzero representation the central character is multiplicative. -/
theorem mul [Nontrivial π.H] (h : HasCentralChar π A χ) (a b : ↥A) : χ (a * b) = χ a * χ b := by
  obtain ⟨v, hv⟩ := exists_ne (0 : π.H)
  apply smul_left_injective ℂ hv
  simp only
  rw [← h.smul_eq, mul_smul, ← h.smul_eq, ← h.smul_eq, Subgroup.coe_mul, map_mul]
  rfl

/-- On a nonzero representation the central character is trivial at `1`. -/
theorem map_one [Nontrivial π.H] (h : HasCentralChar π A χ) : χ 1 = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : π.H)
  apply smul_left_injective ℂ hv
  simp only
  change χ 1 • v = 1 • v
  rw [← h.smul_eq, one_smul]
  simp

/-- On a nonzero unitary representation the central character is unitary. -/
theorem norm_eq_one [Nontrivial π.H] (h : HasCentralChar π A χ) (a : ↥A) : ‖χ a‖ = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : π.H)
  have h1 : ‖π.ρ a v‖ = ‖v‖ := ContinuousLinearMap.norm_map_of_mem_unitary (π.unitary_ρ a) v
  rw [h.smul_eq, norm_smul] at h1
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have := mul_right_cancel₀ hv' (h1.trans (one_mul _).symm)
  exact this

/-- The central character is continuous: `χ(a) = ⟪v, ρ(a) v⟫ / ‖v‖²` for any `v ≠ 0`, and
`a ↦ ρ(a) v` is continuous. -/
theorem continuous [Nontrivial π.H] (h : HasCentralChar π A χ) : Continuous χ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : π.H)
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hv
  have hχ : χ = fun a : ↥A => ⟪v, π.ρ a v⟫_ℂ / ⟪v, v⟫_ℂ := by
    funext a
    rw [h.smul_eq, inner_smul_right, mul_div_assoc, div_self hvv, mul_one]
  rw [hχ]
  exact (continuous_const.inner ((π.strongCont v).comp continuous_subtype_val)).div_const _

/-- Irreducible versions of the three facts above. -/
theorem mul_of_irreducible (hπ : π.IsIrreducible) (h : HasCentralChar π A χ) (a b : ↥A) :
    χ (a * b) = χ a * χ b :=
  haveI := hπ.1; h.mul a b

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem norm_eq_one_of_irreducible (hπ : π.IsIrreducible) (h : HasCentralChar π A χ) (a : ↥A) :
    ‖χ a‖ = 1 :=
  haveI := hπ.1; h.norm_eq_one a

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem continuous_of_irreducible (hπ : π.IsIrreducible) (h : HasCentralChar π A χ) :
    Continuous χ :=
  haveI := hπ.1; h.continuous

end HasCentralChar

/-! ### Transport of submodules along a linear equivalence -/

section Transport

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

/-- If `x ∈ p ↔ e x ∈ q` for all `x`, then `e` maps `p` onto `q`. -/
theorem submodule_map_equiv_eq_of_forall_mem_iff (e : M ≃ₗ[ℂ] N) {p : Submodule ℂ M}
    {q : Submodule ℂ N} (h : ∀ x, x ∈ p ↔ e x ∈ q) : p.map (e : M →ₗ[ℂ] N) = q := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).1 hx
  · intro hy
    exact ⟨e.symm y, (h _).2 (by simpa using hy), by simp⟩

/-- The restriction of `e` to `p ≃ q`, when `x ∈ p ↔ e x ∈ q`. -/
noncomputable def equivOfForallMemIff (e : M ≃ₗ[ℂ] N) {p : Submodule ℂ M} {q : Submodule ℂ N}
    (h : ∀ x, x ∈ p ↔ e x ∈ q) : ↥p ≃ₗ[ℂ] ↥q :=
  e.ofSubmodules p q (submodule_map_equiv_eq_of_forall_mem_iff e h)

@[simp]
theorem equivOfForallMemIff_apply (e : M ≃ₗ[ℂ] N) {p : Submodule ℂ M} {q : Submodule ℂ N}
    (h : ∀ x, x ∈ p ↔ e x ∈ q) (x : ↥p) : (equivOfForallMemIff e h x : N) = e x := rfl

end Transport

/-! ### Invariance of `π(f)`, traces and characters -/

section TraceCongr

variable {π π' : UnitaryRep G}

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem mem_fixedSpace_iff_of_intertwines (U : π.H ≃ₗᵢ[ℂ] π'.H)
    (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) (K : Subgroup G) (v : π.H) :
    v ∈ fixedSpace π K ↔ U v ∈ fixedSpace π' K := by
  constructor
  · intro hv k hk
    rw [← hU, hv k hk]
  · intro hv k hk
    apply U.injective
    rw [hU, hv k hk]

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem OpIntegrable.of_intertwines (U : π.H ≃ₗᵢ[ℂ] π'.H)
    (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) {f : G → ℂ} (hf : OpIntegrable π f) :
    OpIntegrable π' f := by
  intro w
  have : (fun g => f g • π'.ρ g w) = fun g => U (f g • π.ρ g (U.symm w)) := by
    funext g
    rw [map_smul, hU, LinearIsometryEquiv.apply_symm_apply]
  rw [this]
  exact (U.toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp (hf _)

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem opIntegrable_congr (U : π.H ≃ₗᵢ[ℂ] π'.H) (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v))
    (f : G → ℂ) : OpIntegrable π f ↔ OpIntegrable π' f :=
  ⟨OpIntegrable.of_intertwines U hU,
    OpIntegrable.of_intertwines U.symm (UnitaryRep.symm_intertwines U hU)⟩

/-- A unitary intertwiner conjugates `π(f)` into `π'(f)`. -/
theorem opOf_intertwines (U : π.H ≃ₗᵢ[ℂ] π'.H) (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v))
    (f : G → ℂ) (v : π.H) : opOf π' f (U v) = U (opOf π f v) := by
  by_cases hf : OpIntegrable π f
  · have hf' := hf.of_intertwines U hU
    rw [opOf_apply π hf, opOf_apply π' hf']
    have := LinearIsometry.integral_comp_comm (μ := (Measure.haar : Measure G)) U.toLinearIsometry
      (fun g => f g • π.ρ g v)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry, map_smul, hU] at this
    exact this
  · have hf' : ¬ OpIntegrable π' f := fun h => hf ((opIntegrable_congr U hU f).2 h)
    simp [opOf_of_not_opIntegrable π hf, opOf_of_not_opIntegrable π' hf']

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem TraceDatum.of_intertwines (U : π.H ≃ₗᵢ[ℂ] π'.H) (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v))
    {f : G → ℂ} {K : Subgroup G} (hK : TraceDatum π f K) : TraceDatum π' f K := by
  obtain ⟨hKo, hKc, hbi, hfin, hpres⟩ := hK
  have hmem := mem_fixedSpace_iff_of_intertwines U hU K
  let e : ↥(fixedSpace π K) ≃ₗ[ℂ] ↥(fixedSpace π' K) :=
    equivOfForallMemIff U.toLinearEquiv hmem
  refine ⟨hKo, hKc, hbi, LinearEquiv.finiteDimensional e, fun w hw => ?_⟩
  have hw' : U.symm w ∈ fixedSpace π K := (hmem _).2 (by simpa using hw)
  have := (hmem _).1 (hpres _ hw')
  rwa [← opOf_intertwines U hU, LinearIsometryEquiv.apply_symm_apply] at this

/-- `tr π(f)` is an invariant of the unitary equivalence class. -/
theorem traceOf_congr (h : IsEquivalent π π') (f : G → ℂ) : traceOf π f = traceOf π' f := by
  obtain ⟨U, hU⟩ := h
  by_cases hex : ∃ K : Subgroup G, TraceDatum π f K
  · obtain ⟨K, hK⟩ := hex
    have hK' := hK.of_intertwines U hU
    rw [traceOf_eq π f K hK, traceOf_eq π' f K hK']
    have : FiniteDimensional ℂ ↥(fixedSpace π K) := hK.2.2.2.1
    let e : ↥(fixedSpace π K) ≃ₗ[ℂ] ↥(fixedSpace π' K) :=
      equivOfForallMemIff U.toLinearEquiv (mem_fixedSpace_iff_of_intertwines U hU K)
    have hconj : (opOf π' f).toLinearMap.restrict hK'.2.2.2.2 =
        e.conj ((opOf π f).toLinearMap.restrict hK.2.2.2.2) := by
      ext w
      simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, LinearMap.coe_restrict_apply, ContinuousLinearMap.coe_coe]
      have hsymm : ((e.symm w : ↥(fixedSpace π K)) : π.H) = U.symm (w : π'.H) := by
        apply U.injective
        rw [LinearIsometryEquiv.apply_symm_apply]
        exact (equivOfForallMemIff_apply U.toLinearEquiv _ (e.symm w)).symm.trans
          (by rw [LinearEquiv.apply_symm_apply])
      rw [equivOfForallMemIff_apply]
      change opOf π' f (w : π'.H) = U (opOf π f (e.symm w : π.H))
      rw [hsymm, ← opOf_intertwines U hU, LinearIsometryEquiv.apply_symm_apply]
    rw [hconj, LinearMap.trace_conj']
  · have hex' : ¬ ∃ K : Subgroup G, TraceDatum π' f K := by
      rintro ⟨K, hK⟩
      exact hex ⟨K, hK.of_intertwines U.symm (UnitaryRep.symm_intertwines U hU)⟩
    simp only [traceOf, hex, hex', dite_false]

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem isCharacterOf_congr (h : IsEquivalent π π') : IsCharacterOf π = IsCharacterOf π' := by
  funext θ
  unfold IsCharacterOf
  simp_rw [traceOf_congr h]

/-- The character `θ_π` (normalised on `S`) is an invariant of the unitary equivalence class:
the defining predicates are equal, so the `choose`s coincide. -/
theorem characterOn_congr (h : IsEquivalent π π') (S : Set G) :
    characterOn π S = characterOn π' S := by
  have hc := isCharacterOf_congr h
  unfold characterOn
  rw [hc]

end TraceCongr

/-! ### Invariance of smooth vectors, equivariant forms and multiplicities -/

section MultCongr

variable [IsTopologicalGroup G] {π π' : UnitaryRep G}

omit [IsTopologicalGroup G] in
/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem mem_smoothVectors_of_intertwines (U : π.H ≃ₗᵢ[ℂ] π'.H)
    (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) {v : π.H} (hv : v ∈ smoothVectors π) :
    U v ∈ smoothVectors π' := by
  obtain ⟨K, hK, hfix⟩ := hv
  exact ⟨K, hK, fun k hk => by rw [← hU, hfix k hk]⟩

omit [IsTopologicalGroup G] in
/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem mem_smoothVectors_iff_of_intertwines (U : π.H ≃ₗᵢ[ℂ] π'.H)
    (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) (v : π.H) :
    v ∈ smoothVectors π ↔ U v ∈ smoothVectors π' := by
  refine ⟨mem_smoothVectors_of_intertwines U hU, fun hv => ?_⟩
  have := mem_smoothVectors_of_intertwines U.symm (UnitaryRep.symm_intertwines U hU) hv
  simpa using this

/-- The isomorphism `π^∞ ≃ π'^∞` induced by a unitary intertwiner. -/
noncomputable def smoothEquiv (U : π.H ≃ₗᵢ[ℂ] π'.H) (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) :
    ↥(smoothVectors π) ≃ₗ[ℂ] ↥(smoothVectors π') :=
  equivOfForallMemIff U.toLinearEquiv (mem_smoothVectors_iff_of_intertwines U hU)

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem smoothEquiv_smoothAction (U : π.H ≃ₗᵢ[ℂ] π'.H)
    (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) (g : G) (v : ↥(smoothVectors π)) :
    smoothEquiv U hU (smoothAction π g v) = smoothAction π' g (smoothEquiv U hU v) :=
  Subtype.ext (hU g v)

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem mem_equivariantForms_iff_of_intertwines (U : π.H ≃ₗᵢ[ℂ] π'.H)
    (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) (S : Subgroup G) (ξ : ↥S → ℂ)
    (ℓ : Module.Dual ℂ ↥(smoothVectors π')) :
    ℓ ∈ equivariantForms π' S ξ ↔ (smoothEquiv U hU).dualMap ℓ ∈ equivariantForms π S ξ := by
  set e := smoothEquiv U hU
  constructor
  · intro hℓ s v
    simp only [LinearEquiv.dualMap_apply]
    rw [smoothEquiv_smoothAction, hℓ s]
  · intro hℓ s w
    have := hℓ s (e.symm w)
    simp only [LinearEquiv.dualMap_apply] at this
    rwa [smoothEquiv_smoothAction, LinearEquiv.apply_symm_apply] at this

/-- `Hom_S(π^∞, ξ) ≅ Hom_S(π'^∞, ξ)` for unitarily equivalent `π, π'`. -/
noncomputable def equivariantFormsEquiv (U : π.H ≃ₗᵢ[ℂ] π'.H)
    (hU : ∀ g v, U (π.ρ g v) = π'.ρ g (U v)) (S : Subgroup G) (ξ : ↥S → ℂ) :
    ↥(equivariantForms π' S ξ) ≃ₗ[ℂ] ↥(equivariantForms π S ξ) :=
  equivOfForallMemIff (smoothEquiv U hU).dualMap
    (mem_equivariantForms_iff_of_intertwines U hU S ξ)

/-- The multiplicity `m(π)` is an invariant of the unitary equivalence class. -/
theorem multiplicity_congr (h : IsEquivalent π π') (S : Subgroup G) (ξ : ↥S → ℂ) :
    multiplicity π S ξ = multiplicity π' S ξ := by
  obtain ⟨U, hU⟩ := h
  unfold multiplicity
  rw [(equivariantFormsEquiv U hU S ξ).rank_eq]

/-- Invariance under unitary equivalence (Thesis §3.1). -/
theorem hasModel_congr (h : IsEquivalent π π') (S : Subgroup G) (ξ : ↥S → ℂ) :
    HasModel π S ξ ↔ HasModel π' S ξ := by
  rw [hasModel_iff_multiplicity_ne_zero, hasModel_iff_multiplicity_ne_zero,
    multiplicity_congr h]

end MultCongr

/-! ### Separation by test functions

On a totally disconnected locally compact group the test functions `C_c^∞(G)` separate locally
integrable functions: compact open sets form a basis, and `∫_K θ` over a compact `K` is a limit
of integrals over compact open neighbourhoods of `K` (outer regularity). This is what makes the
Harish-Chandra character `θ_π` (and `θ_f`) unique as a function up to null sets. -/

section Separation

/-- In a totally disconnected locally compact Hausdorff space, between a compact set and an
open neighbourhood of it there is a compact open (hence clopen) set. -/
theorem exists_isCompact_isClopen_between {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [TotallyDisconnectedSpace X] {K U : Set X} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) : ∃ V, IsCompact V ∧ IsClopen V ∧ K ⊆ V ∧ V ⊆ U := by
  have hloc : ∀ x ∈ K, ∃ W : Set X, IsCompact W ∧ IsClopen W ∧ x ∈ W ∧ W ⊆ U := by
    intro x hx
    obtain ⟨C, hC, hxC, hCU⟩ := exists_compact_subset hU (hKU hx)
    obtain ⟨W, hW, hxW, hWC⟩ :=
      isTopologicalBasis_isClopen.mem_nhds_iff.mp (isOpen_interior.mem_nhds hxC)
    exact ⟨W, hC.of_isClosed_subset hW.1 (hWC.trans interior_subset), hW, hxW,
      hWC.trans (interior_subset.trans hCU)⟩
  choose! W hWc hWcl hxW hWU using hloc
  obtain ⟨t, htK, hcover⟩ :=
    hK.elim_nhds_subcover W (fun x hx => (hWcl x hx).isOpen.mem_nhds (hxW x hx))
  exact ⟨⋃ x ∈ t, W x, t.isCompact_biUnion fun x hx => hWc x (htK x hx),
    isClopen_biUnion_finset fun x hx => hWcl x (htK x hx), hcover,
    Set.iUnion₂_subset fun x hx => hWU x (htK x hx)⟩

/-- The indicator function of a compact open set is a test function. -/
theorem indicator_mem_testFunctions [T2Space G] {V : Set G} (hVc : IsCompact V)
    (hVo : IsClopen V) : V.indicator (1 : G → ℂ) ∈ testFunctions G := by
  refine ⟨?_, ?_⟩
  · rw [← LocallyConstant.coe_charFn ℂ hVo]
    exact (LocallyConstant.charFn ℂ hVo).isLocallyConstant
  · exact HasCompactSupport.intro' hVc hVc.isClosed fun x hx => Set.indicator_of_notMem hx _

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G]
  [BorelSpace G]

/-- Separation lemma, for a general outer regular measure finite on compacts: on a totally
disconnected, locally compact, σ-compact group, a locally integrable `θ` with `∫ θ f = 0` for all
test functions `f` vanishes almost everywhere.

σ-compactness is needed: for a non-σ-compact group Haar measure is not σ-finite and "locally
null" no longer implies "null" (it holds for `GSpin(F)`, a closed subgroup of `GL_N(F)`). -/
theorem ae_eq_zero_of_integral_testFunctions' [SigmaCompactSpace G] {μ : Measure G}
    [IsFiniteMeasureOnCompacts μ] [μ.OuterRegular] {θ : G → ℂ} (hθ : LocallyIntegrable θ μ)
    (h : ∀ f ∈ testFunctions G, ∫ g, θ g * f g ∂μ = 0) : θ =ᵐ[μ] 0 := by
  -- step 1: `∫_V θ = 0` for compact open `V`
  have hVint : ∀ V : Set G, IsCompact V → IsClopen V → ∫ g in V, θ g ∂μ = 0 := by
    intro V hVc hVo
    have := h _ (indicator_mem_testFunctions hVc hVo)
    have heq : (fun g => θ g * V.indicator (1 : G → ℂ) g) = V.indicator θ := by
      funext g
      by_cases hg : g ∈ V <;> simp [hg]
    rw [heq, integral_indicator hVo.isClosed.measurableSet] at this
    exact this
  -- step 2: `∫_K θ = 0` for compact `K`, by outer regularity
  refine ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' hθ fun K hK => ?_
  have hμK : μ K < ∞ := hK.measure_lt_top
  have hU : ∀ n : ℕ, ∃ U, U ⊇ K ∧ IsOpen U ∧ μ U < μ K + (n : ℝ≥0∞)⁻¹ := fun n =>
    K.exists_isOpen_lt_of_lt _
      (ENNReal.lt_add_right hμK.ne (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n)))
  choose U hKU hUo hUμ using hU
  have hV : ∀ n, ∃ V : Set G, IsCompact V ∧ IsClopen V ∧ K ⊆ V ∧ V ⊆ U n := fun n =>
    exists_isCompact_isClopen_between hK (hUo n) (hKU n)
  choose V hVc hVo hKV hVU using hV
  set W : ℕ → Set G := fun n => ⋂ i ∈ Finset.range (n + 1), V i with hWdef
  have hWo : ∀ n, IsClopen (W n) := fun n => isClopen_biInter_finset fun i _ => hVo i
  have hWV : ∀ n, ∀ i ≤ n, W n ⊆ V i := fun n i hi =>
    Set.biInter_subset_of_mem (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  have hWc : ∀ n, IsCompact (W n) := fun n =>
    (hVc 0).of_isClosed_subset (hWo n).isClosed (hWV n 0 (Nat.zero_le n))
  have hanti : Antitone W := fun m n hmn =>
    Set.biInter_subset_biInter_left fun i hi => by
      simp only [Finset.coe_range, Set.mem_Iio] at hi ⊢; omega
  have hlim := tendsto_setIntegral_of_antitone (μ := μ) (f := θ)
    (fun n => (hWo n).isClosed.measurableSet) hanti ⟨0, hθ.integrableOn_isCompact (hWc 0)⟩
  have hzero : (fun n => ∫ x in W n, θ x ∂μ) = fun _ => 0 :=
    funext fun n => hVint (W n) (hWc n) (hWo n)
  rw [hzero] at hlim
  have h0 : ∫ x in ⋂ n, W n, θ x ∂μ = 0 := tendsto_nhds_unique hlim tendsto_const_nhds
  -- step 3: `⋂ W n` and `K` differ by a null set
  have hKW : K ⊆ ⋂ n, W n :=
    Set.subset_iInter fun n => Set.subset_iInter₂ fun i _ => hKV i
  have hnull : μ ((⋂ n, W n) \ K) = 0 := by
    have hle : ∀ n : ℕ, μ ((⋂ n, W n) \ K) ≤ (n : ℝ≥0∞)⁻¹ := by
      intro n
      calc μ ((⋂ n, W n) \ K) ≤ μ (U n \ K) :=
            measure_mono (Set.sdiff_subset_sdiff_left
              ((Set.iInter_subset _ n).trans ((hWV n n le_rfl).trans (hVU n))))
        _ = μ (U n) - μ K := measure_sdiff (hKU n) hK.measurableSet.nullMeasurableSet hμK.ne
        _ ≤ (n : ℝ≥0∞)⁻¹ := (ENNReal.sub_lt_of_lt_add (measure_mono (hKU n)) (by rw [add_comm]; exact hUμ n)).le
    exact le_antisymm (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero hle) bot_le
  have hae : (⋂ n, W n : Set G) =ᵐ[μ] K := by
    refine (ae_eq_set.2 ⟨hnull, ?_⟩)
    rw [Set.sdiff_eq_empty.2 hKW, measure_empty]
  rw [← setIntegral_congr_set hae, h0]

/-- Separation lemma for Haar measure: on a totally disconnected, locally
compact, σ-compact group (e.g. `GSpin(F)` for `p`-adic `F`), a locally integrable `θ` with
`∫_G θ(g) f(g) dg = 0` for every `f ∈ C_c^∞(G)` vanishes almost everywhere. In particular a
Harish-Chandra character (Thesis Ch. 1) is determined up to null sets by `π`. -/
theorem ae_eq_zero_of_integral_testFunctions [IsTopologicalGroup G] [SigmaCompactSpace G]
    {θ : G → ℂ} (hθ : LocallyIntegrable θ (Measure.haar : Measure G))
    (h : ∀ f ∈ testFunctions G, ∫ g, θ g * f g ∂(Measure.haar : Measure G) = 0) :
    θ =ᵐ[(Measure.haar : Measure G)] 0 :=
  ae_eq_zero_of_integral_testFunctions' hθ h

/-- Two locally integrable functions with the same integrals against all test functions agree
almost everywhere (Haar measure). -/
theorem ae_eq_of_integral_testFunctions [IsTopologicalGroup G] [SigmaCompactSpace G]
    {θ θ' : G → ℂ} (hθ : LocallyIntegrable θ (Measure.haar : Measure G))
    (hθ' : LocallyIntegrable θ' (Measure.haar : Measure G))
    (h : ∀ f ∈ testFunctions G, ∫ g, θ g * f g ∂(Measure.haar : Measure G) =
      ∫ g, θ' g * f g ∂(Measure.haar : Measure G)) :
    θ =ᵐ[(Measure.haar : Measure G)] θ' := by
  have hint : ∀ {φ : G → ℂ}, LocallyIntegrable φ (Measure.haar : Measure G) →
      ∀ f ∈ testFunctions G, Integrable (fun g => φ g * f g) (Measure.haar : Measure G) := by
    intro φ hφ f hf
    simpa [mul_comm] using
      hφ.integrable_smul_left_of_hasCompactSupport hf.1.continuous hf.2
  have := ae_eq_zero_of_integral_testFunctions (hθ.sub hθ') fun f hf => by
    simp only [Pi.sub_apply, sub_mul]
    rw [integral_sub (hint hθ f hf) (hint hθ' f hf), h f hf, sub_self]
  filter_upwards [this] with g hg
  exact sub_eq_zero.mp hg

/-- Two characters of the same representation agree almost everywhere. -/
theorem IsCharacterOf.ae_eq [IsTopologicalGroup G] [SigmaCompactSpace G] {π : UnitaryRep G}
    {θ θ' : G → ℂ} (hθ : IsCharacterOf π θ) (hθ' : IsCharacterOf π θ') :
    θ =ᵐ[(Measure.haar : Measure G)] θ' :=
  ae_eq_of_integral_testFunctions hθ.1 hθ'.1 fun f hf => by rw [hθ.2 f hf, hθ'.2 f hf]

end Separation

end GSpinGGP
