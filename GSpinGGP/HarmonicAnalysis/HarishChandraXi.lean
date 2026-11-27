/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import TauCeti.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Group.ModularCharacter
import GSpinGGP.Literature.Parabolic

/-!
# Harish-Chandra's function `Ξ` for an Iwasawa pair

Harish-Chandra's function is defined (Waldspurger, *La formule de Plancherel pour les groupes
`p`-adiques*, J. Inst. Math. Jussieu 2 (2003), §II.1, pp. 250–251; BP §1.5) from a minimal
parabolic subgroup `P₀` and a compact subgroup `K` with `G = P₀ K`:

  `Ξ(g) = ∫_K δ₀(p₀(kg))^{1/2} dk`,   `dk` the probability Haar measure of `K`,

where `g = p₀(g) k₀(g)` with `p₀(g) ∈ P₀`, `k₀(g) ∈ K`.  Only the decomposition `G = P₀ K`
enters the definition, so this file works for any locally compact group `G`, closed subgroup
`P`, and compact open subgroup `K` with `G = P K` (an `IwasawaPair`).  Harish-Chandra's `Ξ^G` of
`G = GSpin(W) × GSpin(V)` (`GGPData.IwasawaDatum.xiHC`, `TraceFormula/Analytic.lean`) is the `Ξ`
of such a pair; `Ξ^M` for a Levi subgroup `M` and `Ξ^H` for `H = GSpin(W)` would be the `Ξ` of
pairs of `M` and `H` (not built here).

## Main definitions

* `IwasawaDecomp G`: closed `P`, compact `K`, `G = P K`; the choice of components `iwP`, `iwK`
  and the extension `extend` of functions on `P` along `G = P K`.
* `IwasawaPair G`: an `IwasawaDecomp` with `K` open.
* `IwasawaPair.delta`: the modular character `δ_P` of `P` (Mathlib's `modularCharacter`,
  `μ(E p⁻¹) = δ_P(p) μ(E)`, which is `|det Ad(p)|_{𝔲}|` for `P = M U`, as in Waldspurger 2003
  §I.1); `IwasawaPair.rho g = δ_P(p(g))` (independent of the choice of `p(g)`).
* `IwasawaPair.xi`: `Ξ(g) = ∫_K δ_P(p(kg))^{1/2} dk` (normalized Haar measure on `K`).

## Main results

* Modular characters: trivial on a compact open subgroup and on central elements, locally
  constant, bounded below on compact sets (`modularCharacter_eq_one_of_mem`, …).
* `IwasawaPair.rho_mul`: the cocycle relation `δ(p(xy)) = δ(p(x)) δ(p(k(x) y))`.
* `IwasawaPair.xi_mul_left_mem_K`, `xi_mul_right_mem_K`: `Ξ` is bi-`K`-invariant
  (Waldspurger 2003, Lemme II.1.1, first assertion); `IwasawaPair.xi_pos`: `Ξ > 0`.
* **Doubling principle** `IwasawaPair.integral_xi_mul_mul`: `∫_K Ξ(g₁ k g₂) dk = Ξ(g₁) Ξ(g₂)`
  (Waldspurger 2003, Lemme II.1.3; BP Prop 1.5.1(vi)).  Proved for every Iwasawa pair, not only
  for a special maximal compact `K`: the printed proof uses only that the `K`-fixed vectors of
  `i_{P}^G 1` form a line, i.e. `G = P K`; the proof here is a direct computation with the
  cocycle relation and the left invariance of `dk`.
* **Independence of `K`** `IwasawaPair.exists_xi_equiv`: for two Iwasawa pairs `(P, K)`, `(P, K')`
  with the same `P`, `c Ξ_{K'} ≤ Ξ_K ≤ C Ξ_{K'}` for constants `c, C > 0`, for any compact open
  `K`, `K'` (BP §1.5, p. 24, remarks without proof that other choices, with `K` special maximal
  compact, give equivalent functions).
  Ingredients: `ρ_K ≤ C ρ_{K'}` (`rho_le_mul_rho`: the ratio is left `P`-invariant, hence
  determined by its values on the compact `K`), and the proportionality of the `K`- and
  `K'`-integrals on `δ_P`-equivariant functions (`exists_integral_K_eq_mul`).
* `IwasawaPair.integral_K_mul_right`: for continuous `φ` with `φ(p x) = δ_P(p) φ(x)` and `G`
  unimodular, `∫_K φ(k g) dk = ∫_K φ(k) dk`.

The last two use the integration formula for `G = P K` (Bourbaki, the literature axiom
`integral_eq_mul_integral_compact_integral`, `Literature/Parabolic.lean`), hence assume `G`
Hausdorff and second countable.  The rest of the file needs only Mathlib and Tau Ceti.

## Not here

The estimates of Waldspurger 2003 Lemme II.1.1 (second assertion), II.1.5, II.1.6, II.4.4 and
Prop II.4.5 are stated by Waldspurger for `K` the fixer of a special point of the apartment of a
maximal split torus `A₀ ⊆ P₀`, `σ` the log-norm of an embedding `τ : G → GL_n` with
`τ(K) ⊆ GL_n(𝒪)`, and `M̄₀⁺` defined through `H₀` and the simple roots.  They are not stated here.
The comparison `Ξ_K ≤ C Ξ_{K'}` (`exists_xi_le_mul_xi`) transfers such estimates from one `K` to
another with the same `P`.
-/

open MeasureTheory Topology Filter

noncomputable section

namespace GSpinGGP

/-! ## 0. Modular characters -/

section ModularCharacter

variable {G₀ : Type*} [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀]
  [LocallyCompactSpace G₀]

/-- The modular character is trivial on a compact open subgroup `E` (right translation by
`k ∈ E` maps `E`, a set of finite positive Haar measure, to itself). -/
theorem modularCharacter_eq_one_of_mem (E : Subgroup G₀) (hEo : IsOpen (E : Set G₀))
    (hEc : IsCompact (E : Set G₀)) (k : G₀) (hk : k ∈ E) : Measure.modularCharacter k = 1 := by
  borelize G₀
  set μ : Measure G₀ := Measure.haar
  have hcl : closure (E : Set G₀) = E := (Subgroup.isClosed_of_isOpen E hEo).closure_eq
  have h := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure
    (Measure.map (· * k) μ) μ (s := (E : Set G₀)) (by rw [hcl]; exact hEc)
  have hpre : (· * k) ⁻¹' (E : Set G₀) = E := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact ⟨fun hx => by simpa using E.mul_mem hx (E.inv_mem hk), fun hx => E.mul_mem hx hk⟩
  rw [Measure.map_apply (measurable_mul_const k) hEo.measurableSet, hpre] at h
  have hpos : μ E ≠ 0 := (hEo.measure_pos μ ⟨1, E.one_mem⟩).ne'
  have htop : μ E ≠ ⊤ := hEc.measure_lt_top.ne
  have h1 : ((Measure.haarScalarFactor (Measure.map (· * k) μ) μ : NNReal) : ENNReal) = 1 := by
    rw [ENNReal.smul_def, smul_eq_mul] at h
    have h' : 1 * μ E = _ * μ E := (one_mul (μ E)).trans h
    exact ((ENNReal.mul_left_inj hpos htop).mp h').symm
  change Measure.modularCharacterFun k = 1
  rw [Measure.modularCharacterFun_eq_haarScalarFactor μ k]
  exact_mod_cast h1

/-- A function on a topological group that is invariant under right translation by an open
subgroup `K` is locally constant (it is constant on each open coset `xK`). -/
theorem isLocallyConstant_of_mul_right_invariant {G A : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] {K : Subgroup G} (hK : IsOpen (K : Set G)) {f : G → A}
    (hf : ∀ x, ∀ k ∈ K, f (x * k) = f x) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (K : Set G),
    hK.preimage (continuous_const.mul continuous_id), by simp, fun y hy => ?_⟩
  have e : y = x * (x⁻¹ * y) := by group
  rw [e, hf x _ hy]

/-- The modular character is locally constant if there is a compact open subgroup. -/
theorem isLocallyConstant_modularCharacter (E : Subgroup G₀) (hEo : IsOpen (E : Set G₀))
    (hEc : IsCompact (E : Set G₀)) :
    IsLocallyConstant (fun p : G₀ => (Measure.modularCharacter p : ℝ)) := by
  refine isLocallyConstant_of_mul_right_invariant hEo fun x k hk => ?_
  rw [map_mul, modularCharacter_eq_one_of_mem E hEo hEc _ hk, mul_one]

/-- On a compact set, the modular character is bounded below by a positive constant (it is
continuous, `TauCeti.continuous_modularCharacter`, and positive). -/
theorem exists_lowerBound_modularCharacter (S : Set G₀) (hS : IsCompact S) :
    ∃ m : ℝ, 0 < m ∧ ∀ p ∈ S, m ≤ (Measure.modularCharacter p : ℝ) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨p0, -, hmin⟩ :=
    hS.exists_isMinOn hne
      (NNReal.continuous_coe.comp TauCeti.continuous_modularCharacter).continuousOn
  exact ⟨_, by exact_mod_cast Measure.modularCharacterFun_pos p0, fun p hp => hmin hp⟩

/-- The modular character is trivial on central elements. -/
theorem modularCharacter_eq_one_of_central (a : G₀) (ha : ∀ y : G₀, y * a = a * y) :
    Measure.modularCharacter a = 1 := by
  borelize G₀
  have e : (fun y : G₀ => y * a) = fun y => a * y := funext ha
  have hmap : Measure.map (· * a) (Measure.haar : Measure G₀) = Measure.haar := by
    rw [e]
    exact map_mul_left_eq_self (Measure.haar : Measure G₀) a
  change Measure.modularCharacterFun a = 1
  rw [Measure.modularCharacterFun_eq_haarScalarFactor (Measure.haar : Measure G₀) a]
  simp only [hmap, Measure.haarScalarFactor_self]

end ModularCharacter


/-! ## 1. Iwasawa pairs and `Ξ` -/

/-- An **Iwasawa decomposition** `G = P K` in a topological group `G`: a closed subgroup `P` and a
compact subgroup `K` with `G = P K` (Waldspurger 2003 §I.1: `G = P K` for every semi-standard
parabolic `P`, with `K` special maximal compact).  No openness of `K` is assumed, so that the
archimedean case (`K` maximal compact, not open) fits; the refinement with `K` open is
`IwasawaPair`. -/
structure IwasawaDecomp (G : Type*) [Group G] [TopologicalSpace G] where
  /-- the parabolic subgroup -/
  P : Subgroup G
  /-- the compact subgroup -/
  K : Subgroup G
  isClosed_P : IsClosed (P : Set G)
  isCompact_K : IsCompact (K : Set G)
  /-- the Iwasawa decomposition `G = P K` -/
  mul_eq : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k

/-- An **Iwasawa pair** in a topological group `G`: an Iwasawa decomposition `G = P K`
(`IwasawaDecomp`) with `K` open, i.e. a closed subgroup `P` and a compact open subgroup `K` with
`G = P K` (Waldspurger 2003 §I.1: `G = P K` for every semi-standard parabolic `P`, with `K`
special maximal compact; here `K` is any compact open subgroup). -/
structure IwasawaPair (G : Type*) [Group G] [TopologicalSpace G] extends IwasawaDecomp G where
  isOpen_K : IsOpen (K : Set G)

namespace IwasawaDecomp

variable {G : Type*} [Group G] [TopologicalSpace G] (I : IwasawaDecomp G)

instance locallyCompactSpace_P [IsTopologicalGroup G] [LocallyCompactSpace G] :
    LocallyCompactSpace ↥I.P :=
  I.isClosed_P.locallyCompactSpace

instance compactSpace_K : CompactSpace ↥I.K :=
  isCompact_iff_compactSpace.mp I.isCompact_K

/-- `P ∩ K`, as a subgroup of `P`: a compact subgroup (open when `K` is). -/
abbrev KP : Subgroup ↥I.P := I.K.subgroupOf I.P

theorem isCompact_KP : IsCompact (I.KP : Set ↥I.P) :=
  I.isClosed_P.isClosedEmbedding_subtypeVal.isCompact_preimage I.isCompact_K

/-- A choice of `P`-component of `g = p k`. -/
def iwP (g : G) : ↥I.P := ⟨(I.mul_eq g).choose, (I.mul_eq g).choose_spec.1⟩

/-- A choice of `K`-component of `g = p k`. -/
def iwK (g : G) : ↥I.K := ⟨(I.iwP g : G)⁻¹ * g, by
  obtain ⟨k, hk, hg⟩ := (I.mul_eq g).choose_spec.2
  have e : ((I.mul_eq g).choose)⁻¹ * g = k := by rw [inv_mul_eq_iff_eq_mul]; exact hg
  change ((I.mul_eq g).choose)⁻¹ * g ∈ I.K
  rw [e]
  exact hk⟩

theorem iwP_mul_iwK (g : G) : ((I.iwP g : G)) * (I.iwK g : G) = g := by
  simp [iwK]

/-- **Extension along `G = P K`**: `extend h g = h (p(g))` for the chosen decomposition
`g = p(g) k(g)`.  It is independent of the choice when `h` is right invariant under `P ∩ K`
(`extend_mul`); this is how `H_P(g) = H_M(m_P(g))` is defined (Thesis §2.1). -/
def extend {E : Type*} (h : ↥I.P → E) (g : G) : E := h (I.iwP g)

/-- `extend h (p k) = h p`, for `h` right invariant under `P ∩ K`. -/
theorem extend_mul {E : Type*} {h : ↥I.P → E}
    (hh : ∀ (p q : ↥I.P), (q : G) ∈ I.K → h (p * q) = h p) (p : ↥I.P) {k : G} (hk : k ∈ I.K) :
    I.extend h ((p : G) * k) = h p := by
  set p' := I.iwP ((p : G) * k)
  have hmem : ((p'⁻¹ * p : ↥I.P) : G) ∈ I.K := by
    have e : ((p'⁻¹ * p : ↥I.P) : G) = (I.iwK ((p : G) * k) : G) * k⁻¹ := by
      have := I.iwP_mul_iwK ((p : G) * k)
      push_cast
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, this]
      group
    rw [e]
    exact I.K.mul_mem (I.iwK _).property (I.K.inv_mem hk)
  have := hh p' _ hmem
  rw [mul_inv_cancel_left] at this
  exact this.symm

/-- `extend h (g k) = extend h g` for `k ∈ K`, `h` right invariant under `P ∩ K`. -/
theorem extend_mul_right {E : Type*} {h : ↥I.P → E}
    (hh : ∀ (p q : ↥I.P), (q : G) ∈ I.K → h (p * q) = h p) (g : G) {k : G} (hk : k ∈ I.K) :
    I.extend h (g * k) = I.extend h g := by
  conv_lhs => rw [← I.iwP_mul_iwK g, mul_assoc]
  exact I.extend_mul hh _ (I.K.mul_mem (I.iwK g).2 hk)

/-- `extend h (p g) = h p + extend h g` for additive `h`, right invariant under `P ∩ K`. -/
theorem extend_mul_left {E : Type*} [Add E] {h : ↥I.P → E}
    (hh : ∀ (p q : ↥I.P), (q : G) ∈ I.K → h (p * q) = h p)
    (hadd : ∀ p q : ↥I.P, h (p * q) = h p + h q) (p : ↥I.P) (g : G) :
    I.extend h ((p : G) * g) = h p + I.extend h g := by
  conv_lhs => rw [← I.iwP_mul_iwK g, ← mul_assoc]
  rw [show (p : G) * (I.iwP g : G) = ((p * I.iwP g : ↥I.P) : G) from rfl,
    I.extend_mul hh _ (I.iwK g).2, hadd]
  rfl

end IwasawaDecomp

namespace IwasawaPair

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] (I : IwasawaPair G)

omit [IsTopologicalGroup G] [LocallyCompactSpace G] in
theorem isOpen_KP : IsOpen (I.KP : Set ↥I.P) :=
  I.isOpen_K.preimage continuous_subtypeVal

/-- The modular character `δ_P` of `P` (Mathlib's `modularCharacter`: `μ(E p⁻¹) = δ_P(p) μ(E)`
for a left Haar measure `μ`; for `P = M U` this is `|det Ad(p)|_{𝔲}|`, Waldspurger's `δ_P`). -/
def delta (p : ↥I.P) : ℝ := (Measure.modularCharacter p : ℝ)

theorem delta_pos (p : ↥I.P) : 0 < I.delta p := by
  unfold delta
  exact_mod_cast Measure.modularCharacterFun_pos p

theorem delta_mul (p q : ↥I.P) : I.delta (p * q) = I.delta p * I.delta q := by
  unfold delta
  rw [map_mul, NNReal.coe_mul]

theorem delta_inv (p : ↥I.P) : I.delta p⁻¹ = (I.delta p)⁻¹ := by
  unfold delta
  rw [map_inv, NNReal.coe_inv]

/-- `δ_P` is trivial on `P ∩ K`. -/
theorem delta_eq_one_of_mem (k : ↥I.P) (hk : (k : G) ∈ I.K) : I.delta k = 1 := by
  unfold delta
  rw [modularCharacter_eq_one_of_mem I.KP I.isOpen_KP I.isCompact_KP k hk, NNReal.coe_one]

/-- `δ_P(p)` depends only on the coset `p K`: if `p k = p' k'` then `δ_P(p) = δ_P(p')`. -/
theorem delta_eq_of_mul_eq {p p' : ↥I.P} {k k' : G} (hk : k ∈ I.K) (hk' : k' ∈ I.K)
    (h : (p : G) * k = p' * k') : I.delta p = I.delta p' := by
  have hmem : ((p'⁻¹ * p : ↥I.P) : G) ∈ I.K := by
    have e : ((p'⁻¹ * p : ↥I.P) : G) = k' * k⁻¹ := by
      push_cast
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h]
      group
    rw [e]
    exact I.K.mul_mem hk' (I.K.inv_mem hk)
  have := I.delta_eq_one_of_mem _ hmem
  rw [delta_mul, delta_inv] at this
  have hp' := (I.delta_pos p').ne'
  field_simp at this
  exact this

/-- `δ_P` is trivial on central elements of `P`. -/
theorem delta_eq_one_of_central (a : ↥I.P) (ha : ∀ y : ↥I.P, y * a = a * y) : I.delta a = 1 := by
  unfold delta
  rw [modularCharacter_eq_one_of_central a ha, NNReal.coe_one]

/-- On a compact subset of `P`, `δ_P` is bounded below by a positive constant. -/
theorem exists_lowerBound_delta (S : Set ↥I.P) (hS : IsCompact S) :
    ∃ m : ℝ, 0 < m ∧ ∀ p ∈ S, m ≤ I.delta p :=
  exists_lowerBound_modularCharacter S hS

/-- `ρ(g) = δ_P(p(g))`, for `g = p(g) k(g)`. -/
def rho (g : G) : ℝ := I.delta (I.iwP g)

theorem rho_pos (g : G) : 0 < I.rho g := I.delta_pos _

theorem rho_eq_delta {p : ↥I.P} {k g : G} (hk : k ∈ I.K) (hg : g = p * k) :
    I.rho g = I.delta p :=
  I.delta_eq_of_mul_eq (I.iwK g).property hk (by rw [IwasawaDecomp.iwP_mul_iwK, hg])

/-- `ρ(p) = δ_P(p)` on `P`. -/
theorem rho_of_mem (p : ↥I.P) : I.rho p = I.delta p :=
  I.rho_eq_delta I.K.one_mem (mul_one _).symm

theorem rho_mul_right {g k : G} (hk : k ∈ I.K) : I.rho (g * k) = I.rho g :=
  I.rho_eq_delta (I.K.mul_mem (I.iwK g).property hk) 
    (by rw [← mul_assoc, IwasawaDecomp.iwP_mul_iwK])

theorem rho_mul_left (p : ↥I.P) (g : G) : I.rho (p * g) = I.delta p * I.rho g := by
  change _ = I.delta p * I.delta (I.iwP g)
  rw [← I.delta_mul]
  exact I.rho_eq_delta (I.iwK g).property 
    (by rw [Subgroup.coe_mul, mul_assoc, IwasawaDecomp.iwP_mul_iwK])

/-- **The cocycle relation** `δ(p(xy)) = δ(p(x)) δ(p(k(x) y))`. -/
theorem rho_mul (x y : G) : I.rho (x * y) = I.rho x * I.rho ((I.iwK x : G) * y) := by
  conv_lhs => rw [← I.iwP_mul_iwK x, mul_assoc]
  rw [rho_mul_left]
  rfl

theorem isLocallyConstant_rho : IsLocallyConstant I.rho :=
  isLocallyConstant_of_mul_right_invariant I.isOpen_K fun _ _ hk => I.rho_mul_right hk

theorem continuous_rho : Continuous I.rho := I.isLocallyConstant_rho.continuous

variable [MeasurableSpace G] [BorelSpace G]

/-- **Harish-Chandra's function** `Ξ(g) = ∫_K δ_P(p(kg))^{1/2} dk`, `dk` the probability Haar
measure on `K` (Waldspurger 2003 §II.1, p. 251; BP §1.5). -/
def xi (g : G) : ℝ :=
  ((Measure.haar : Measure ↥I.K) Set.univ).toReal⁻¹ *
    ∫ k : ↥I.K, Real.sqrt (I.rho ((k : G) * g)) ∂Measure.haar

omit [LocallyCompactSpace G] in
/-- The total mass of the Haar measure of `K`, as a positive real. -/
theorem haar_K_toReal_pos : 0 < ((Measure.haar : Measure ↥I.K) Set.univ).toReal :=
  ENNReal.toReal_pos (Measure.measure_univ_pos.2 (NeZero.ne _)).ne'
    (measure_ne_top _ _)

omit [MeasurableSpace G] [BorelSpace G] in
theorem continuous_sqrt_rho_mul (g : G) :
    Continuous fun k : ↥I.K => Real.sqrt (I.rho ((k : G) * g)) :=
  Real.continuous_sqrt.comp (I.continuous_rho.comp (continuous_subtypeVal.mul continuous_const))

theorem integrable_sqrt_rho_mul (g : G) :
    Integrable (fun k : ↥I.K => Real.sqrt (I.rho ((k : G) * g))) Measure.haar :=
  (I.continuous_sqrt_rho_mul g).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem xi_nonneg (g : G) : 0 ≤ I.xi g :=
  mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (integral_nonneg fun _ => Real.sqrt_nonneg _)

/-- `Ξ > 0`: the integrand is continuous and positive on the compact group `K`. -/
theorem xi_pos (g : G) : 0 < I.xi g := by
  refine mul_pos (inv_pos.2 I.haar_K_toReal_pos) ?_
  have hcont := I.continuous_sqrt_rho_mul g
  refine (integral_pos_iff_support_of_nonneg (fun _ => Real.sqrt_nonneg _)
    (I.integrable_sqrt_rho_mul g)).2 ?_
  have hsupp : Function.support (fun k : ↥I.K => Real.sqrt (I.rho ((k : G) * g))) = Set.univ :=
    Set.eq_univ_of_forall fun k => (Real.sqrt_pos.2 (I.rho_pos _)).ne'
  rw [hsupp]
  exact Measure.measure_univ_pos.2 (NeZero.ne _)

/-- For commutative `G`, `Ξ ≡ 1`: `δ_P` is trivial on the central elements of `P`. -/
theorem xi_eq_one_of_comm (hc : ∀ x y : G, x * y = y * x) (g : G) : I.xi g = 1 := by
  have hρ : ∀ x : G, I.rho x = 1 := fun x =>
    I.delta_eq_one_of_central _ fun y => Subtype.ext (hc _ _)
  unfold xi
  simp only [hρ, Real.sqrt_one, integral_const, smul_eq_mul, mul_one, Measure.real]
  exact inv_mul_cancel₀ I.haar_K_toReal_pos.ne'

/-- `Ξ` is right `K`-invariant (Waldspurger 2003, Lemme II.1.1, first assertion). -/
theorem xi_mul_right_mem_K (g : G) {k : G} (hk : k ∈ I.K) : I.xi (g * k) = I.xi g := by
  unfold xi
  congr 2
  funext k'
  rw [← mul_assoc, I.rho_mul_right hk]

/-- `Ξ` is continuous: it is right `K`-invariant for the open subgroup `K`, hence locally
constant. -/
theorem continuous_xi : Continuous I.xi :=
  (isLocallyConstant_of_mul_right_invariant I.isOpen_K fun x _ hk =>
    I.xi_mul_right_mem_K x hk).continuous

/-- The inner step of the doubling principle: for `k' ∈ K`,
`∫_K δ(p(k' g₁ k g₂))^{1/2} dk = δ(p(k' g₁))^{1/2} ∫_K δ(p(k g₂))^{1/2} dk`. -/
theorem integral_sqrt_rho_mul_mul (x g₂ : G) :
    ∫ k : ↥I.K, Real.sqrt (I.rho (x * (k : G) * g₂)) ∂Measure.haar =
      Real.sqrt (I.rho x) * ∫ k : ↥I.K, Real.sqrt (I.rho ((k : G) * g₂)) ∂Measure.haar := by
  have h1 : ∀ k : ↥I.K, Real.sqrt (I.rho (x * (k : G) * g₂)) =
      Real.sqrt (I.rho x) * Real.sqrt (I.rho (((I.iwK x * k : ↥I.K) : G) * g₂)) := by
    intro k
    rw [mul_assoc, I.rho_mul, Real.sqrt_mul (I.rho_pos x).le, Subgroup.coe_mul, mul_assoc]
  simp_rw [h1]
  rw [integral_const_mul]
  congr 1
  exact integral_mul_left_eq_self (μ := (Measure.haar : Measure ↥I.K))
    (fun k : ↥I.K => Real.sqrt (I.rho ((k : G) * g₂))) (I.iwK x)

/-- `Ξ` is left `K`-invariant (Waldspurger 2003, Lemme II.1.1, first assertion): the finite Haar
measure of the compact group `K` is right invariant. -/
theorem xi_mul_left_mem_K {k : G} (hk : k ∈ I.K) (g : G) : I.xi (k * g) = I.xi g := by
  have := Measure.isMulRightInvariant_of_isHaarMeasure_of_isFiniteMeasure
    (Measure.haar : Measure ↥I.K)
  unfold xi
  congr 1
  have := integral_mul_right_eq_self (μ := (Measure.haar : Measure ↥I.K))
    (fun k' : ↥I.K => Real.sqrt (I.rho ((k' : G) * g))) (⟨k, hk⟩ : ↥I.K)
  simpa [mul_assoc] using this

/-- **The doubling principle** (Waldspurger 2003, Lemme II.1.3, p. 252; BP Prop 1.5.1(vi)):
`∫_K Ξ(g₁ k g₂) dk = Ξ(g₁) Ξ(g₂)`, `dk` the probability Haar measure on `K`.

Proved for every Iwasawa pair: by Fubini (the integrand is continuous on the compact `K × K`), the
left side is `∫_K ∫_K δ(p(k' g₁ k g₂))^{1/2} dk dk'`, and the inner integral is
`δ(p(k' g₁))^{1/2} Ξ(g₂)` by the cocycle relation and left invariance of `dk`
(`integral_sqrt_rho_mul_mul`). -/
theorem integral_xi_mul_mul (g₁ g₂ : G) :
    ((Measure.haar : Measure ↥I.K) Set.univ).toReal⁻¹ *
        ∫ k : ↥I.K, I.xi (g₁ * (k : G) * g₂) ∂Measure.haar = I.xi g₁ * I.xi g₂ := by
  set μ : Measure ↥I.K := Measure.haar
  -- Fubini on `K × K`
  have hcont : Continuous (Function.uncurry fun (k k' : ↥I.K) =>
      Real.sqrt (I.rho ((k' : G) * (g₁ * (k : G) * g₂)))) :=
    Real.continuous_sqrt.comp (I.continuous_rho.comp
      ((continuous_subtypeVal.comp continuous_snd).mul
        ((continuous_const.mul (continuous_subtypeVal.comp continuous_fst)).mul
          continuous_const)))
  have hswap := integral_integral_swap_of_hasCompactSupport (μ := μ) (ν := μ) hcont
    (HasCompactSupport.of_compactSpace _)
  unfold xi
  simp_rw [integral_const_mul]
  rw [hswap]
  have hin : ∀ k' : ↥I.K, ∫ k : ↥I.K, Real.sqrt (I.rho ((k' : G) * (g₁ * (k : G) * g₂))) ∂μ =
      Real.sqrt (I.rho ((k' : G) * g₁)) * ∫ k : ↥I.K, Real.sqrt (I.rho ((k : G) * g₂)) ∂μ := by
    intro k'
    rw [← I.integral_sqrt_rho_mul_mul]
    simp only [mul_assoc]
    rfl
  simp_rw [hin]
  rw [integral_mul_const]
  ring

/-! ## 2. Integrals of `δ_P`-equivariant functions and independence of `K` -/

omit [MeasurableSpace G] [BorelSpace G] in
/-- `ρ = 1` on `K`. -/
theorem rho_eq_one_of_mem {k : G} (hk : k ∈ I.K) : I.rho k = 1 := by
  rw [I.rho_eq_delta (p := 1) hk (by simp)]
  simp [delta]

omit [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
theorem isClopen_KP : IsClopen (I.KP : Set ↥I.P) :=
  ⟨Subgroup.isClosed_of_isOpen _ I.isOpen_KP, I.isOpen_KP⟩

/-- `0 < μ_P(P ∩ K)` (`P ∩ K` is open, nonempty and compact in `P`). -/
theorem haar_KP_real_pos : 0 < (Measure.haar : Measure ↥I.P).real (I.KP : Set ↥I.P) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (I.isOpen_KP.measure_pos _ ⟨1, I.KP.one_mem⟩).ne'
    I.isCompact_KP.measure_lt_top.ne

/-- **The fibre integral**: for `φ` with `φ(p x) = δ_P(p) φ(x)`,
`∫_P (1_K φ)(p x) dp = μ_P(P ∩ K) φ(x)` (write `x = q k₀`; then `1_K(p q k₀) = 1_{P ∩ K}(p q)`,
`φ(p q k₀) = φ(k₀)` there, and right translation by `q` multiplies `μ_P` by `δ_P(q)`). -/
theorem integral_indicator_K_mul {φ : G → ℂ}
    (hφP : ∀ (p : ↥I.P) (x : G), φ ((p : G) * x) = (I.delta p : ℂ) * φ x) (x : G) :
    ∫ p : ↥I.P, (I.K : Set G).indicator φ ((p : G) * x) ∂Measure.haar =
      ((Measure.haar : Measure ↥I.P).real (I.KP : Set ↥I.P) : ℂ) * φ x := by
  obtain ⟨q, hq, k₀, hk₀, rfl⟩ := I.mul_eq x
  set e : ↥I.P → ℂ := (I.KP : Set ↥I.P).indicator (fun _ => (1 : ℂ)) with he
  have h1 : ∀ p : ↥I.P, (I.K : Set G).indicator φ ((p : G) * (q * k₀)) =
      e (p * ⟨q, hq⟩) * φ k₀ := by
    intro p
    by_cases hp : p * ⟨q, hq⟩ ∈ (I.KP : Set ↥I.P)
    · have hp' : (p : G) * q ∈ I.K := hp
      have hmem : (p : G) * (q * k₀) ∈ I.K := by
        rw [← mul_assoc]; exact I.K.mul_mem hp' hk₀
      rw [Set.indicator_of_mem hmem, he, Set.indicator_of_mem hp, one_mul, ← mul_assoc]
      have := hφP (p * ⟨q, hq⟩) k₀
      rw [I.delta_eq_one_of_mem (p * ⟨q, hq⟩) hp', Complex.ofReal_one, one_mul] at this
      exact this
    · have hmem : (p : G) * (q * k₀) ∉ I.K := fun h => hp (by
        have := I.K.mul_mem h (I.K.inv_mem hk₀)
        rw [← mul_assoc, mul_inv_cancel_right] at this
        exact this)
      rw [Set.indicator_of_notMem hmem, he, Set.indicator_of_notMem hp, zero_mul]
  simp_rw [h1]
  rw [integral_mul_const]
  have hec : Continuous e := by
    rw [he]
    exact continuous_indicator (by simp [I.isClopen_KP.frontier_eq]) continuousOn_const
  have hes : HasCompactSupport e :=
    HasCompactSupport.intro I.isCompact_KP fun y hy => by rw [he, Set.indicator_of_notMem hy]
  have htr := TauCeti.integral_mul_right_eq_modularCharacter_smul
    (μ := (Measure.haar : Measure ↥I.P)) hec hes ⟨q, hq⟩
  rw [htr, he, integral_indicator_const _ I.isOpen_KP.measurableSet, hφP ⟨q, hq⟩ k₀]
  simp only [delta, Complex.real_smul, mul_one]
  ring

/-- **`G = P K` invariance** (`G` unimodular): for continuous `φ` with `φ(p x) = δ_P(p) φ(x)`,
`∫_K φ(k g) dk = ∫_K φ(k) dk`.  Proof: `β = 1_K φ` is continuous with compact support and
`∫_P β(p x) dp = μ_P(P ∩ K) φ(x)` (`integral_indicator_K_mul`); the integration formula for
`G = P K` (`integral_eq_mul_integral_compact_integral`) and the right invariance of `dx` give
`μ_P(P ∩ K) ∫_K φ(k g) dk = c⁻¹ ∫_G β(x g) dx = c⁻¹ ∫_G β(x) dx = μ_P(P ∩ K) ∫_K φ(k) dk`. -/
theorem integral_K_mul_right [T2Space G] [SecondCountableTopology G]
    [(Measure.haar : Measure G).IsMulRightInvariant] {φ : G → ℂ} (hφ : Continuous φ)
    (hφP : ∀ (p : ↥I.P) (x : G), φ ((p : G) * x) = (I.delta p : ℂ) * φ x) (g : G) :
    ∫ k : ↥I.K, φ ((k : G) * g) ∂(Measure.haar : Measure ↥I.K) =
      ∫ k : ↥I.K, φ k ∂(Measure.haar : Measure ↥I.K) := by
  set mS : ℝ := (Measure.haar : Measure ↥I.P).real (I.KP : Set ↥I.P)
  set β : G → ℂ := (I.K : Set G).indicator φ with hβ
  have hKclopen : IsClopen (I.K : Set G) := ⟨I.K.isClosed_of_isOpen I.isOpen_K, I.isOpen_K⟩
  have hβc : Continuous β :=
    continuous_indicator (by simp [hKclopen.frontier_eq]) hφ.continuousOn
  have hβs : HasCompactSupport β :=
    HasCompactSupport.intro I.isCompact_K fun x hx => Set.indicator_of_notMem hx _
  obtain ⟨c, hc, hformula⟩ := integral_eq_mul_integral_compact_integral I.P I.K I.isClosed_P
    I.mul_eq
  have hβg : Continuous fun x => β (x * g) := hβc.comp (continuous_id.mul continuous_const)
  have hβgs : HasCompactSupport fun x => β (x * g) := hβs.comp_homeomorph (Homeomorph.mulRight g)
  have h1 := hformula _ hβg hβgs
  have h2 := hformula _ hβc hβs
  rw [integral_mul_right_eq_self β g] at h1
  have e1 : ∀ k : ↥I.K, ∫ p : ↥I.P, β ((p : G) * (k : G) * g)
      ∂(Measure.haar : Measure ↥I.P) = (mS : ℂ) * φ ((k : G) * g) := fun k => by
    simp only [mul_assoc]
    exact I.integral_indicator_K_mul hφP _
  have e2 : ∀ k : ↥I.K, ∫ p : ↥I.P, β ((p : G) * (k : G))
      ∂(Measure.haar : Measure ↥I.P) = (mS : ℂ) * φ k := fun k =>
    I.integral_indicator_K_mul hφP _
  rw [integral_congr_ae (Filter.Eventually.of_forall e1), integral_const_mul] at h1
  rw [integral_congr_ae (Filter.Eventually.of_forall e2), integral_const_mul] at h2
  have hne : (c : ℂ) * (mS : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 hc.ne') (Complex.ofReal_ne_zero.2 I.haar_KP_real_pos.ne')
  apply mul_left_cancel₀ hne
  calc (c : ℂ) * mS * ∫ k : ↥I.K, φ ((k : G) * g) ∂(Measure.haar : Measure ↥I.K)
      = (c : ℂ) * (mS * ∫ k : ↥I.K, φ ((k : G) * g) ∂(Measure.haar : Measure ↥I.K)) := by ring
    _ = (c : ℂ) * (mS * ∫ k : ↥I.K, φ k ∂(Measure.haar : Measure ↥I.K)) := h1.symm.trans h2
    _ = (c : ℂ) * mS * ∫ k : ↥I.K, φ k ∂(Measure.haar : Measure ↥I.K) := by ring

/-- **The `K`- and `K'`-integrals are proportional on `δ_P`-equivariant functions.** For two
Iwasawa pairs `(P, K)`, `(P, K')` with the same `P` there is `c > 0` with
`∫_K φ(k) dk = c ∫_{K'} φ(k') dk'` for every continuous `φ` with `φ(p x) = δ_P(p) φ(x)`
(both are multiples of the integral over `P\G`).  Proof: with `β = 1_{K'} φ`, the integration
formula for `G = P K` and for `G = P K'` and the fibre integral `∫_P β(p x) dp = μ_P(P ∩ K') φ(x)`
(`integral_indicator_K_mul` for `(P, K')`) give
`c_K μ_P(P ∩ K') ∫_K φ = ∫_G β = c_{K'} μ_P(P ∩ K') ∫_{K'} φ`. -/
theorem exists_integral_K_eq_mul [T2Space G] [SecondCountableTopology G] (J : IwasawaPair G)
    (hP : I.P = J.P) :
    ∃ c : ℝ, 0 < c ∧ ∀ φ : G → ℂ, Continuous φ →
      (∀ (p : ↥I.P) (x : G), φ ((p : G) * x) = (I.delta p : ℂ) * φ x) →
      ∫ k : ↥I.K, φ k ∂(Measure.haar : Measure ↥I.K) =
        c * ∫ k : ↥J.K, φ k ∂(Measure.haar : Measure ↥J.K) := by
  obtain ⟨⟨P, K, hPc, hKc, hmul⟩, hKo⟩ := I
  obtain ⟨⟨P', K', hPc', hKc', hmul'⟩, hKo'⟩ := J
  obtain rfl : P = P' := hP
  set I : IwasawaPair G := ⟨⟨P, K, hPc, hKc, hmul⟩, hKo⟩
  set J : IwasawaPair G := ⟨⟨P, K', hPc', hKc', hmul'⟩, hKo'⟩
  have : LocallyCompactSpace ↥P := hPc.locallyCompactSpace
  have : CompactSpace ↥K := isCompact_iff_compactSpace.mp hKc
  have : CompactSpace ↥K' := isCompact_iff_compactSpace.mp hKc'
  obtain ⟨cI, hcI, hI⟩ := integral_eq_mul_integral_compact_integral (G := G) P K hPc hmul
  obtain ⟨cJ, hcJ, hJ⟩ := integral_eq_mul_integral_compact_integral (G := G) P K' hPc hmul'
  refine ⟨cJ / cI, div_pos hcJ hcI, fun φ hφ hφP => ?_⟩
  set mS : ℝ := (Measure.haar : Measure ↥J.P).real (J.KP : Set ↥J.P)
  set β : G → ℂ := (K' : Set G).indicator φ with hβ
  have hKclopen : IsClopen (K' : Set G) := ⟨K'.isClosed_of_isOpen hKo', hKo'⟩
  have hβc : Continuous β :=
    continuous_indicator (by simp [hKclopen.frontier_eq]) hφ.continuousOn
  have hβs : HasCompactSupport β :=
    HasCompactSupport.intro hKc' fun x hx => Set.indicator_of_notMem hx _
  have hfib : ∀ x : G, ∫ p : ↥P, β ((p : G) * x) ∂(Measure.haar : Measure ↥P) = (mS : ℂ) * φ x :=
    J.integral_indicator_K_mul hφP
  have h1 := hI _ hβc hβs
  have h2 := hJ _ hβc hβs
  rw [integral_congr_ae (Filter.Eventually.of_forall fun k => hfib _), integral_const_mul] at h1 h2
  have hm : (mS : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 J.haar_KP_real_pos.ne'
  have hcI' : (cI : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hcI.ne'
  have key : (cI : ℂ) * (mS * ∫ k : ↥K, φ k ∂(Measure.haar : Measure ↥K)) =
      (cJ : ℂ) * (mS * ∫ k : ↥K', φ k ∂(Measure.haar : Measure ↥K')) := h1.symm.trans h2
  change ∫ k : ↥K, φ k ∂(Measure.haar : Measure ↥K) =
    ((cJ / cI : ℝ) : ℂ) * ∫ k : ↥K', φ k ∂(Measure.haar : Measure ↥K')
  rw [Complex.ofReal_div]
  field_simp
  apply mul_left_cancel₀ hm
  linear_combination key

omit [MeasurableSpace G] [BorelSpace G] in
/-- **`ρ_K ≤ C ρ_{K'}`** for two Iwasawa pairs with the same `P`: write `g = p k` with `k ∈ K`;
then `ρ_K(g) = δ_P(p)` and `ρ_{K'}(g) = δ_P(p) ρ_{K'}(k)`, and the continuous positive function
`ρ_{K'}` is bounded below on the compact `K`. -/
theorem rho_le_mul_rho (J : IwasawaPair G) (hP : I.P = J.P) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : G, I.rho g ≤ C * J.rho g := by
  obtain ⟨⟨P, K, hPc, hKc, hmul⟩, hKo⟩ := I
  obtain ⟨⟨P', K', hPc', hKc', hmul'⟩, hKo'⟩ := J
  obtain rfl : P = P' := hP
  set I : IwasawaPair G := ⟨⟨P, K, hPc, hKc, hmul⟩, hKo⟩
  set J : IwasawaPair G := ⟨⟨P, K', hPc', hKc', hmul'⟩, hKo'⟩
  obtain ⟨k₀, -, hmin⟩ := hKc.exists_isMinOn ⟨1, K.one_mem⟩ J.continuous_rho.continuousOn
  have hm := J.rho_pos k₀
  refine ⟨(J.rho k₀)⁻¹, inv_pos.2 hm, fun g => ?_⟩
  have hg := I.iwP_mul_iwK g
  have hJ : J.rho g = I.delta (I.iwP g) * J.rho (I.iwK g) := by
    conv_lhs => rw [← hg]
    exact J.rho_mul_left (I.iwP g) _
  have hk : J.rho k₀ ≤ J.rho (I.iwK g) := hmin (I.iwK g).property
  change I.delta (I.iwP g) ≤ _
  rw [hJ, ← mul_assoc, mul_comm _ (I.delta _), mul_assoc]
  refine le_mul_of_one_le_right (I.delta_pos _).le ?_
  rw [inv_mul_eq_div, one_le_div hm]
  exact hk

/-- **`Ξ_K ≤ C Ξ_{K'}`** for two Iwasawa pairs `(P, K)`, `(P, K')` with the same `P`.  Proof:
`ψ_K(x) = ρ_K(x g)^{1/2} ρ_K(x)^{1/2}` is `δ_P`-equivariant and `Ξ_K(g)` is its normalized
`K`-integral (`ρ_K = 1` on `K`); by `exists_integral_K_eq_mul` this is a constant times its
`K'`-integral, and `ψ_K ≤ C ψ_{K'}` pointwise (`rho_le_mul_rho`). -/
theorem exists_xi_le_mul_xi [T2Space G] [SecondCountableTopology G] (J : IwasawaPair G)
    (hP : I.P = J.P) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : G, I.xi g ≤ C * J.xi g := by
  obtain ⟨c, hc, hint⟩ := I.exists_integral_K_eq_mul J hP
  obtain ⟨C, hC, hρ⟩ := I.rho_le_mul_rho J hP
  set μI : ℝ := ((Measure.haar : Measure ↥I.K) Set.univ).toReal
  set μJ : ℝ := ((Measure.haar : Measure ↥J.K) Set.univ).toReal
  refine ⟨μI⁻¹ * c * C * μJ, by
    have := I.haar_K_toReal_pos; have := J.haar_K_toReal_pos; positivity, fun g => ?_⟩
  -- `ψ_I(x) = √ρ_I(x g) √ρ_I(x)`
  set ψ : G → ℝ := fun x => Real.sqrt (I.rho (x * g)) * Real.sqrt (I.rho x) with hψ
  have hψc : Continuous ψ :=
    (Real.continuous_sqrt.comp (I.continuous_rho.comp (continuous_id.mul continuous_const))).mul
      (Real.continuous_sqrt.comp I.continuous_rho)
  have hψP : ∀ (p : ↥I.P) (x : G), ((ψ ((p : G) * x) : ℝ) : ℂ) = (I.delta p : ℂ) * (ψ x : ℂ) := by
    intro p x
    have hd := (I.delta_pos p).le
    simp only [hψ, mul_assoc, I.rho_mul_left, Real.sqrt_mul hd]
    rw [← Complex.ofReal_mul]
    congr 1
    linear_combination (Real.sqrt (I.rho (x * g)) * Real.sqrt (I.rho x)) * Real.mul_self_sqrt hd
  have hint' := hint (fun x => (ψ x : ℂ)) (Complex.continuous_ofReal.comp hψc) hψP
  rw [integral_complex_ofReal, integral_complex_ofReal, ← Complex.ofReal_mul] at hint'
  have hintR := Complex.ofReal_injective hint'
  -- `Ξ_I(g) = μ_I⁻¹ ∫_K ψ`
  have hxiI : I.xi g = μI⁻¹ * ∫ k : ↥I.K, ψ k ∂Measure.haar := by
    unfold xi
    congr 2
    funext k
    simp [hψ, I.rho_eq_one_of_mem k.property]
  -- `ψ_I ≤ C ψ_J`
  have hle : ∀ x : G, ψ x ≤ C * (Real.sqrt (J.rho (x * g)) * Real.sqrt (J.rho x)) := by
    intro x
    have h1 : Real.sqrt (I.rho (x * g)) ≤ Real.sqrt C * Real.sqrt (J.rho (x * g)) := by
      rw [← Real.sqrt_mul hC.le]; exact Real.sqrt_le_sqrt (hρ _)
    have h2 : Real.sqrt (I.rho x) ≤ Real.sqrt C * Real.sqrt (J.rho x) := by
      rw [← Real.sqrt_mul hC.le]; exact Real.sqrt_le_sqrt (hρ _)
    calc ψ x ≤ (Real.sqrt C * Real.sqrt (J.rho (x * g))) * (Real.sqrt C * Real.sqrt (J.rho x)) :=
          mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
      _ = (Real.sqrt C * Real.sqrt C) * (Real.sqrt (J.rho (x * g)) * Real.sqrt (J.rho x)) := by
          ring
      _ = _ := by rw [Real.mul_self_sqrt hC.le]
  have hJint : ∫ k : ↥J.K, C * (Real.sqrt (J.rho ((k : G) * g)) * Real.sqrt (J.rho k))
      ∂Measure.haar = C * (μJ * J.xi g) := by
    rw [integral_const_mul]
    congr 1
    unfold xi
    rw [← mul_assoc, mul_inv_cancel₀ J.haar_K_toReal_pos.ne', one_mul]
    congr 1
    funext k
    simp [J.rho_eq_one_of_mem k.property]
  have hmono : ∫ k : ↥J.K, ψ k ∂Measure.haar ≤
      ∫ k : ↥J.K, C * (Real.sqrt (J.rho ((k : G) * g)) * Real.sqrt (J.rho k)) ∂Measure.haar := by
    refine integral_mono ((hψc.comp continuous_subtypeVal).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) ?_ fun k => hle k
    exact (continuous_const.mul ((Real.continuous_sqrt.comp (J.continuous_rho.comp
      (continuous_subtypeVal.mul continuous_const))).mul (Real.continuous_sqrt.comp
        (J.continuous_rho.comp continuous_subtypeVal)))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  rw [hxiI, hintR]
  have hμI := inv_pos.2 I.haar_K_toReal_pos
  calc μI⁻¹ * (c * ∫ k : ↥J.K, ψ k ∂Measure.haar) ≤ μI⁻¹ * (c * (C * (μJ * J.xi g))) := by
        gcongr
        exact hmono.trans_eq hJint
    _ = μI⁻¹ * c * C * μJ * J.xi g := by ring

/-- **Independence of `K`** (BP §1.5, p. 24, remark for special `K`; here any compact open `K`):
for two Iwasawa pairs `(P, K)`, `(P, K')` with the same `P`, `Ξ_K` and `Ξ_{K'}` are
equivalent: `c Ξ_{K'} ≤ Ξ_K ≤ C Ξ_{K'}`. -/
theorem exists_xi_equiv [T2Space G] [SecondCountableTopology G] (J : IwasawaPair G)
    (hP : I.P = J.P) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ g : G, c * J.xi g ≤ I.xi g ∧ I.xi g ≤ C * J.xi g := by
  obtain ⟨C, hC, h⟩ := I.exists_xi_le_mul_xi J hP
  obtain ⟨C', hC', h'⟩ := J.exists_xi_le_mul_xi I hP.symm
  refine ⟨C'⁻¹, C, inv_pos.2 hC', hC, fun g => ⟨?_, h g⟩⟩
  rw [inv_mul_le_iff₀ hC']
  exact h' g

end IwasawaPair


end GSpinGGP
