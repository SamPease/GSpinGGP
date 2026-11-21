/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import TauCeti.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Group.ModularCharacter

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

* `IwasawaPair G`: closed `P`, compact open `K`, `G = P K`.
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

## Not here

The estimates of Waldspurger 2003 Lemme II.1.1 (second assertion), II.1.5, II.1.6, II.4.4 and
Prop II.4.5 are stated by Waldspurger for `K` the fixer of a special point of the apartment of a
maximal split torus `A₀ ⊆ P₀`, `σ` the log-norm of an embedding `τ : G → GL_n` with
`τ(K) ⊆ GL_n(𝒪)`, and `M̄₀⁺` defined through `H₀` and the simple roots.  They are not stated here.
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

/-- An **Iwasawa pair** in a topological group `G`: a closed subgroup `P` and a compact open
subgroup `K` with `G = P K` (Waldspurger 2003 §I.1: `G = P K` for every semi-standard parabolic
`P`, with `K` special maximal compact; here `K` is any compact open subgroup). -/
structure IwasawaPair (G : Type*) [Group G] [TopologicalSpace G] where
  /-- the parabolic subgroup -/
  P : Subgroup G
  /-- the compact open subgroup -/
  K : Subgroup G
  isClosed_P : IsClosed (P : Set G)
  isOpen_K : IsOpen (K : Set G)
  isCompact_K : IsCompact (K : Set G)
  /-- the Iwasawa decomposition `G = P K` -/
  mul_eq : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k

namespace IwasawaPair

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] (I : IwasawaPair G)

instance locallyCompactSpace_P : LocallyCompactSpace ↥I.P :=
  I.isClosed_P.locallyCompactSpace

instance compactSpace_K : CompactSpace ↥I.K :=
  isCompact_iff_compactSpace.mp I.isCompact_K

/-- `P ∩ K`, as a subgroup of `P`: a compact open subgroup. -/
abbrev KP : Subgroup ↥I.P := I.K.subgroupOf I.P

omit [IsTopologicalGroup G] [LocallyCompactSpace G] in
theorem isOpen_KP : IsOpen (I.KP : Set ↥I.P) :=
  I.isOpen_K.preimage continuous_subtypeVal

omit [IsTopologicalGroup G] [LocallyCompactSpace G] in
theorem isCompact_KP : IsCompact (I.KP : Set ↥I.P) :=
  I.isClosed_P.isClosedEmbedding_subtypeVal.isCompact_preimage I.isCompact_K

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

/-- A choice of `P`-component of `g = p k`. -/
def iwP (g : G) : ↥I.P := ⟨(I.mul_eq g).choose, (I.mul_eq g).choose_spec.1⟩

/-- A choice of `K`-component of `g = p k`. -/
def iwK (g : G) : ↥I.K := ⟨(I.iwP g : G)⁻¹ * g, by
  obtain ⟨k, hk, hg⟩ := (I.mul_eq g).choose_spec.2
  have e : ((I.mul_eq g).choose)⁻¹ * g = k := by rw [inv_mul_eq_iff_eq_mul]; exact hg
  change ((I.mul_eq g).choose)⁻¹ * g ∈ I.K
  rw [e]
  exact hk⟩

omit [IsTopologicalGroup G] [LocallyCompactSpace G] in
theorem iwP_mul_iwK (g : G) : ((I.iwP g : G)) * (I.iwK g : G) = g := by
  simp [iwK]

/-- `ρ(g) = δ_P(p(g))`, for `g = p(g) k(g)`. -/
def rho (g : G) : ℝ := I.delta (I.iwP g)

theorem rho_pos (g : G) : 0 < I.rho g := I.delta_pos _

theorem rho_eq_delta {p : ↥I.P} {k g : G} (hk : k ∈ I.K) (hg : g = p * k) :
    I.rho g = I.delta p :=
  I.delta_eq_of_mul_eq (I.iwK g).property hk (by rw [iwP_mul_iwK, hg])

/-- `ρ(p) = δ_P(p)` on `P`. -/
theorem rho_of_mem (p : ↥I.P) : I.rho p = I.delta p :=
  I.rho_eq_delta I.K.one_mem (mul_one _).symm

theorem rho_mul_right {g k : G} (hk : k ∈ I.K) : I.rho (g * k) = I.rho g :=
  I.rho_eq_delta (I.K.mul_mem (I.iwK g).property hk) (by rw [← mul_assoc, iwP_mul_iwK])

theorem rho_mul_left (p : ↥I.P) (g : G) : I.rho (p * g) = I.delta p * I.rho g := by
  change _ = I.delta p * I.delta (I.iwP g)
  rw [← I.delta_mul]
  exact I.rho_eq_delta (I.iwK g).property (by rw [Subgroup.coe_mul, mul_assoc, iwP_mul_iwK])

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

/-- `Ξ` is right `K`-invariant (Waldspurger 2003, Lemme II.1.1, first assertion). -/
theorem xi_mul_right_mem_K (g : G) {k : G} (hk : k ∈ I.K) : I.xi (g * k) = I.xi g := by
  unfold xi
  congr 2
  funext k'
  rw [← mul_assoc, I.rho_mul_right hk]

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

end IwasawaPair


end GSpinGGP
