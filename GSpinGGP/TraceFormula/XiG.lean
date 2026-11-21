/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Analytic
import GSpinGGP.GGP.Cocharacter

/-!
# Harish-Chandra's function `Ξ` for an Iwasawa pair, and Levi data

Harish-Chandra's function is defined (Waldspurger, *La formule de Plancherel pour les groupes
`p`-adiques*, J. Inst. Math. Jussieu 2 (2003), §II.1, p. 250–251; BP §1.5) from a minimal
parabolic subgroup `P₀` and a compact subgroup `K` with `G = P₀ K`:

  `Ξ(g) = ∫_K δ₀(p₀(kg))^{1/2} dk`,   `dk` the probability Haar measure of `K`,

where `g = p₀(g) k₀(g)` with `p₀(g) ∈ P₀`, `k₀(g) ∈ K`.  Only the decomposition `G = P₀ K`
enters the definition, so this file works for any locally compact group `G`, closed subgroup
`P`, and compact open subgroup `K` with `G = P K` (an `IwasawaPair`).  The same construction gives
`Ξ^G` for `G = GSpin(W) × GSpin(V)` (`IwasawaDatum.toIwasawaPair`, `IwasawaDatum.xiHC_eq_xi`), and
`Ξ^M` for a Levi subgroup `M` (`LeviDatum.xiM`) or `Ξ^H` for `H = GSpin(W)`, each with its own
pair.

## Main definitions

* `IwasawaPair G`: closed `P`, compact open `K`, `G = P K`.
* `IwasawaPair.delta`: the modular character `δ_P` of `P` (Mathlib's `modularCharacter`,
  `μ(E p⁻¹) = δ_P(p) μ(E)`, which is `|det Ad(p)|_{𝔲}|` for `P = M U`, as in Waldspurger 2003
  §I.1); `IwasawaPair.rho g = δ_P(p(g))` (independent of the choice of `p(g)`).
* `IwasawaPair.xi`: `Ξ(g) = ∫_K δ_P(p(kg))^{1/2} dk` (normalized Haar measure on `K`).
* `LeviDatum I`: a parabolic subgroup `P ⊇ I.P` with a Levi decomposition `P = M U`, an opposite
  unipotent subgroup `Ū`, and the *good position* of `K` relative to `M`,
  `M = (P₀ ∩ M)(K ∩ M)` (Waldspurger 2003 §I.1: "le groupe `M ∩ K` vérifie relativement à `M`
  les mêmes propriétés que `K` relativement à `G`"); its Iwasawa pair `LeviDatum.levi` on `M`,
  `Ξ^M = LeviDatum.xiM`, and `δ_P` on `M` (`LeviDatum.deltaP`); `LeviDatum.top` (`P = M = G`).
* `flagLevi b wt`: the Levi subgroup of a flag stabilizer in `GSpin(V)` attached to a splitting
  `(b, wt)` of its weight filtration (the centralizer of the cocharacter `λ`), and
  `GGPData.flagLeviG`, its product for `G = GSpin(W) × GSpin(V)`.

## Main results

* `IwasawaPair.rho_mul`: the cocycle relation `δ(p(xy)) = δ(p(x)) δ(p(k(x) y))`.
* `IwasawaPair.xi_mul_left_mem_K`, `xi_mul_right_mem_K`: `Ξ` is bi-`K`-invariant
  (Waldspurger 2003, Lemme II.1.1, first assertion).
* `IwasawaPair.xi_pos`: `Ξ > 0`.
* **Doubling principle** `IwasawaPair.integral_xi_mul_mul`: `∫_K Ξ(g₁ k g₂) dk = Ξ(g₁) Ξ(g₂)`
  (Waldspurger 2003, Lemme II.1.3; BP Prop 1.5.1(vi)).  Proved for every Iwasawa pair, not only
  for a special maximal compact `K`: the printed proof uses only that the `K`-fixed vectors of
  `i_{P}^G 1` form a line, i.e. `G = P K`; the proof here is a direct computation with the
  cocycle relation and the left invariance of `dk`.
* Levi decompositions `P_F = M_F N_F` (`IsFlagSplitting.exists_mem_flagLevi_mul`) and
  `P_{F_W} × P_{F_V} = (M_{F_W} × M_{F_V})(N_{F_W} × N_{F_V})` (`GGPData.exists_mem_flagLeviG_mul`).
* For `G = GSpin(W) × GSpin(V)`: `IwasawaDatum.xiHC_eq_xi`, and hence the doubling principle and
  bi-`K`-invariance for `xiHC` (`IwasawaDatum.integral_xiHC_mul_mul`, …).

## Not here

The estimates of Waldspurger 2003 Lemme II.1.1 (second assertion), II.1.5, II.1.6, II.4.4 and
Prop II.4.5 are stated by Waldspurger for `K` the fixer of a special point of the apartment of a
maximal split torus `A₀ ⊆ P₀`, `σ` the log-norm of an embedding `τ : G → GL_n` with
`τ(K) ⊆ GL_n(𝒪)`, and `M̄₀⁺` defined through `H₀` and the simple roots.  None of these objects
is available for `G = GSpin(W) × GSpin(V)` here, so they are not stated as literature
assumptions in this file.
-/

open MeasureTheory Topology Filter
open scoped Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace GSpinGGP

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

theorem isOpen_KP : IsOpen (I.KP : Set ↥I.P) :=
  I.isOpen_K.preimage continuous_subtypeVal

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

/-- A choice of `P`-component of `g = p k`. -/
def iwP (g : G) : ↥I.P := ⟨(I.mul_eq g).choose, (I.mul_eq g).choose_spec.1⟩

/-- A choice of `K`-component of `g = p k`. -/
def iwK (g : G) : ↥I.K := ⟨(I.iwP g : G)⁻¹ * g, by
  obtain ⟨k, hk, hg⟩ := (I.mul_eq g).choose_spec.2
  have e : ((I.mul_eq g).choose)⁻¹ * g = k := by rw [inv_mul_eq_iff_eq_mul]; exact hg
  show ((I.mul_eq g).choose)⁻¹ * g ∈ I.K
  rw [e]
  exact hk⟩

theorem iwP_mul_iwK (g : G) : ((I.iwP g : G)) * (I.iwK g : G) = g := by
  simp [iwK]

/-- `ρ(g) = δ_P(p(g))`, for `g = p(g) k(g)`. -/
def rho (g : G) : ℝ := I.delta (I.iwP g)

theorem rho_pos (g : G) : 0 < I.rho g := I.delta_pos _

theorem rho_eq_delta {p : ↥I.P} {k g : G} (hk : k ∈ I.K) (hg : g = p * k) :
    I.rho g = I.delta p :=
  I.delta_eq_of_mul_eq (I.iwK g).2 hk (by rw [iwP_mul_iwK, hg])

/-- `ρ(p) = δ_P(p)` on `P`. -/
theorem rho_of_mem (p : ↥I.P) : I.rho p = I.delta p :=
  I.rho_eq_delta I.K.one_mem (mul_one _).symm

theorem rho_mul_right {g k : G} (hk : k ∈ I.K) : I.rho (g * k) = I.rho g :=
  I.rho_eq_delta (I.K.mul_mem (I.iwK g).2 hk) (by rw [← mul_assoc, iwP_mul_iwK])

theorem rho_mul_left (p : ↥I.P) (g : G) : I.rho (p * g) = I.delta p * I.rho g := by
  show _ = I.delta p * I.delta (I.iwP g)
  rw [← I.delta_mul]
  exact I.rho_eq_delta (I.iwK g).2 (by rw [Subgroup.coe_mul, mul_assoc, iwP_mul_iwK])

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

/-- The total mass of the Haar measure of `K`, as a positive real. -/
theorem haar_K_toReal_pos : 0 < ((Measure.haar : Measure ↥I.K) Set.univ).toReal :=
  ENNReal.toReal_pos (Measure.measure_univ_pos.2 (NeZero.ne _)).ne'
    (measure_ne_top _ _)

theorem continuous_sqrt_rho_mul (g : G) : Continuous fun k : ↥I.K => Real.sqrt (I.rho ((k : G) * g)) :=
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

variable [SecondCountableTopology G] [T2Space G]

instance secondCountableTopology_K : SecondCountableTopology ↥I.K :=
  TopologicalSpace.Subtype.secondCountableTopology (I.K : Set G)

/-- `Ξ` is left `K`-invariant (Waldspurger 2003, Lemme II.1.1, first assertion): the Haar measure of
the compact group `K` is right invariant. -/
theorem xi_mul_left_mem_K {k : G} (hk : k ∈ I.K) (g : G) : I.xi (k * g) = I.xi g := by
  unfold xi
  congr 1
  have hmap := map_mul_right_haar_of_mem_compact (Q := ↥I.K) ⊤ (by simpa using isCompact_univ)
    (Subgroup.mem_top (⟨k, hk⟩ : ↥I.K))
  conv_rhs => rw [← hmap]
  rw [integral_map (measurable_mul_const _).aemeasurable
    (I.continuous_sqrt_rho_mul g).aestronglyMeasurable]
  congr 1
  funext k'
  simp [mul_assoc]


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
  set c : ℝ := (μ Set.univ).toReal⁻¹
  -- Fubini on `K × K`
  have hcont : Continuous (Function.uncurry fun (k k' : ↥I.K) =>
      Real.sqrt (I.rho ((k' : G) * (g₁ * (k : G) * g₂)))) :=
    Real.continuous_sqrt.comp (I.continuous_rho.comp
      ((continuous_subtypeVal.comp continuous_snd).mul
        ((continuous_const.mul (continuous_subtypeVal.comp continuous_fst)).mul
          continuous_const)))
  have hint : Integrable (Function.uncurry fun (k k' : ↥I.K) =>
      Real.sqrt (I.rho ((k' : G) * (g₁ * (k : G) * g₂)))) (μ.prod μ) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hswap := integral_integral_swap hint
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

/-! ## 2. Levi data -/

/-- **Levi data** for an Iwasawa pair `I = (P₀, K)`: a parabolic subgroup `P ⊇ P₀` with a Levi
decomposition `P = M U` (`M` normalizes `U`, `M ∩ U = 1`), an opposite unipotent subgroup `Ū`
(`M` normalizes it and `P ∩ Ū = 1`), and the good position of `K` relative to `M`:
`M = (P₀ ∩ M)(K ∩ M)` (Waldspurger 2003 §I.1, for `P` semi-standard and `K` special: "le groupe
`M ∩ K` vérifie relativement à `M` les mêmes propriétés que `K` relativement à `G`").  The good
position is a hypothesis: for an arbitrary compact open `K` with `G = P₀ K` it can fail. -/
structure LeviDatum {G : Type*} [Group G] [TopologicalSpace G] (I : IwasawaPair G) where
  /-- the parabolic subgroup -/
  P : Subgroup G
  /-- its Levi factor -/
  M : Subgroup G
  /-- its unipotent radical -/
  U : Subgroup G
  /-- the opposite unipotent radical -/
  Ubar : Subgroup G
  P0_le : I.P ≤ P
  M_le : M ≤ P
  U_le : U ≤ P
  isClosed_P : IsClosed (P : Set G)
  isClosed_M : IsClosed (M : Set G)
  isClosed_U : IsClosed (U : Set G)
  isClosed_Ubar : IsClosed (Ubar : Set G)
  conj_mem_U : ∀ m ∈ M, ∀ u ∈ U, m * u * m⁻¹ ∈ U
  conj_mem_Ubar : ∀ m ∈ M, ∀ u ∈ Ubar, m * u * m⁻¹ ∈ Ubar
  /-- `P = M U` -/
  mul_eq : ∀ p ∈ P, ∃ m ∈ M, ∃ u ∈ U, p = m * u
  inf_eq_bot : M ⊓ U = ⊥
  inf_Ubar_eq_bot : P ⊓ Ubar = ⊥
  /-- good position of `K` relative to `M`: `M = (P₀ ∩ M)(K ∩ M)` -/
  goodPos : ∀ m ∈ M, ∃ p ∈ I.P, ∃ k ∈ I.K, p ∈ M ∧ k ∈ M ∧ m = p * k

namespace LeviDatum

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] {I : IwasawaPair G} (L : LeviDatum I)

instance locallyCompactSpace_P : LocallyCompactSpace ↥L.P := L.isClosed_P.locallyCompactSpace

instance locallyCompactSpace_M : LocallyCompactSpace ↥L.M := L.isClosed_M.locallyCompactSpace

instance locallyCompactSpace_Ubar : LocallyCompactSpace ↥L.Ubar :=
  L.isClosed_Ubar.locallyCompactSpace

/-- The Iwasawa pair `(P₀ ∩ M, K ∩ M)` of the Levi subgroup `M`. -/
def levi : IwasawaPair ↥L.M where
  P := I.P.subgroupOf L.M
  K := I.K.subgroupOf L.M
  isClosed_P := I.isClosed_P.preimage continuous_subtypeVal
  isOpen_K := I.isOpen_K.preimage continuous_subtypeVal
  isCompact_K := L.isClosed_M.isClosedEmbedding_subtypeVal.isCompact_preimage I.isCompact_K
  mul_eq m := by
    obtain ⟨p, hp, k, hk, hpM, hkM, h⟩ := L.goodPos m m.2
    exact ⟨⟨p, hpM⟩, hp, ⟨k, hkM⟩, hk, Subtype.ext h⟩

/-- `δ_P` on the Levi factor `M`: the modular character of `P` (Waldspurger 2003 §I.1:
`|det Ad(m)|_{𝔲}|`). -/
def deltaP (m : ↥L.M) : ℝ :=
  (Measure.modularCharacter (⟨m, L.M_le m.2⟩ : ↥L.P) : ℝ)

theorem deltaP_pos (m : ↥L.M) : 0 < L.deltaP m := by
  unfold deltaP
  exact_mod_cast Measure.modularCharacterFun_pos _

/-- **`Ξ^M`**, Harish-Chandra's function of the Levi factor, built from `(P₀ ∩ M, K ∩ M)`
(Waldspurger 2003 §II.1, p. 252: "on définit une fonction `Ξ^M` sur `M` comme on vient de définir
`Ξ` sur `G`"). -/
def xiM [MeasurableSpace G] [BorelSpace G] (m : ↥L.M) : ℝ := L.levi.xi m

theorem xiM_pos [MeasurableSpace G] [BorelSpace G] (m : ↥L.M) : 0 < L.xiM m := L.levi.xi_pos m

/-- The trivial Levi datum `P = M = G`, `U = Ū = 1` (good position is the Iwasawa decomposition
itself). -/
def top [T1Space G] (I : IwasawaPair G) : LeviDatum I where
  P := ⊤
  M := ⊤
  U := ⊥
  Ubar := ⊥
  P0_le := le_top
  M_le := le_rfl
  U_le := bot_le
  isClosed_P := by simp
  isClosed_M := by simp
  isClosed_U := by simp
  isClosed_Ubar := by simp
  conj_mem_U m _ u hu := by
    rw [Subgroup.mem_bot] at hu ⊢
    simp [hu]
  conj_mem_Ubar m _ u hu := by
    rw [Subgroup.mem_bot] at hu ⊢
    simp [hu]
  mul_eq p _ := ⟨p, trivial, 1, Subgroup.one_mem _, (mul_one p).symm⟩
  inf_eq_bot := by simp
  inf_Ubar_eq_bot := by simp
  goodPos m _ := by
    obtain ⟨p, hp, k, hk, h⟩ := I.mul_eq m
    exact ⟨p, hp, k, hk, trivial, trivial, h⟩

end LeviDatum

/-! ## 3. The Levi subgroup of a flag stabilizer in `GSpin(V)` -/

section FlagLevi

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V}
variable {ι : Type*} [Fintype ι]

/-- **The Levi subgroup** attached to a splitting `(b, wt)` of the weight filtration of an
isotropic flag (Thesis §5.1.2, `P = M N`): the elements of `GSpin(V)` whose image in `SO(V)`
commutes with the cocharacter `λ(τ)` (`cochar b wt τ`) for every `τ`, i.e. preserves each weight
space of the splitting.  It contains the central scalars `K^×`. -/
def flagLevi (b : Module.Basis ι K V) (wt : ι → ℤ) : Subgroup (GSpin Q) where
  carrier := {g | ∀ τ : K,
    (specP Q g : V →ₗ[K] V) ∘ₗ cochar b wt τ = cochar b wt τ ∘ₗ (specP Q g : V →ₗ[K] V)}
  one_mem' := by intro τ; ext v; simp
  mul_mem' := by
    intro g h hg hh τ
    rw [map_mul, show ((specP Q g * specP Q h : V ≃ₗ[K] V) : V →ₗ[K] V) =
      (specP Q g : V →ₗ[K] V) ∘ₗ (specP Q h : V →ₗ[K] V) from rfl, LinearMap.comp_assoc, hh τ,
      ← LinearMap.comp_assoc, hg τ, LinearMap.comp_assoc]
  inv_mem' := by
    intro g hg τ
    ext v
    have h := congr($(hg τ) (specP Q g⁻¹ v))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h ⊢
    rw [specP_inv_apply_apply] at h
    rw [← h]
    have := specP_inv_apply_apply g⁻¹ (cochar b wt τ (specP Q g⁻¹ v))
    rwa [inv_inv] at this

theorem scalarGSpin_mem_flagLevi (b : Module.Basis ι K V) (wt : ι → ℤ) (c : Kˣ) :
    scalarGSpin Q c ∈ flagLevi (Q := Q) b wt := by
  intro τ
  rw [specP_scalarGSpin_eq_one]
  rfl

/-- **Levi decomposition of a flag stabilizer** `P_F = M_F N_F` (Thesis §5.1.2): every `p ∈ P_F`
is `m u` with `m` in the Levi subgroup `flagLevi b wt` of a splitting and `u` in the unipotent
radical `flagUnip F`.  From `IsFlagSplitting.exists_levi_decomp` (`p = m y` with `y ∈ K^× N_F`) by
moving the scalar of `y` into `m` (`exists_smul_sub_one_isNilpotent_of_mem_flagUnipSO`). -/
theorem IsFlagSplitting.exists_mem_flagLevi_mul [FiniteDimensional K V] (hQ : IsNondeg Q)
    {F : IsotropicFlag Q} {b : Module.Basis ι K V} {wt : ι → ℤ} (hs : IsFlagSplitting F b wt)
    {p : GSpin Q} (hp : p ∈ flagStab F) :
    ∃ m ∈ flagLevi (Q := Q) b wt, ∃ u ∈ flagUnip F, p = m * u := by
  obtain ⟨m, y, he, hm, hy, hy'⟩ := hs.exists_levi_decomp hQ hp
  have hySO : y ∈ flagUnipSO F := mem_flagUnipSO_of_raisesFil hy hy'
  obtain ⟨c, hc⟩ := exists_smul_sub_one_isNilpotent_of_mem_flagUnipSO hQ hySO
  have hSO' := (flagUnipSO F).mul_mem hySO (scalarGSpin_mem_flagUnipSO F c)
  refine ⟨m * scalarGSpin Q c⁻¹, (flagLevi b wt).mul_mem
      (fun τ => (cochar_comp_of_isHomog hm τ).symm) (scalarGSpin_mem_flagLevi b wt c⁻¹),
    y * scalarGSpin Q c, ⟨hSO'.1, hSO'.2.1, hSO'.2.2, by rw [coe_mul_scalarGSpin]; exact hc⟩, ?_⟩
  have hcen := Subgroup.mem_center_iff.mp (scalarGSpin_mem_center Q c⁻¹)
  rw [he, mul_assoc, ← mul_assoc (scalarGSpin Q c⁻¹), ← hcen y, mul_assoc y,
    ← map_mul, inv_mul_cancel, map_one, mul_one]

end FlagLevi

/-! ## 4. The Iwasawa datum of `G = GSpin(W) × GSpin(V)` -/

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {d : GGPData F}

section LeviG

variable (d)
variable {ιW ιV : Type*} [Fintype ιW] [Fintype ιV]

/-- **The Levi subgroup of `P = P_{F_W} × P_{F_V}`** (`d.whittB F_W F_V`) attached to splittings
`(b_W, wt_W)`, `(b_V, wt_V)` of the two flags: `M = M_{F_W} × M_{F_V}` (Thesis §5.1.2). -/
def flagLeviG (bW : Module.Basis ιW F (Fin d.m → F)) (wtW : ιW → ℤ)
    (bV : Module.Basis ιV F d.V) (wtV : ιV → ℤ) : Subgroup ↥d.G :=
  (flagLevi (Q := d.QW) bW wtW).comap d.fst ⊓ (flagLevi (Q := d.QV) bV wtV).comap d.snd

theorem pair_fst_snd (g : ↥d.G) : d.pair (d.fst g, d.snd g) = g := by
  apply Subtype.ext; apply Units.ext; rfl

variable {d}

/-- **Levi decomposition** `P_{F_W} × P_{F_V} = (M_{F_W} × M_{F_V})(N_{F_W} × N_{F_V})`
(Thesis §5.1.2), factorwise from `IsFlagSplitting.exists_mem_flagLevi_mul`. -/
theorem exists_mem_flagLeviG_mul {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV}
    {bW : Module.Basis ιW F (Fin d.m → F)} {wtW : ιW → ℤ}
    {bV : Module.Basis ιV F d.V} {wtV : ιV → ℤ}
    (hsW : IsFlagSplitting FW bW wtW) (hsV : IsFlagSplitting FV bV wtV)
    {p : ↥d.G} (hp : p ∈ d.whittB FW FV) :
    ∃ m ∈ d.flagLeviG bW wtW bV wtV, ∃ u ∈ d.whittU FW FV, p = m * u := by
  obtain ⟨mW, hmW, uW, huW, eW⟩ := hsW.exists_mem_flagLevi_mul d.nondeg hp.1
  obtain ⟨mV, hmV, uV, huV, eV⟩ := hsV.exists_mem_flagLevi_mul d.nondeg_QV hp.2
  refine ⟨d.pair (mW, mV), ⟨hmW, hmV⟩, d.pair (uW, uV), ⟨huW, huV⟩, ?_⟩
  rw [← map_mul, Prod.mk_mul_mk, ← eW, ← eV, pair_fst_snd]

end LeviG

namespace IwasawaDatum

variable (IW : d.IwasawaDatum)

/-- The Iwasawa pair `(P₀, K)` of an Iwasawa datum. -/
def toIwasawaPair : IwasawaPair ↥d.G where
  P := IW.P0
  K := IW.K
  isClosed_P := d.isClosed_whittB IW.FW IW.FV
  isOpen_K := IW.isOpen_K
  isCompact_K := IW.isCompact_K
  mul_eq := IW.mul_eq

/-- `xiHC` is the `Ξ` of the Iwasawa pair `(P₀, K)`. -/
theorem xiHC_eq_xi : IW.xiHC = IW.toIwasawaPair.xi := rfl

/-- `Ξ^G` is bi-`K`-invariant (Waldspurger 2003, Lemme II.1.1, first assertion). -/
theorem xiHC_mul_left_mem_K {k : ↥d.G} (hk : k ∈ IW.K) (g : ↥d.G) :
    IW.xiHC (k * g) = IW.xiHC g :=
  IW.toIwasawaPair.xi_mul_left_mem_K hk g

theorem xiHC_mul_right_mem_K (g : ↥d.G) {k : ↥d.G} (hk : k ∈ IW.K) :
    IW.xiHC (g * k) = IW.xiHC g :=
  IW.toIwasawaPair.xi_mul_right_mem_K g hk

theorem xiHC_pos (g : ↥d.G) : 0 < IW.xiHC g := IW.toIwasawaPair.xi_pos g

/-- **The doubling principle for `Ξ^G`** (Waldspurger 2003, Lemme II.1.3; BP Prop 1.5.1(vi)):
`∫_K Ξ(g₁ k g₂) dk = Ξ(g₁) Ξ(g₂)`, `dk` the probability Haar measure on `K`. -/
theorem integral_xiHC_mul_mul (g₁ g₂ : ↥d.G) :
    ((Measure.haar : Measure ↥IW.K) Set.univ).toReal⁻¹ *
        ∫ k : ↥IW.K, IW.xiHC (g₁ * (k : ↥d.G) * g₂) ∂Measure.haar = IW.xiHC g₁ * IW.xiHC g₂ := by
  have : SecondCountableTopology ↥d.G := subgroup_secondCountableTopology F d.ambient d.G
  exact IW.toIwasawaPair.integral_xi_mul_mul g₁ g₂

end IwasawaDatum

end GGPData

end GSpinGGP
