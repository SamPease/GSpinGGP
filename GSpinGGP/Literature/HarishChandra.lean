/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups
import GSpinGGP.Foundations.Representations
import GSpinGGP.Foundations.GSpin

/-!
# Cited harmonic analysis: Harish-Chandra, Rodier, Beuzart-Plessis

The results of harmonic analysis on `p`-adic
reductive groups that the proof of the main theorem (Thesis Thm 6.4.1) uses
as black boxes, stated as `axiom`s about the concrete groups `d.G = GSpin(W) × GSpin(V)` of a
`d : GGPData F` over a `p`-adic field `F`. Every axiom quantifies over *all* `d`, so it applies
to the inner forms `d.twist τ` as well (those are not quasi-split; no axiom below except (e)
and (f) assumes quasi-splitness).

Since `GGP/Triple.lean` is in the same layer and not visible here, the character
`θ_π = characterOn π (regularSet d.G d.lie)` (= Triple's `charG d π`) and stability/transfer are
written out inline.

## Contents
* instances `T2Space ↥d.G`, `LocallyCompactSpace ↥d.G` (theorems of LocalGroups, made instances
  here because `F` is recoverable from `d`);
* (a) `hc_regularSet_open_conull`  — `G_reg(F)` is open with Haar-null complement (Harish-Chandra);
* (b) `hc_character_exists`, theorem `hc_character` — `θ_π` is a function, locally constant on
  `G_reg(F)` (Harish-Chandra's regularity theorem; Bernstein's admissibility);
* (c) `hc_character_isQuasiCharacter` — `θ_π` is a quasi-character (HC local character expansion;
  BP Prop 4.1.1(i), Thesis Prop 4.1.1.1);
* (d) `germ_unique` — uniqueness of the local expansion (linear independence of the `ĵ(O,·)`,
  Harish-Chandra; BP §4.5, Thesis §4.2); derived: `germ_eq_of_hasGermExpansion`, `germ_add`,
  `germ_smul`, `germ_finset_sum`, `germ_zero`;
* (e) `bp_germ_transfer` — BP (12.1.2) = Thesis (6.1.2), extended to the inner twists of `GSpin`;
* (f) `rodier_germ_one` — BP Prop 4.8.1(i) = Thesis Prop 4.4.1(i) (Rodier, Mœglin–Waldspurger);
* (g) `schur_central` — Schur's lemma for irreducible unitary representations.

Not needed as an axiom: BP Prop 4.5.1(i) (`c_θ(x) = 0` if `G_x` is not quasi-split) — `germ` is
`0` off `NilReg` by definition (`germ_of_not_mem`), and `NilReg(𝔤_x) = ∅ ↔ G_x` not quasi-split
is a GSpin fact (`Literature/GSpin.lean`).
-/

open MeasureTheory Topology Filter

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

namespace HarishChandra

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-! ## Topological instances on `↥d.G` -/

/-- `G(F)` is Hausdorff (LocalGroups `subgroup_t2Space`). An instance here because `F` is
determined by `d`. -/
instance t2Space_G (d : GGPData F) : T2Space ↥d.G :=
  subgroup_t2Space F d.ambient d.G

/-- `G(F)` is locally compact (`d.G` is closed in `(C(W) × C(V))ˣ`). -/
instance locallyCompactSpace_G (d : GGPData F) : LocallyCompactSpace ↥d.G :=
  subgroup_locallyCompactSpace_of_isClosed F d.ambient d.G d.isClosed_G

/-- The same for an inner form `d.twist τ`. Needed separately: `GGPData.twist` is an `abbrev`, so
`(d.twist τ).QW` reduces to `τ.Q'` and the instance discrimination tree no longer matches the
generic `t2Space_G`. -/
instance t2Space_twist_G (d : GGPData F) (τ : InnerTwist d.QW) : T2Space ↥(d.twist τ).G :=
  t2Space_G (d.twist τ)

/-- `G_α(F)` is locally compact (see `t2Space_twist_G`). -/
instance locallyCompactSpace_twist_G (d : GGPData F) (τ : InnerTwist d.QW) :
    LocallyCompactSpace ↥(d.twist τ).G :=
  locallyCompactSpace_G (d.twist τ)

end HarishChandra

open HarishChandra

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-! ## (a) The regular set -/

/-- **(a) Harish-Chandra.** The regular semisimple set `G_reg(F)` of `G = GSpin(W) × GSpin(V)` is
open in `G(F)` and its complement has Haar measure zero (it is the non-vanishing locus of a
nonzero polynomial function, the coefficient of `t^{rk G}` in `det(t − (1 − Ad g))`, on the
connected group `G`). Thesis §2.1; Harish-Chandra, *Harmonic analysis on reductive p-adic groups*
(LNM 162, 1970) (section unverified); BP Astérisque 418, §1.

Its role in this project: two representatives of the character distribution that are continuous on
`G_reg(F)` agree on `G_reg(F)` (open, conull), so `characterOn π (regularSet …)` is canonical there.
Stated for the Haar measure `Measure.haar` used in `IsCharacterOf`. -/
axiom hc_regularSet_open_conull (d : GGPData F) :
    IsOpen (regularSet d.G d.lie) ∧
      (Measure.haar : Measure ↥d.G) (regularSet d.G d.lie)ᶜ = 0

/-! ## (b) Characters -/

/-- **(b) Harish-Chandra's regularity theorem.** For an irreducible tempered unitary
representation `π` of `G(F)`, the distribution `f ↦ tr π(f)` on `C_c^∞(G(F))` is given by a locally
integrable function which is locally constant on `G_reg(F)`.

Sources: Bernstein, *All reductive p-adic groups are tame* (Funct. Anal. Appl. 8, 1974) —
irreducible unitary representations are admissible, so `tr π(f)` is defined (`traceOf`);
Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (Univ. Lecture
Series 16, AMS 1999) (theorem number unverified) — the character of an admissible irreducible representation is a
locally integrable function, locally constant on `G_reg(F)` (characteristic `0`).
Thesis Ch. 1, BP §2.1 / Prop 4.1.1(i). -/
axiom hc_character_exists (d : GGPData F) (π : UnitaryRep ↥d.G) (hπ : IsTempered π) :
    ∃ θ : ↥d.G → ℂ, IsCharacterOf π θ ∧ ContinuousOn θ (regularSet d.G d.lie)

/-- `θ_π = characterOn π (regularSet d.G d.lie)` (Triple's `charG d π`) represents the character
of `π` and is continuous on `G_reg(F)` (from `hc_character_exists`). -/
theorem hc_character (d : GGPData F) (π : UnitaryRep ↥d.G) (hπ : IsTempered π) :
    IsCharacterOf π (characterOn π (regularSet d.G d.lie)) ∧
      ContinuousOn (characterOn π (regularSet d.G d.lie)) (regularSet d.G d.lie) :=
  characterOn_spec π _ (hc_character_exists d π hπ)

/-! ## (c) Characters are quasi-characters -/

/-- **(c) Harish-Chandra's local character expansion** (in the semisimple-descent form of
Waldspurger / BP). For `π` irreducible tempered, `θ_π` is a quasi-character on `G(F)`:
it is conjugation invariant on `G_reg(F)`, and at every semisimple `x ∈ G(F)` there are finitely
many coefficients `c_{θ_π,O}(x)`, `O ∈ Nil(𝔤_x)`, with
`θ_π(x e^X) = ∑_O c_{θ_π,O}(x) ĵ(O, X)` for `X ∈ 𝔤_x(F)` regular and close to `0`.

Sources: Harish-Chandra 1999 (op. cit.; theorem number unverified), local expansion at `x = 1`, with
semisimple descent; Waldspurger, *Une formule intégrale reliée à la conjecture locale de
Gross–Prasad* (Compositio 146, 2010), §4; BP Astérisque 418, Prop 4.1.1(i); Thesis Prop 4.1.1.1(i).
Here `ĵ` is normalized by `d.bilin` and `ψ` (Thesis §2.4); a rescaling of `ĵ` is absorbed by the
coefficients, so this axiom is insensitive to the measure normalization. -/
axiom hc_character_isQuasiCharacter (d : GGPData F) (ψ : NontrivialAddChar F)
    (π : UnitaryRep ↥d.G) (hπ : IsTempered π) :
    IsQuasiCharacter d.G d.lie d.bilin ψ (characterOn π (regularSet d.G d.lie))

/-! ## (d) Uniqueness of germs -/

/-- **(d) Linear independence of the `ĵ(O, ·)` (Harish-Chandra).** At a semisimple `x ∈ G(F)`, the
coefficients of a local expansion `θ(x e^X) = ∑_O c_O ĵ(O, X)` are unique on the regular orbits
`O ∈ Nil_reg(𝔤_x)`: the functions `ĵ(O, ·)`, `O ∈ Nil(𝔤_x)`, restricted to any neighbourhood of `0`
in `𝔤_{x,reg}(F)` are linearly independent (homogeneity `ĵ(O, t²X) = |t|^{-dim O} ĵ(O, X)` reduces
this to linear independence on all of `𝔤_x(F)`, Harish-Chandra), and `x e^X ∈ G(F)` for small
`X ∈ 𝔤_x(F)`.

Sources: Harish-Chandra, *Admissible invariant distributions…* (1999) (Fourier transforms of
nilpotent orbital integrals; theorem number unverified); BP Astérisque 418 §4.5 ("by homogeneity and
linear independence the `c_{θ,O}(x)`, `O ∈ Nil_reg(𝔤_x)`, are uniquely defined"); Thesis §4.2.

Only uniqueness on `Nil_reg` is asserted (that is all `germ` reads). -/
axiom germ_unique (d : GGPData F) (ψ : NontrivialAddChar F) (θ : ↥d.G → ℂ) (x : ↥d.G)
    (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    (c c' : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))
      → ℂ)
    (hc : HasGermExpansion d.G d.lie d.bilin ψ θ x c)
    (hc' : HasGermExpansion d.G d.lie d.bilin ψ θ x c') :
    ∀ O ∈ NilReg (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)),
      c O = c' O

section GermAlgebra

variable (d : GGPData F) (ψ : NontrivialAddChar F)

/-- With uniqueness (d), the germ `c_{θ,O}(x)` is the coefficient of *any* local expansion. -/
theorem germ_eq_of_hasGermExpansion {θ : ↥d.G → ℂ} {x : ↥d.G}
    (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    {c : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) → ℂ}
    (hc : HasGermExpansion d.G d.lie d.bilin ψ θ x c)
    {O} (hO : O ∈ NilReg (grpCentralizer d.G x)
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))) :
    germ d.G d.lie d.bilin ψ θ x O = c O := by
  have h : ∃ c, HasGermExpansion d.G d.lie d.bilin ψ θ x c := ⟨c, hc⟩
  simp only [germ, hO, h, ↓reduceIte, ↓reduceDIte]
  exact germ_unique d ψ θ x hx _ _ h.choose_spec hc O hO

/-- Local expansions add. -/
theorem hasGermExpansion_add {θ₁ θ₂ : ↥d.G → ℂ} {x : ↥d.G}
    {c₁ c₂ : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))
      → ℂ}
    (h₁ : HasGermExpansion d.G d.lie d.bilin ψ θ₁ x c₁)
    (h₂ : HasGermExpansion d.G d.lie d.bilin ψ θ₂ x c₂) :
    HasGermExpansion d.G d.lie d.bilin ψ (θ₁ + θ₂) x (c₁ + c₂) := by
  obtain ⟨hf₁, ω₁, hω₁, e₁⟩ := h₁
  obtain ⟨hf₂, ω₂, hω₂, e₂⟩ := h₂
  refine ⟨(hf₁.union hf₂).subset (Function.support_add _ _), ω₁ ∩ ω₂,
    Filter.inter_mem hω₁ hω₂, ?_⟩
  intro X hX hXg hXr y hy
  rw [Pi.add_apply, e₁ X hX.1 hXg hXr y hy, e₂ X hX.2 hXg hXr y hy, ← finsum_add_distrib]
  · exact finsum_congr fun O => by simp [add_mul]
  · exact hf₁.subset (Function.support_mul_subset_left _ _)
  · exact hf₂.subset (Function.support_mul_subset_left _ _)

/-- Local expansions scale. -/
theorem hasGermExpansion_smul {θ : ↥d.G → ℂ} {x : ↥d.G} (a : ℂ)
    {c : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) → ℂ}
    (h : HasGermExpansion d.G d.lie d.bilin ψ θ x c) :
    HasGermExpansion d.G d.lie d.bilin ψ (a • θ) x (a • c) := by
  obtain ⟨hf, ω, hω, e⟩ := h
  refine ⟨hf.subset (Function.support_const_smul_subset a c), ω, hω, ?_⟩
  intro X hX hXg hXr y hy
  rw [Pi.smul_apply, e X hX hXg hXr y hy, smul_eq_mul, mul_finsum]
  exact finsum_congr fun O => by simp [mul_assoc]

/-- The zero function has the zero expansion. -/
theorem hasGermExpansion_zero (x : ↥d.G) :
    HasGermExpansion d.G d.lie d.bilin ψ 0 x 0 := by
  refine ⟨by simp, Set.univ, Filter.univ_mem, ?_⟩
  intro X _ _ _ y _
  simp

/-- `c_{θ₁+θ₂,O}(x) = c_{θ₁,O}(x) + c_{θ₂,O}(x)` when both have local expansions at the
semisimple point `x` (e.g. both are quasi-characters). Used to compute the germs of the stable
characters `θ_α = ∑_{π ∈ Π_α} θ_π` (Thesis §6.7). -/
theorem germ_add {θ₁ θ₂ : ↥d.G → ℂ} {x : ↥d.G} (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    (h₁ : ∃ c, HasGermExpansion d.G d.lie d.bilin ψ θ₁ x c)
    (h₂ : ∃ c, HasGermExpansion d.G d.lie d.bilin ψ θ₂ x c)
    {O} (hO : O ∈ NilReg (grpCentralizer d.G x)
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))) :
    germ d.G d.lie d.bilin ψ (θ₁ + θ₂) x O =
      germ d.G d.lie d.bilin ψ θ₁ x O + germ d.G d.lie d.bilin ψ θ₂ x O := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  rw [germ_eq_of_hasGermExpansion d ψ hx (hasGermExpansion_add d ψ hc₁ hc₂) hO,
    germ_eq_of_hasGermExpansion d ψ hx hc₁ hO, germ_eq_of_hasGermExpansion d ψ hx hc₂ hO,
    Pi.add_apply]

/-- `c_{aθ,O}(x) = a · c_{θ,O}(x)` (used with `a = e(G_α)` in TRANS). -/
theorem germ_smul {θ : ↥d.G → ℂ} {x : ↥d.G} (hx : IsSS F ((x : d.ambientˣ) : d.ambient)) (a : ℂ)
    (h : ∃ c, HasGermExpansion d.G d.lie d.bilin ψ θ x c)
    {O} (hO : O ∈ NilReg (grpCentralizer d.G x)
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))) :
    germ d.G d.lie d.bilin ψ (a • θ) x O = a * germ d.G d.lie d.bilin ψ θ x O := by
  obtain ⟨c, hc⟩ := h
  rw [germ_eq_of_hasGermExpansion d ψ hx (hasGermExpansion_smul d ψ a hc) hO,
    germ_eq_of_hasGermExpansion d ψ hx hc hO, Pi.smul_apply, smul_eq_mul]

/-- The germs of the zero function vanish (at semisimple points). -/
theorem germ_zero {x : ↥d.G} (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    {O} (hO : O ∈ NilReg (grpCentralizer d.G x)
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))) :
    germ d.G d.lie d.bilin ψ 0 x O = 0 :=
  germ_eq_of_hasGermExpansion d ψ hx (hasGermExpansion_zero d ψ x) hO

/-- Finite sums of functions with local expansions have local expansions. -/
theorem exists_hasGermExpansion_finset_sum {ι : Type*} (s : Finset ι) (θ : ι → ↥d.G → ℂ)
    {x : ↥d.G} (h : ∀ i ∈ s, ∃ c, HasGermExpansion d.G d.lie d.bilin ψ (θ i) x c) :
    ∃ c, HasGermExpansion d.G d.lie d.bilin ψ (∑ i ∈ s, θ i) x c := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa using hasGermExpansion_zero d ψ x⟩
  | insert i s hi ih =>
    obtain ⟨c₁, hc₁⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨c₂, hc₂⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi]
    exact ⟨_, hasGermExpansion_add d ψ hc₁ hc₂⟩

/-- `c_{∑ θ_i, O}(x) = ∑ c_{θ_i, O}(x)` for a finite family with local expansions at the
semisimple point `x` (e.g. the characters of an `L`-packet, by (c)). -/
theorem germ_finset_sum {ι : Type*} (s : Finset ι) (θ : ι → ↥d.G → ℂ) {x : ↥d.G}
    (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    (h : ∀ i ∈ s, ∃ c, HasGermExpansion d.G d.lie d.bilin ψ (θ i) x c)
    {O} (hO : O ∈ NilReg (grpCentralizer d.G x)
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))) :
    germ d.G d.lie d.bilin ψ (∑ i ∈ s, θ i) x O = ∑ i ∈ s, germ d.G d.lie d.bilin ψ (θ i) x O := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using germ_zero d ψ hx hO
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, ∃ c, HasGermExpansion d.G d.lie d.bilin ψ (θ j) x c :=
      fun j hj => h j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      germ_add d ψ hx (h i (Finset.mem_insert_self i s))
        (exists_hasGermExpansion_finset_sum d ψ s θ hs) hO, ih hs]

/-! ### Quasi-characters form a vector space (needed to apply (e) to `e · ∑_{π ∈ Π} θ_π`) -/

theorem isQuasiCharacter_zero : IsQuasiCharacter d.G d.lie d.bilin ψ 0 :=
  ⟨fun _ _ _ => rfl, fun x _ => ⟨0, hasGermExpansion_zero d ψ x⟩⟩

theorem isQuasiCharacter_add {θ₁ θ₂ : ↥d.G → ℂ} (h₁ : IsQuasiCharacter d.G d.lie d.bilin ψ θ₁)
    (h₂ : IsQuasiCharacter d.G d.lie d.bilin ψ θ₂) :
    IsQuasiCharacter d.G d.lie d.bilin ψ (θ₁ + θ₂) := by
  refine ⟨fun g y hy => by simp [h₁.1 g y hy, h₂.1 g y hy], fun x hx => ?_⟩
  obtain ⟨c₁, hc₁⟩ := h₁.2 x hx
  obtain ⟨c₂, hc₂⟩ := h₂.2 x hx
  exact ⟨_, hasGermExpansion_add d ψ hc₁ hc₂⟩

theorem isQuasiCharacter_smul (a : ℂ) {θ : ↥d.G → ℂ} (h : IsQuasiCharacter d.G d.lie d.bilin ψ θ) :
    IsQuasiCharacter d.G d.lie d.bilin ψ (a • θ) := by
  refine ⟨fun g y hy => by simp [h.1 g y hy], fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := h.2 x hx
  exact ⟨_, hasGermExpansion_smul d ψ a hc⟩

theorem isQuasiCharacter_finset_sum {ι : Type*} (s : Finset ι) (θ : ι → ↥d.G → ℂ)
    (h : ∀ i ∈ s, IsQuasiCharacter d.G d.lie d.bilin ψ (θ i)) :
    IsQuasiCharacter d.G d.lie d.bilin ψ (∑ i ∈ s, θ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isQuasiCharacter_zero d ψ
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact isQuasiCharacter_add d ψ (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end GermAlgebra

/-! ## (e) Transfer preserves germs -/

/-- **(e) Beuzart-Plessis (12.1.2)** (Thesis (6.1.2)), for the inner twists of `GSpin`.
Let `G` be quasi-split, `τ` an inner twist (`G_α = (d.twist τ).G`), `θ` a *stable*
quasi-character on `G(F)` and `θ'` a stable quasi-character on `G_α(F)` which is a *transfer* of
`θ`: `θ'(y) = θ(x)` whenever `x ∈ G_reg(F)`, `y ∈ G_{α,reg}(F)` are stably conjugate through
`ψ_α = C(φ) × C(φ ⊕ id_Z)`. Then for `x ∈ GSpin(W)(F)`, `y ∈ GSpin(W_α)(F)` semisimple and strongly
stably conjugate (embedded diagonally), `c_{θ',O'}(y) = c_{θ,O}(x)` for all `O ∈ Nil_reg(𝔤_x)`,
`O' ∈ Nil_reg(𝔤_{α,y})`. (For stable `θ` the regular germs do not depend on the orbit; the
equality then follows from the limit formula BP Prop 4.5.1(ii) along a maximal torus of `G_x`
transported to `G_{α,y}`.)

Sources: Beuzart-Plessis, *A local trace formula for the Gan–Gross–Prasad conjecture for unitary
groups: the archimedean case* (Astérisque 418, 2020), (12.1.2) (as cited in Thesis §6.1) — stated there for pure inner
forms; here it is used for the inner twists of `GSpin` with cocycle in `SO(W) × SO(V)`, for
which the proof is unchanged. Stability and transfer are written out inline (Triple's
`IsStableFn` is not visible here). Only diagonal elements are needed (Thesis §6.7). -/
axiom bp_germ_transfer (d : GGPData F) (hqs : d.IsQuasiSplit) (ψ : NontrivialAddChar F)
    (τ : InnerTwist d.QW) (θ : ↥d.G → ℂ) (θ' : ↥(d.twist τ).G → ℂ)
    (hθ : IsQuasiCharacter d.G d.lie d.bilin ψ θ)
    (hθ' : IsQuasiCharacter (d.twist τ).G (d.twist τ).lie (d.twist τ).bilin ψ θ')
    (hstab : ∀ x ∈ regularSet d.G d.lie, ∀ x' ∈ regularSet d.G d.lie,
      d.StablyConj x x' → θ x = θ x')
    (hstab' : ∀ y ∈ regularSet (d.twist τ).G (d.twist τ).lie,
      ∀ y' ∈ regularSet (d.twist τ).G (d.twist τ).lie,
      (d.twist τ).StablyConj y y' → θ' y = θ' y')
    (htrans : ∀ x ∈ regularSet d.G d.lie, ∀ y ∈ regularSet (d.twist τ).G (d.twist τ).lie,
      d.StablyConjG τ x y → θ' y = θ x)
    (x : GSpin d.QW) (y : GSpin (d.twist τ).QW)
    (hx : IsSS F (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient))
    (hy : IsSS F ((((d.twist τ).diag y : ↥(d.twist τ).G) : (d.twist τ).ambientˣ) :
      (d.twist τ).ambient))
    (hxy : d.StronglyStablyConjW τ x y) :
    ∀ O ∈ NilReg (grpCentralizer d.G (d.diag x))
        (lieCentralizer d.lie (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient)),
    ∀ O' ∈ NilReg (grpCentralizer (d.twist τ).G ((d.twist τ).diag y))
        (lieCentralizer (d.twist τ).lie
          ((((d.twist τ).diag y : ↥(d.twist τ).G) : (d.twist τ).ambientˣ) : (d.twist τ).ambient)),
      germ (d.twist τ).G (d.twist τ).lie (d.twist τ).bilin ψ θ' ((d.twist τ).diag y) O' =
        germ d.G d.lie d.bilin ψ θ (d.diag x) O

/-! ## (f) Germs at the identity and Whittaker models -/

/-- **(f) Rodier; Mœglin–Waldspurger** (BP Prop 4.8.1(i), Thesis Prop 4.4.1(i)). Let `G` be
quasi-split. For each regular nilpotent orbit `O ∈ Nil_reg(𝔤)` there is a Whittaker datum
`(U, χ)` — namely `(U_O, ξ_O)`, `ξ_O(u) = ψ(b(Y, log u))` for `Y` in an `𝔰𝔩₂`-triple opposite to
`O` (Thesis §4.4) — such that for every irreducible tempered `π`,
`c_{θ_π,O}(1) = 1` if `π` has a `(U, χ)`-Whittaker model and `0` otherwise.

Sources: Rodier, *Modèle de Whittaker et caractères de représentations* (LNM 466, 1975);
Mœglin–Waldspurger, *Modèles de Whittaker dégénérés pour des groupes p-adiques* (Math. Z. 196,
1987) (theorem numbers unverified); BP Astérisque 418, Prop 4.8.1(i).

The identity is passed as `x` with `hx : x = 1`, so that the orbit type
`NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie x)` matches whatever form of `1` the
consumer has (e.g. `d.diag 1`); `grpCentralizer d.G 1 = d.G` (`grpCentralizer_one`).
Only the existence of *some* datum per orbit is asserted.

**Normalization risk.** Unlike (c)–(e), the value `1` depends on the
normalization of `ĵ(O,·)`: self-dual Haar measure on `𝔤(F)` for `(d.bilin, ψ)` and the Kirillov
measure on `O` self-dual for `ψ ∘ ω_X`, `ω_X(Y,Z) = b(Y,[X,Z])` (Thesis §2.4 = BP §1.6). This is the
normalization of `LocalGroups.IsOrbitMeasure`; if that definition deviated from BP's, this axiom
would be false. Checked on `𝔰𝔩₂`/`GL₂` (two independent hand computations, any residue
characteristic including `2`): the Lean normalization gives germ `1` for a principal series
(`Sanity/NilpotentOrbit.lean`). -/
axiom rodier_germ_one (d : GGPData F) (hqs : d.IsQuasiSplit) (ψ : NontrivialAddChar F)
    (x : ↥d.G) (hx : x = 1)
    (O : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)))
    (hO : O ∈ NilReg (grpCentralizer d.G x)
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))) :
    ∃ w : WhittakerDatum d, ∀ π : UnitaryRep ↥d.G, IsTempered π →
      (HasModel π w.U w.χ →
          germ d.G d.lie d.bilin ψ (characterOn π (regularSet d.G d.lie)) x O = 1) ∧
        (¬ HasModel π w.U w.χ →
          germ d.G d.lie d.bilin ψ (characterOn π (regularSet d.G d.lie)) x O = 0)

/-- `G_1 = G`. -/
theorem grpCentralizer_one {A : Type*} [Ring A] (G : Subgroup Aˣ) : grpCentralizer G 1 = G := by
  ext g
  simp [grpCentralizer, Subgroup.mem_centralizer_iff]

/-- `𝔤_1 = 𝔤`. -/
theorem lieCentralizer_one {A : Type*} [Ring A] [Algebra F A] (𝔤 : LieSubalgebra F A) :
    lieCentralizer 𝔤 (1 : A) = 𝔤 := by
  ext X
  simp [mem_lieCentralizer]

/-! ## (g) Schur's lemma -/

/-- **(g) Schur's lemma for unitary representations.** The centre of `G` acts by scalars in an
irreducible unitary representation (the commutant of an irreducible unitary representation is
`ℂ · 1`, by the spectral theorem). Dixmier, *C\*-algebras* (1977) (section unverified); used for the
central character of tempered representations (Thesis §3.1.2). No reductive-group
hypothesis is needed, so it is stated for any topological group. -/
axiom schur_central {G : Type*} [Group G] [TopologicalSpace G] (π : UnitaryRep G)
    (hπ : π.IsIrreducible) :
    ∃ χ : ↥(Subgroup.center G) → ℂ, HasCentralChar π (Subgroup.center G) χ

end GSpinGGP
