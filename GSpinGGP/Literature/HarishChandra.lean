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
to the inner forms `d.twist τ` as well (those are not quasi-split; no axiom below except (f)
assumes quasi-splitness).

Since `GGP/Triple.lean` is in the same layer and not visible here, the character
`θ_π = characterOn π (regularSet d.G d.lie)` (= Triple's `charG d π`) and stability/transfer are
written out inline.

## Contents
* (a) `hc_regular_open_dense_conull` — Harish-Chandra's `G' = {D ≠ 0}` is open, dense and conull
  (`hcDisc`);
* instances `T2Space ↥d.G`, `LocallyCompactSpace ↥d.G` (theorems of LocalGroups, made instances
  here because `F` is recoverable from `d`);
* (b) `hc_character_exists` — `θ_π` is a function, continuous on Harish-Chandra's `G' = {D ≠ 0}`
  (Harish-Chandra's regularity theorem; Bernstein's admissibility); the form on `G_reg(F)` is
  `hc_character` in `GGP/Germs.lean`;
* (c) `hc_character_isQuasiCharacter` — `θ_π` is a quasi-character (HC local character expansion;
  BP Prop 4.1.1(i), Thesis Prop 4.1.1.1);
* (d) `germ_unique` — uniqueness of the local expansion (linear independence of the `ĵ(O,·)`,
  Harish-Chandra; BP §4.5, Thesis §4.2); derived: `germ_eq_of_hasGermExpansion`, `germ_add`,
  `germ_smul`, `germ_finset_sum`, `germ_zero`;
* (f) `rodier_germ_one` — BP Prop 4.8.1(i) = Thesis Prop 4.4.1(i) (Rodier, Mœglin–Waldspurger);
* (g) `dixmier_commutant_scalar` — Schur's lemma (Dixmier 13.1.4); `schur_central` (the centre acts
  by scalars) is proved from it.

Not needed as an axiom: BP Prop 4.5.1(i) (`c_θ(x) = 0` if `G_x` is not quasi-split) — `germ` is
`0` off `NilReg` by definition (`germ_of_not_mem`), and `NilReg(𝔤_x) = ∅ ↔ G_x` not quasi-split
is a GSpin fact (`GGP/Centralizers.lean`).

`GGP/Germs.lean` derives `hc_regularSet_open_conull` from (a) and the identification of `G'` with
`regularSet`; `bp_germ_transfer` (not verbatim in the literature) is proved there from
`bp_germAvg_transfer` (proved there by transport along the `F`-isomorphism `G_x ≃ G_{α,y}`, from the
`sorry` theorems `exists_centralizerIso_of_stronglyStablyConjW`, `jHat_centralizerIso`) and the `sorry`
theorems `germ_eq_germ_of_stable`, `finite_nilReg`.
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

/-! ## (b) Characters -/

/-! ## (a) The regular set (Harish-Chandra) -/

open Classical in
/-- Harish-Chandra's discriminant `D(x)`: the coefficient of `t^ℓ`, `ℓ = rank G`, in
`det(t − 1 + Ad(x))`, i.e. in the characteristic polynomial of `1 − Ad(x)` on
`𝔤 = gspin(W) × gspin(V)` (`0` if `𝔤` is not `Ad(x)`-stable, which does not happen). The rank is
the intrinsic `lieRank 𝔤` (the minimal dimension of a centralizer `𝔤_X`, which is the dimension of a
Cartan subalgebra), not a formula in `dim W`, `dim V`. -/
def hcDisc (d : GGPData F) (x : ↥d.G) : F :=
  if h : ∀ X ∈ d.lie.toSubmodule, conjAd F (x : d.ambientˣ) X ∈ d.lie.toSubmodule then
    (LinearMap.charpoly (1 - (conjAd F (x : d.ambientˣ)).toLinearEquiv.toLinearMap.restrict h)).coeff
      (lieRank d.lie)
  else 0

/-- **Harish-Chandra: the regular set is open, dense and conull.** Harish-Chandra, *Harmonic
analysis on reductive p-adic groups* (notes by G. van Dijk), LNM 162 (1970), Part V §3, p. 54
(the Introduction, p. 2, writes `det(t + 1 − Ad(x))` instead; the coefficient changes by the sign
`(−1)^{dim 𝔤 − ℓ}`, so `G'` is the same): let `G` be a connected reductive linear algebraic group over a `p`-adic
field and `G` its group of rational points. For `x ∈ G` write
`det(t − 1 + Ad(x)) = D(x) t^ℓ + …` (terms of higher degree), `ℓ = rank G`; then
`G' = {x ∈ G : D(x) ≠ 0}` is an open and dense subset of `G`, whose complement has Haar measure
zero. Specialized to the connected reductive group `G = GSpin(W) × GSpin(V)` (Lie algebra
`gspin(W) × gspin(V)`, `D = hcDisc`, `ℓ = lieRank 𝔤`). -/
axiom hc_regular_open_dense_conull (d : GGPData F) :
    IsOpen {x : ↥d.G | hcDisc d x ≠ 0} ∧ Dense {x : ↥d.G | hcDisc d x ≠ 0} ∧
      (Measure.haar : Measure ↥d.G) {x : ↥d.G | hcDisc d x ≠ 0}ᶜ = 0

/-- **(b) Harish-Chandra's regularity theorem.** For an irreducible tempered unitary
representation `π` of `G(F)`, the distribution `f ↦ tr π(f)` on `C_c^∞(G(F))` is given by a locally
integrable function which is locally constant on `G' = {D ≠ 0}`.

Sources:
* Bernstein, *All reductive p-adic groups are tame*, Funct. Anal. Appl. 8 (1974), 91–93, Thm 1.
  For `G` the group of `F`-points of a reductive group over a non-archimedean local field and
  `K ⊆ G` compact open, `dim V^K` is bounded over all irreducible unitary `(π, V)`. In particular
  `π` is admissible, so `tr π(f)` is defined (`traceOf`).
* Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, Univ. Lecture
  Series 16, AMS 1999, Thm 16.3 (= Theorem 1 of the introduction; proved in §21). For `G` the
  `F`-points of a connected reductive group, `char F = 0`, the character `Θ_π` of an admissible
  irreducible `π` is a locally summable function on `G`, locally constant on
  `G' = {x : D_G(x) ≠ 0}`.

Harish-Chandra's `G'` is `{x | hcDisc d x ≠ 0}` (as in `hc_regular_open_dense_conull`), and the
conclusion is stated on that set, verbatim; its identification with `regularSet` is a separate
theorem (`hcDisc_ne_zero_iff_mem_regularSet`, GGP/Germs). Only continuity on `G'` is stated, which is
weaker than local constancy. Thesis Ch. 1, BP §2.1 / Prop 4.1.1(i).

One step of the chain is not covered by an exact citation yet: for a topologically irreducible
unitary `π`, the smooth vectors `π^∞` form an (algebraically) irreducible admissible representation,
and its character `f ↦ tr π^∞(f)` is `traceOf π` (the trace on `π^K`). Bernstein's Thm 1 gives
admissibility; the irreducibility of `π^∞` is standard but its source is still to be pinned down. -/
axiom hc_character_exists (d : GGPData F) (π : UnitaryRep ↥d.G) (hπ : IsTempered π) :
    ∃ θ : ↥d.G → ℂ, IsCharacterOf π θ ∧ ContinuousOn θ {x : ↥d.G | hcDisc d x ≠ 0}

/-! ## (c) Characters are quasi-characters -/

/-- **(c) Harish-Chandra's local character expansion** (in the semisimple-descent form of
Waldspurger / BP). For `π` irreducible tempered, `θ_π` is a quasi-character on `G(F)`:
it is conjugation invariant on `G_reg(F)`, and at every semisimple `x ∈ G(F)` there are finitely
many coefficients `c_{θ_π,O}(x)`, `O ∈ Nil(𝔤_x)`, with
`θ_π(x e^X) = ∑_O c_{θ_π,O}(x) ĵ(O, X)` for `X ∈ 𝔤_x(F)` regular and close to `0`.

Sources: Harish-Chandra 1999 (op. cit.), Thm 16.2 (= Theorems 5 and 20): for `γ` semisimple,
with `M`, `𝔪` its centralizers in `G`, `𝔤`, there are unique `c_ξ` with
`Θ_π(γ exp Y) = Σ_ξ c_ξ μ̂_ξ(Y)` for `Y` close to `0` in `𝔪`, `ξ` running over the nilpotent
`M`-orbits in `𝔪` (applied with the admissibility of `Θ_π` at `γ`, §15); BP Astérisque 418,
Prop 4.1.1(i): "for every irreducible admissible representation `π` of `G(F)`, the character `θ_π`
is a quasi-character on `G(F)`", which is the form stated here (BP §4.1's definition);
Waldspurger, Compositio 146 (2010), §4; Thesis Prop 4.1.1.1(i).
Here `ĵ` is normalized by `d.bilin` and `ψ` (Thesis §2.4); a change of invariant form or of measures
permutes and rescales the `ĵ(O,·)`, which is absorbed by the coefficients, so this axiom is
insensitive to the normalization. -/
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

Sources: Harish-Chandra, *Admissible invariant distributions…* (1999), Cor 5.10 (and Thm 5.11 =
Theorem 4): for a reductive Lie algebra `𝔤` over `F` and any open neighbourhood `V` of `0`, the
functions `μ̂_O`, `O` a nilpotent orbit, are linearly independent on `V ∩ 𝔤'` (applied to
`𝔤_x`, p. 36; a different invariant form or normalization rescales and relabels the `μ̂_O`, which
does not affect independence; `G_x` is connected for `GSpin`, whose derived group is simply connected
(Steinberg), and HC's footnote 4, p. 75, covers disconnected centralizers anyway); BP Astérisque 418
§4.5, p. 96 ("by
homogeneity and linear independence the `c_{θ,O}(x)`, `O ∈ Nil_reg(𝔤_x)`, are uniquely defined"); Thesis §4.2.

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

/-! ## (f) Germs at the identity and Whittaker models -/

/-- **(f) Rodier; Mœglin–Waldspurger** (BP Prop 4.8.1(i), Thesis Prop 4.4.1(i)). Let `G` be
quasi-split. For each regular nilpotent orbit `O ∈ Nil_reg(𝔤)` there is a Whittaker datum
`(U, χ)` — namely `(U_O, ξ_O)`, `ξ_O(u) = ψ(b(Y, log u))` for `Y` in an `𝔰𝔩₂`-triple opposite to
`O` (Thesis §4.4) — such that for every irreducible tempered `π`,
`c_{θ_π,O}(1) = 1` if `π` has a `(U, χ)`-Whittaker model and `0` otherwise.

Sources: Rodier, *Modèle de Whittaker et caractères de représentations* (LNM 466, 1975);
Mœglin–Waldspurger, *Modèles de Whittaker dégénérés pour des groupes p-adiques* (Math. Z. 196,
1987), Thm I.16 and Cor I.17; BP Astérisque 418, Prop 4.8.1(i).

**Residue characteristic.** BP states Prop 4.8.1(i) for every `p`-adic field, and so does this
axiom. Mœglin–Waldspurger assume the residue characteristic is not `2` (their introduction), and
Rodier treats split groups. The remaining case is S. Varma, *On a result of Moeglin and
Waldspurger in residual characteristic 2*, Math. Z. 277 (2014), doi:10.1007/s00209-014-1292-8,
Thm 1: for `F` `p`-adic of any residue characteristic, `G` connected reductive and `π` smooth of
finite length, the maximal orbits with `c_O ≠ 0` are the maximal orbits carrying a nonzero space
of degenerate Whittaker forms, and for such `O` the coefficient `c_O` is the dimension of that
space. A regular nilpotent orbit is maximal, so `c_O` is that dimension (`0` if the space is `0`).

The identity is passed as `x` with `hx : x = 1`, so that the orbit type
`NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie x)` matches whatever form of `1` the
consumer has (e.g. `d.diag 1`); `grpCentralizer d.G 1 = d.G` (`grpCentralizer_one`).
Only the existence of *some* datum per orbit is asserted.

**Normalization risk.** Unlike (c)–(e), the value `1` depends on the
normalization of `ĵ(O,·)`: self-dual Haar measure on `𝔤(F)` for `(d.bilin, ψ)` and the Kirillov
measure on `O` self-dual for `ψ ∘ ω_X`, `ω_X(Y,Z) = b(Y,[X,Z])` (Thesis §2.4 = BP §1.6). This is the
normalization of `LocalGroups.IsOrbitMeasure`; if that definition deviated from BP's, this axiom
would be false. Checked by hand on `𝔰𝔩₂`/`GL₂` (two independent computations, any residue
characteristic including `2`): the Lean normalization gives germ `1` for a principal series.
`Sanity/NilpotentOrbit.lean` records the values of these hand computations as `sorry` statements;
they are not checked by Lean. -/
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

/-- **(g) Schur's lemma for unitary representations** (Dixmier, *Les C\*-algèbres et leurs
représentations*, Gauthier-Villars 1964, 13.1.4, p. 250, (i) ⇒ (ii); the same for involutive algebras is
2.3.1): for a continuous unitary representation `π` of a topological group `G` whose only closed
`π(G)`-stable subspaces are `0` and `H`, the commutant of `π(G)` in `L(H)` consists of the scalars.
Our `UnitaryRep` is strongly continuous, which is Dixmier's continuity (13.1.1, 13.1.2), and
`IsIrreducible` is his condition (i) together with `H ≠ 0`.  Dixmier's `G` is a topological group;
only the topology of `G` enters (through continuity), so the axiom is stated for a group with a
topology, as used here (in fact only with the discrete topology). -/
axiom dixmier_commutant_scalar {G : Type*} [Group G] [TopologicalSpace G] (π : UnitaryRep G)
    (hπ : π.IsIrreducible) (T : π.H →L[ℂ] π.H) (hT : ∀ g, T * π.ρ g = π.ρ g * T) :
    ∃ c : ℂ, T = c • (1 : π.H →L[ℂ] π.H)

/-- **The centre acts by scalars** in an irreducible unitary representation (used for the central
character of tempered representations, Thesis §3.1.2): `π(z)` commutes with `π(G)` for `z` central,
so it is a scalar by `dixmier_commutant_scalar`. -/
theorem schur_central {G : Type*} [Group G] [TopologicalSpace G] (π : UnitaryRep G)
    (hπ : π.IsIrreducible) :
    ∃ χ : ↥(Subgroup.center G) → ℂ, HasCentralChar π (Subgroup.center G) χ := by
  choose χ hχ using fun z : ↥(Subgroup.center G) =>
    dixmier_commutant_scalar π hπ (π.ρ z) fun g => by
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 z.2 g).symm]
  exact ⟨χ, hχ⟩

end GSpinGGP
