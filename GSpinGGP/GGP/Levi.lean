import GSpinGGP.GGP.Triple
import GSpinGGP.Literature.GSpin
import GSpinGGP.Literature.HarishChandra
import GSpinGGP.Literature.TraceFormula
import GSpinGGP.Literature.Parabolic

/-!
# Isomorphisms of GGP triples, and the Levi subgroups of `G`

## 1. Isomorphisms of GGP triples

A GGP triple `(G, H, ξ)` is only "well defined up to conjugacy" (Thesis §9.3 after (9.3.3)):
the triples attached to the Levi subgroups, or to centralizers in the descent,
are given only up to isomorphism.  `GGPIso d d'` packages such an isomorphism.

It is *one* `F`-algebra isomorphism `alg : C(W) × C(V) ≃ C(W') × C(V')` of the ambient algebras
that carries `G` onto `G'`, `H` onto `H'`, `𝔤` onto `𝔤'`, and `λ` to `λ'` (so `ξ' ∘ e = ξ` for every
`ψ`).  The group isomorphism `e : G(F) ≃ G'(F)` is derived from it, and is automatically a
homeomorphism (`alg` is linear between finite-dimensional spaces); the compatibility of the
invariant forms `bilin` is a theorem (`GGPIso.bilin_alg`), as is the transport of the regular set.

Transport along `e` (proved): temperedness `isTempered_congr_iso`, the multiplicity
`mult_congr_iso`, the character on the regular set `charG_congr_iso` (from the Harish-Chandra
axioms `hc_character_exists`, `hc_regularSet_open_conull`), `A_{G,H}` (`mem_AGH_iff`) and the
regular set (`mem_regularSet_iff`).  Representations of `G'(F)` are pulled back along `e`
(`GGPIso.pullback`); the generic transport lemmas (Haar measure, `π(f)`, traces, characters,
weak containment in the regular representation) are in §2–§3 of this file, for any isomorphism of
second-countable locally compact groups.
Transport of `m_geom` (`mGeom_congr_iso`) is left as `sorry`.

## 2. The Levi subgroups (Thesis §5.1.2, §9.3 (9.3.1)–(9.3.3))

For a pair of isotropic flags `(F_W, F_V)`, the Levi of `P = P_{F_W} × P_{F_V}` is
`∏ GL(Z_{i,W}) × ∏ GL(Z_{j,V}) × GSpin(W̃) × GSpin(Ṽ)`, where `W = H^{a_W} ⊥ W̃` with
`a_W = dim F_W.top`, likewise for `V`, and `(W̃, Ṽ)` is admissible *up to permutation*.
`leviSmall d FW FV` is a GGP datum for `(W̃, Ṽ)` (epsilon pattern from the specification
`LeviSpec`); `dimG_leviSmall_lt` is what the induction on `dim G` uses.  The existence of such a
datum (`exists_leviSpec`) is proved (§4a: hyperbolic splitting, `Z ≅ H^r ⊥ ⟨ν⟩`, `H ≅ ⟨ν⟩ ⊥ ⟨-ν⟩`,
from the cited Witt decomposition and Witt cancellation).  The description of the Levi quotient
`P/U` (`exists_leviHom_of_leviSpec`) is stated precisely and left as `sorry`.

## 6–7. Parabolic induction and `R_ind`

`GGPData.parInd`: normalized parabolic induction `i_P^G(σ)` as a `UnitaryRep` (real data; proved
from the integration formula for `G = P K`, `Literature/Parabolic.lean`, and the unimodularity of `G(F)`).  `GGPData.Rind`: the properly induced virtual representations, defined at the
level of characters.

Design note: `GGPIso` has no factor swap `GSpin(W̃)×GSpin(Ṽ) ≅ GSpin(Ṽ)×GSpin(W̃)`.  Between two
`GGPData` it can never occur (`dim W < dim V` always); the swap lives in `LeviSpec` (its second
disjunct).
-/

noncomputable section

open MeasureTheory Filter Topology Module
open scoped Classical

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-! ## 0. Instances -/

namespace LeviAux

/-- The ambient algebra `C(W) × C(V)` is second countable (`F` is proper, `C(W) × C(V) ≅ F^n`;
the same proof as `TraceFormula/Basic.lean`, redeclared since this file does not import it). -/
theorem secondCountableTopology_ambient (d : GGPData F) : SecondCountableTopology d.ambient := by
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  exact (toPiCLE F d.ambient).toHomeomorph.secondCountableTopology

/-- `G(F)` is second countable. -/
instance secondCountableTopology_G (d : GGPData F) : SecondCountableTopology ↥d.G := by
  have := secondCountableTopology_ambient d
  have : SecondCountableTopology d.ambientᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := d.ambient)).symm.secondCountableTopology
  have : SecondCountableTopology d.ambientˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

end LeviAux

open LeviAux

/-! ## 1. Isomorphisms of GGP triples -/

namespace GGPData

/-- The units map `(C(W) × C(V))ˣ ≃* (C(W') × C(V'))ˣ` induced by an algebra isomorphism. -/
abbrev unitsOf {d d' : GGPData F} (alg : d.ambient ≃ₐ[F] d'.ambient) :
    d.ambientˣ ≃* d'.ambientˣ :=
  Units.mapEquiv alg.toRingEquiv.toMulEquiv

@[simp] theorem coe_unitsOf {d d' : GGPData F} (alg : d.ambient ≃ₐ[F] d'.ambient) (u : d.ambientˣ) :
    ((unitsOf alg u : d'.ambientˣ) : d'.ambient) = alg (u : d.ambient) := rfl

theorem unitsOf_refl {d : GGPData F} (u : d.ambientˣ) :
    unitsOf (AlgEquiv.refl : d.ambient ≃ₐ[F] d.ambient) u = u := Units.ext rfl

theorem unitsOf_symm_apply {d d' : GGPData F} (alg : d.ambient ≃ₐ[F] d'.ambient)
    (u : d'.ambientˣ) : unitsOf alg (unitsOf alg.symm u) = u :=
  Units.ext (alg.apply_symm_apply (u : d'.ambient))

/-- The group isomorphism `G(F) ≃ G'(F)` induced by an algebra isomorphism carrying `G` onto `G'`. -/
def isoG {d d' : GGPData F} (alg : d.ambient ≃ₐ[F] d'.ambient)
    (mem_G : ∀ u : d.ambientˣ, u ∈ d.G ↔ unitsOf alg u ∈ d'.G) : ↥d.G ≃* ↥d'.G where
  toFun g := ⟨unitsOf alg g, (mem_G g).1 g.2⟩
  invFun g := ⟨(unitsOf alg).symm g, (mem_G _).2 (by rw [MulEquiv.apply_symm_apply]; exact g.2)⟩
  left_inv g := Subtype.ext ((unitsOf alg).symm_apply_apply (g : d.ambientˣ))
  right_inv g := Subtype.ext ((unitsOf alg).apply_symm_apply (g : d'.ambientˣ))
  map_mul' g h := Subtype.ext (map_mul (unitsOf alg) (g : d.ambientˣ) h)

@[simp] theorem coe_isoG {d d' : GGPData F} (alg : d.ambient ≃ₐ[F] d'.ambient)
    (mem_G : ∀ u : d.ambientˣ, u ∈ d.G ↔ unitsOf alg u ∈ d'.G) (g : ↥d.G) :
    (((isoG alg mem_G g : ↥d'.G) : d'.ambientˣ) : d'.ambient) = alg ((g : d.ambientˣ) : d.ambient) :=
  rfl

end GGPData

/-- An isomorphism of GGP triples `(G, H, ξ) ≅ (G', H', ξ')` (Thesis §9.3, the
triple attached to `(W̃, Ṽ)` "well-defined up to conjugation").

It is given by an `F`-algebra isomorphism `alg` of the ambient algebras `C(W) × C(V)` that
* carries `G(F)` onto `G'(F)` (`mem_G`), hence induces `e : G(F) ≃ G'(F)` (`GGPIso.e`);
* carries `H(F)` onto `H'(F)` (`mem_H`);
* carries the Lie algebra `𝔤` onto `𝔤'` (`mem_lie`) — the compatible Lie algebra isomorphism;
* carries `λ` to `λ'` (`lam_eq`), so `ξ' ∘ e = ξ` for every additive character `ψ`.

Homeomorphy of `e` and `bilin' ∘ alg = bilin` are consequences (`GGPIso.continuous_e`,
`GGPIso.bilin_alg`). -/
structure GGPIso (d d' : GGPData F) where
  /-- the algebra isomorphism of the ambient algebras -/
  alg : d.ambient ≃ₐ[F] d'.ambient
  /-- `alg` carries `G` onto `G'` -/
  mem_G : ∀ u : d.ambientˣ, u ∈ d.G ↔ GGPData.unitsOf alg u ∈ d'.G
  /-- `alg` carries `H` onto `H'` -/
  mem_H : ∀ g : ↥d.G, g ∈ d.H ↔ GGPData.isoG alg mem_G g ∈ d'.H
  /-- `alg` carries `𝔤` onto `𝔤'` -/
  mem_lie : ∀ X : d.ambient, X ∈ d.lie ↔ alg X ∈ d'.lie
  /-- `λ' ∘ e = λ` on `H` -/
  lam_eq : ∀ (h : ↥d.G) (hh : h ∈ d.H),
    d'.lam ⟨GGPData.isoG alg mem_G h, (mem_H h).1 hh⟩ = d.lam ⟨h, hh⟩

namespace GGPIso

variable {d d' d'' : GGPData F}

/-- The induced group isomorphism `e : G(F) ≃* G'(F)`. -/
def e (Φ : GGPIso d d') : ↥d.G ≃* ↥d'.G := GGPData.isoG Φ.alg Φ.mem_G

@[simp] theorem coe_e (Φ : GGPIso d d') (g : ↥d.G) :
    (((Φ.e g : ↥d'.G) : d'.ambientˣ) : d'.ambient) = Φ.alg ((g : d.ambientˣ) : d.ambient) := rfl

@[simp] theorem coe_e_symm (Φ : GGPIso d d') (g : ↥d'.G) :
    (((Φ.e.symm g : ↥d.G) : d.ambientˣ) : d.ambient) = Φ.alg.symm ((g : d'.ambientˣ) : d'.ambient) :=
  rfl

/-- The identity isomorphism. -/
def refl (d : GGPData F) : GGPIso d d where
  alg := AlgEquiv.refl
  mem_G u := by rw [GGPData.unitsOf_refl]
  mem_H g := by
    have : GGPData.isoG (AlgEquiv.refl : d.ambient ≃ₐ[F] d.ambient)
        (fun u => by rw [GGPData.unitsOf_refl]) g = g := Subtype.ext (GGPData.unitsOf_refl _)
    rw [this]
  mem_lie X := Iff.rfl
  lam_eq h hh := rfl

/-- The inverse isomorphism. -/
def symm (Φ : GGPIso d d') : GGPIso d' d where
  alg := Φ.alg.symm
  mem_G u := by
    rw [Φ.mem_G, GGPData.unitsOf_symm_apply]
  mem_H g := by
    have hsymm : GGPData.isoG Φ.alg.symm (fun u => by rw [Φ.mem_G, GGPData.unitsOf_symm_apply]) g =
        Φ.e.symm g := rfl
    rw [hsymm, Φ.mem_H]
    show g ∈ d'.H ↔ Φ.e (Φ.e.symm g) ∈ d'.H
    rw [Φ.e.apply_symm_apply]
  mem_lie X := by
    rw [Φ.mem_lie, AlgEquiv.apply_symm_apply]
  lam_eq h hh := by
    have hg : GGPData.isoG Φ.alg Φ.mem_G (Φ.e.symm h) = h := Φ.e.apply_symm_apply h
    have hmem : Φ.e.symm h ∈ d.H := by
      rw [Φ.mem_H]
      show Φ.e (Φ.e.symm h) ∈ d'.H
      rw [Φ.e.apply_symm_apply]; exact hh
    have := Φ.lam_eq (Φ.e.symm h) hmem
    rw [eq_comm]
    convert this using 2
    · exact Subtype.ext hg.symm
    · rfl

/-- Composition of isomorphisms. -/
def trans (Φ : GGPIso d d') (Ψ : GGPIso d' d'') : GGPIso d d'' where
  alg := Φ.alg.trans Ψ.alg
  mem_G u := by
    rw [Φ.mem_G, Ψ.mem_G]
    rfl
  mem_H g := by
    rw [Φ.mem_H, Ψ.mem_H]
    rfl
  mem_lie X := by
    rw [Φ.mem_lie, Ψ.mem_lie]
    rfl
  lam_eq h hh := by
    have h1 := Φ.lam_eq h hh
    have h2 := Ψ.lam_eq (Φ.e h) ((Φ.mem_H h).1 hh)
    exact h2.trans h1

@[simp] theorem trans_e (Φ : GGPIso d d') (Ψ : GGPIso d' d'') (g : ↥d.G) :
    (Φ.trans Ψ).e g = Ψ.e (Φ.e g) := rfl

@[simp] theorem symm_e (Φ : GGPIso d d') (g : ↥d'.G) : Φ.symm.e g = Φ.e.symm g := rfl

theorem mem_H_iff (Φ : GGPIso d d') (g : ↥d.G) : g ∈ d.H ↔ Φ.e g ∈ d'.H := Φ.mem_H g

/-- `ξ' ∘ e = ξ` on `H(F)`, for every `ψ` (Thesis §5.2: `ξ(h) = ψ(λ(h))`). -/
theorem xi_e (Φ : GGPIso d d') (ψ : AddChar F Circle) (h : ↥d.H) :
    d'.xi ψ ⟨Φ.e h, (Φ.mem_H h).1 h.2⟩ = d.xi ψ h := by
  unfold GGPData.xi
  rw [show d'.lam ⟨Φ.e h, (Φ.mem_H h).1 h.2⟩ = d.lam h from Φ.lam_eq h h.2]

/-! ### Topology: `e` is a homeomorphism -/

/-- An algebra isomorphism of the (finite-dimensional, module-topology) ambient algebras is
continuous. -/
theorem continuous_alg (alg : d.ambient ≃ₐ[F] d'.ambient) : Continuous alg :=
  IsModuleTopology.continuous_of_linearMap alg.toLinearEquiv.toLinearMap

theorem continuous_e (Φ : GGPIso d d') : Continuous Φ.e := by
  have hu : Continuous (GGPData.unitsOf Φ.alg) :=
    Units.continuous_map (f := (Φ.alg.toRingEquiv.toMulEquiv : d.ambient →* d'.ambient))
      (continuous_alg Φ.alg)
  exact (hu.comp continuous_subtype_val).subtype_mk _

theorem continuous_e_symm (Φ : GGPIso d d') : Continuous Φ.e.symm :=
  Φ.symm.continuous_e

/-- `e` as an isomorphism of topological groups. -/
def toCME (Φ : GGPIso d d') : ↥d.G ≃ₜ* ↥d'.G :=
  { Φ.e with
    continuous_toFun := Φ.continuous_e
    continuous_invFun := Φ.continuous_e_symm }

@[simp] theorem toCME_apply (Φ : GGPIso d d') (g : ↥d.G) : Φ.toCME g = Φ.e g := rfl

/-! ### The invariant form and the regular set -/

/-- `bilin' (alg X) (alg Y) = bilin X Y`: the trace form `tr(L_{XY})` is invariant under algebra
isomorphisms. -/
theorem bilin_alg (Φ : GGPIso d d') (X Y : d.ambient) :
    d'.bilin (Φ.alg X) (Φ.alg Y) = d.bilin X Y := by
  rw [GGPData.bilin_apply, GGPData.bilin_apply, ← map_mul]
  have : LinearMap.mulLeft F (Φ.alg (X * Y)) =
      Φ.alg.toLinearEquiv.conj (LinearMap.mulLeft F (X * Y)) := by
    refine LinearMap.ext fun Z => ?_
    simp [LinearEquiv.conj_apply]
  rw [this, LinearMap.trace_conj']

/-- `mulLeft (alg x)` is the conjugate of `mulLeft x` by `alg`. -/
theorem isSS_alg_iff (alg : d.ambient ≃ₐ[F] d'.ambient) (x : d.ambient) :
    IsSS F (alg x) ↔ IsSS F x := by
  unfold IsSS
  refine (LinearEquiv.isSemisimple_iff (LinearMap.mulLeft F x) (LinearMap.mulLeft F (alg x))
    alg.toLinearEquiv ?_).symm
  refine LinearMap.ext fun Z => ?_
  simp

omit [PAdicField F] in
/-- `lieCentralizer 𝔤 x` is abelian iff its elements pairwise commute. -/
theorem isLieAbelian_lieCentralizer_iff {A : Type*} [Ring A] [Algebra F A]
    (𝔤 : LieSubalgebra F A) (x : A) :
    IsLieAbelian ↥(lieCentralizer 𝔤 x) ↔
      ∀ X ∈ lieCentralizer 𝔤 x, ∀ Y ∈ lieCentralizer 𝔤 x, X * Y = Y * X := by
  constructor
  · intro h X hX Y hY
    have := h.trivial ⟨X, hX⟩ ⟨Y, hY⟩
    have := congrArg Subtype.val this
    rw [LieSubalgebra.coe_bracket, Ring.lie_def] at this
    exact sub_eq_zero.mp this
  · intro h
    refine ⟨fun X Y => Subtype.ext ?_⟩
    rw [LieSubalgebra.coe_bracket, Ring.lie_def]
    exact sub_eq_zero.mpr (h X X.2 Y Y.2)

theorem mem_lieCentralizer_alg (Φ : GGPIso d d') (x X : d.ambient) :
    X ∈ lieCentralizer d.lie x ↔ Φ.alg X ∈ lieCentralizer d'.lie (Φ.alg x) := by
  rw [mem_lieCentralizer, mem_lieCentralizer, Φ.mem_lie, ← map_mul, ← map_mul,
    Φ.alg.injective.eq_iff]

theorem isRegularSS_alg_iff (Φ : GGPIso d d') (x : d.ambient) :
    IsRegularSS d'.lie (Φ.alg x) ↔ IsRegularSS d.lie x := by
  unfold IsRegularSS
  rw [isSS_alg_iff, isLieAbelian_lieCentralizer_iff, isLieAbelian_lieCentralizer_iff]
  refine and_congr Iff.rfl ⟨fun h X hX Y hY => ?_, fun h X hX Y hY => ?_⟩
  · have := h _ ((Φ.mem_lieCentralizer_alg x X).1 hX) _ ((Φ.mem_lieCentralizer_alg x Y).1 hY)
    rw [← map_mul, ← map_mul] at this
    exact Φ.alg.injective this
  · have hX' : Φ.alg.symm X ∈ lieCentralizer d.lie x := by
      rw [Φ.mem_lieCentralizer_alg, AlgEquiv.apply_symm_apply]; exact hX
    have hY' : Φ.alg.symm Y ∈ lieCentralizer d.lie x := by
      rw [Φ.mem_lieCentralizer_alg, AlgEquiv.apply_symm_apply]; exact hY
    have := congrArg Φ.alg (h _ hX' _ hY')
    simpa only [map_mul, AlgEquiv.apply_symm_apply] using this

/-- `e` carries the regular semisimple set `G_reg(F)` onto `G'_reg(F)` (Thesis §2.1). -/
theorem mem_regularSet_iff (Φ : GGPIso d d') (g : ↥d.G) :
    Φ.e g ∈ regularSet d'.G d'.lie ↔ g ∈ regularSet d.G d.lie := by
  show IsRegularSS d'.lie (((Φ.e g : ↥d'.G) : d'.ambientˣ) : d'.ambient) ↔ _
  rw [coe_e, isRegularSS_alg_iff]
  rfl

/-- `e` carries the centre onto the centre and `H` onto `H'`, hence `A_{G,H} = Z_G ∩ H` onto
`A_{G',H'}` (`center_inf_H_eq_AGH`). -/
theorem mem_center_iff (Φ : GGPIso d d') (g : ↥d.G) :
    g ∈ Subgroup.center ↥d.G ↔ Φ.e g ∈ Subgroup.center ↥d'.G := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h z
    obtain ⟨y, rfl⟩ := Φ.e.surjective z
    rw [← MulEquiv.map_mul, ← MulEquiv.map_mul, h]
  · intro h z
    apply Φ.e.injective
    rw [MulEquiv.map_mul, MulEquiv.map_mul]
    exact h _

theorem mem_AGH_iff (Φ : GGPIso d d') (g : ↥d.G) : g ∈ d.AGH ↔ Φ.e g ∈ d'.AGH := by
  have h1 : g ∈ d.AGH ↔ g ∈ Subgroup.center ↥d.G ⊓ d.H := by rw [d.center_inf_H_eq_AGH]
  have h2 : Φ.e g ∈ d'.AGH ↔ Φ.e g ∈ Subgroup.center ↥d'.G ⊓ d'.H := by
    rw [d'.center_inf_H_eq_AGH]
  rw [h1, h2, Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr (Φ.mem_center_iff g) (Φ.mem_H_iff g)

end GGPIso

/-! ## 2. Pulling back a representation along a continuous isomorphism -/

section Comap

universe u

variable {G G' : Type u} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']

/-- The pullback `π ∘ e` of a unitary representation of `G'` along a continuous homomorphism
`e : G → G'` (same Hilbert space).  (Generic; a candidate for `Foundations/Representations.lean`.) -/
abbrev UnitaryRep.comap (e : G →* G') (he : Continuous e) (π : UnitaryRep G') : UnitaryRep G where
  H := π.H
  ρ := π.ρ.comp e
  unitary_ρ g := π.unitary_ρ (e g)
  strongCont v := (π.strongCont v).comp he

/-- The pullback along an isomorphism of topological groups. -/
abbrev UnitaryRep.comapCME (e : G ≃ₜ* G') (π : UnitaryRep G') : UnitaryRep G :=
  π.comap (e : G ≃* G').toMonoidHom e.continuous

@[simp] theorem UnitaryRep.comapCME_ρ (e : G ≃ₜ* G') (π : UnitaryRep G') (g : G) :
    (π.comapCME e).ρ g = π.ρ (e g) := rfl

/-- Irreducibility is preserved by pulling back along an isomorphism. -/
theorem UnitaryRep.isIrreducible_comapCME (e : G ≃ₜ* G') (π : UnitaryRep G') :
    (π.comapCME e).IsIrreducible ↔ π.IsIrreducible := by
  unfold UnitaryRep.IsIrreducible
  constructor <;> rintro ⟨hn, h⟩ <;> refine ⟨hn, fun W hW hinv => h W hW ?_⟩
  · intro g v hv
    exact hinv (e g) v hv
  · intro g' v hv
    have := hinv (e.symm g') v hv
    rw [UnitaryRep.comapCME_ρ, ContinuousMulEquiv.apply_symm_apply] at this
    exact this

/-- Smooth vectors are the same for `π ∘ e` and `π` (open subgroups correspond under the
homeomorphism `e`). -/
theorem smoothVectors_comapCME (e : G ≃ₜ* G') (π : UnitaryRep G') :
    smoothVectors (π.comapCME e) = smoothVectors π := by
  ext v
  constructor
  · rintro ⟨U, hU, hfix⟩
    refine ⟨U.map (e : G ≃* G').toMonoidHom, ?_, ?_⟩
    · have : ((U.map (e : G ≃* G').toMonoidHom : Subgroup G') : Set G') = e '' (U : Set G) := rfl
      rw [this]
      exact e.toHomeomorph.isOpenMap _ hU
    · rintro _ ⟨u, hu, rfl⟩
      exact hfix u hu
  · rintro ⟨U, hU, hfix⟩
    refine ⟨U.comap (e : G ≃* G').toMonoidHom, hU.preimage e.continuous, fun u hu => ?_⟩
    exact hfix _ hu

variable [IsTopologicalGroup G] [IsTopologicalGroup G']

/-- Equivariant forms correspond under pullback along `e`, when `e` carries `(S, ξ)` to
`(S', ξ')`. -/
theorem multiplicity_comapCME (e : G ≃ₜ* G') (π : UnitaryRep G') (S : Subgroup G)
    (S' : Subgroup G') (hS : ∀ g, g ∈ S ↔ e g ∈ S') (ξ : ↥S → ℂ) (ξ' : ↥S' → ℂ)
    (hξ : ∀ s : ↥S, ξ' ⟨e s, (hS s).1 s.2⟩ = ξ s) :
    multiplicity (π.comapCME e) S ξ = multiplicity π S' ξ' := by
  have hsm := smoothVectors_comapCME e π
  let E : ↥(smoothVectors (π.comapCME e)) ≃ₗ[ℂ] ↥(smoothVectors π) := LinearEquiv.ofEq _ _ hsm
  have hact : ∀ (s : ↥S) (v : ↥(smoothVectors (π.comapCME e))),
      E (smoothAction (π.comapCME e) s v) =
        smoothAction π (⟨e s, (hS s).1 s.2⟩ : ↥S') (E v) := fun s v => Subtype.ext rfl
  have hmem : ∀ ℓ : Module.Dual ℂ ↥(smoothVectors π),
      ℓ ∈ equivariantForms π S' ξ' ↔ E.dualMap ℓ ∈ equivariantForms (π.comapCME e) S ξ := by
    intro ℓ
    constructor
    · intro hℓ s v
      simp only [LinearEquiv.dualMap_apply]
      rw [hact, hℓ, hξ]
    · intro hℓ s' w
      have hs : e.symm s' ∈ S := by rw [hS]; simp
      have key : smoothAction π s' w =
          E (smoothAction (π.comapCME e) (⟨e.symm s', hs⟩ : ↥S) (E.symm w)) := by
        apply Subtype.ext
        show π.ρ s' w = π.ρ (e (e.symm s')) w
        rw [ContinuousMulEquiv.apply_symm_apply]
      have kξ : ξ' s' = ξ ⟨e.symm s', hs⟩ := by
        rw [← hξ]; congr 1; exact Subtype.ext (by simp)
      have h1 := hℓ ⟨e.symm s', hs⟩ (E.symm w)
      rw [LinearEquiv.dualMap_apply, LinearEquiv.dualMap_apply, LinearEquiv.apply_symm_apply] at h1
      rw [key, kξ, h1]
  unfold multiplicity
  rw [(equivOfForallMemIff E.dualMap hmem).rank_eq]

end Comap

/-! ## 3. Haar measure, traces and characters under a topological group isomorphism -/

section HaarTransport

open scoped NNReal ENNReal InnerProductSpace

set_option linter.unusedSectionVars false

universe u

variable {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [LocallyCompactSpace G'] [T2Space G']
  [MeasurableSpace G'] [BorelSpace G'] [SecondCountableTopology G']

/-- The constant `c > 0` with `e_*(dg) = c · dg'` (uniqueness of Haar measure). -/
def haarFactor (e : G ≃ₜ* G') : ℝ≥0 :=
  Measure.haarScalarFactor (Measure.map e (Measure.haar : Measure G)) (Measure.haar : Measure G')

theorem haarFactor_pos (e : G ≃ₜ* G') : 0 < haarFactor e := by
  have : (Measure.map e (Measure.haar : Measure G)).IsHaarMeasure := e.isHaarMeasure_map _
  exact Measure.haarScalarFactor_pos_of_isHaarMeasure _ _

/-- `e_*(dg) = c · dg'` with `c = haarFactor e > 0`. -/
theorem map_haar_eq (e : G ≃ₜ* G') :
    Measure.map e (Measure.haar : Measure G) = ((haarFactor e : ℝ≥0∞)) • (Measure.haar : Measure G') := by
  have : (Measure.map e (Measure.haar : Measure G)).IsHaarMeasure := e.isHaarMeasure_map _
  exact Measure.isMulLeftInvariant_eq_smul _ _

theorem haarFactor_ne_zero (e : G ≃ₜ* G') : (haarFactor e : ℝ≥0∞) ≠ 0 := by
  simpa using (haarFactor_pos e).ne'

theorem haarFactor_ne_top (e : G ≃ₜ* G') : (haarFactor e : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top

/-- Change of variables: `∫_G f(e x) dx = c ∫_{G'} f(y) dy`. -/
theorem integral_comp_cme {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (e : G ≃ₜ* G')
    (f : G' → E) :
    ∫ x, f (e x) ∂(Measure.haar : Measure G) =
      ((haarFactor e : ℝ)) • ∫ y, f y ∂(Measure.haar : Measure G') := by
  have h := integral_map_equiv (μ := (Measure.haar : Measure G)) e.toHomeomorph.toMeasurableEquiv f
  rw [Homeomorph.toMeasurableEquiv_coe] at h
  change ∫ y, f y ∂Measure.map e Measure.haar = ∫ x, f (e x) ∂Measure.haar at h
  rw [← h, map_haar_eq, integral_smul_measure]
  rfl

theorem integrable_comp_cme_iff {E : Type*} [NormedAddCommGroup E] (e : G ≃ₜ* G') (f : G' → E) :
    Integrable (f ∘ e) (Measure.haar : Measure G) ↔ Integrable f (Measure.haar : Measure G') := by
  have h := integrable_map_equiv (μ := (Measure.haar : Measure G)) e.toHomeomorph.toMeasurableEquiv f
  rw [Homeomorph.toMeasurableEquiv_coe] at h
  change Integrable f (Measure.map e Measure.haar) ↔ Integrable (f ∘ e) Measure.haar at h
  rw [← h, map_haar_eq, integrable_smul_measure (haarFactor_ne_zero e) (haarFactor_ne_top e)]

theorem locallyIntegrable_smul_measure_iff {X E : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {f : X → E} {c : ℝ≥0∞} (h0 : c ≠ 0) (htop : c ≠ ∞) :
    LocallyIntegrable f (c • μ) ↔ LocallyIntegrable f μ := by
  simp only [LocallyIntegrable, IntegrableAtFilter, IntegrableOn, Measure.restrict_smul,
    integrable_smul_measure h0 htop]

theorem locallyIntegrable_comp_cme_iff {E : Type*} [NormedAddCommGroup E] (e : G ≃ₜ* G')
    (f : G' → E) :
    LocallyIntegrable (f ∘ e) (Measure.haar : Measure G) ↔
      LocallyIntegrable f (Measure.haar : Measure G') := by
  have h := locallyIntegrable_map_homeomorph (μ := (Measure.haar : Measure G)) e.toHomeomorph
    (f := f)
  change LocallyIntegrable f (Measure.map e Measure.haar) ↔ LocallyIntegrable (f ∘ e) Measure.haar
    at h
  rw [← h, map_haar_eq, locallyIntegrable_smul_measure_iff (haarFactor_ne_zero e)
    (haarFactor_ne_top e)]

namespace UnitaryRep

variable (e : G ≃ₜ* G') (π : UnitaryRep G')

theorem opIntegrable_comapCME_iff (f : G → ℂ) :
    OpIntegrable (π.comapCME e) f ↔ OpIntegrable π (f ∘ e.symm) := by
  refine forall_congr' fun v => ?_
  have : (fun g => f g • (π.comapCME e).ρ g v) = (fun y => (f ∘ e.symm) y • π.ρ y v) ∘ e := by
    funext g; simp only [Function.comp_apply, ContinuousMulEquiv.symm_apply_apply]; rfl
  rw [this]
  exact integrable_comp_cme_iff e (fun y => (f ∘ e.symm) y • π.ρ y v)

/-- `π∘e(f) = c · π(f ∘ e⁻¹)`. -/
theorem opOf_comapCME (f : G → ℂ) :
    opOf (π.comapCME e) f = ((haarFactor e : ℝ) : ℂ) • opOf π (f ∘ e.symm) := by
  ext v
  by_cases hf : OpIntegrable (π.comapCME e) f
  · have hf' := (opIntegrable_comapCME_iff e π f).1 hf
    rw [FunLike.coe_smul, Pi.smul_apply, opOf_apply _ hf, opOf_apply _ hf']
    have := integral_comp_cme e (fun y => (f ∘ e.symm) y • π.ρ y v)
    simp only [Function.comp_apply, ContinuousMulEquiv.symm_apply_apply] at this
    rw [show (fun g => f g • (π.comapCME e).ρ g v) = fun g => f g • π.ρ (e g) v from rfl, this,
      ← Complex.coe_smul]
    rfl
  · have hf' : ¬ OpIntegrable π (f ∘ e.symm) := fun h => hf ((opIntegrable_comapCME_iff e π f).2 h)
    rw [opOf_of_not_opIntegrable _ hf, opOf_of_not_opIntegrable _ hf', smul_zero]

theorem fixedSpace_comapCME (K : Subgroup G) :
    fixedSpace (π.comapCME e) K = fixedSpace π (K.map (e : G ≃* G').toMonoidHom) := by
  ext v
  constructor
  · rintro hv _ ⟨k, hk, rfl⟩
    exact hv k hk
  · intro hv k hk
    exact hv (e k) ⟨k, hk, rfl⟩

theorem map_comap_cme (K' : Subgroup G') :
    (K'.comap (e : G ≃* G').toMonoidHom).map (e : G ≃* G').toMonoidHom = K' :=
  Subgroup.map_comap_eq_self_of_surjective (e : G ≃* G').surjective K'

/-- Trace of a restriction, invariant under equal subspaces and scaling. -/
theorem trace_restrict_smul {M : Type*} [AddCommGroup M] [Module ℂ M] {p q : Submodule ℂ M}
    [FiniteDimensional ℂ ↥q] (hpq : p = q) (T T' : M →ₗ[ℂ] M) (c : ℂ) (hT : T = c • T')
    (hp : ∀ x ∈ p, T x ∈ p) (hq : ∀ x ∈ q, T' x ∈ q) :
    LinearMap.trace ℂ ↥p (T.restrict hp) = c * LinearMap.trace ℂ ↥q (T'.restrict hq) := by
  subst hpq; subst hT
  have : (c • T').restrict hp = c • T'.restrict hq := by
    ext x; simp
  rw [this, map_smul, smul_eq_mul]

theorem TraceDatum.comapCME {f : G → ℂ} {K : Subgroup G} (h : TraceDatum (π.comapCME e) f K) :
    TraceDatum π (f ∘ e.symm) (K.map (e : G ≃* G').toMonoidHom) := by
  obtain ⟨hKo, hKc, hbi, hfin, hpres⟩ := h
  have hfix := fixedSpace_comapCME e π K
  have hc : ((haarFactor e : ℝ) : ℂ) ≠ 0 := by
    have := haarFactor_pos e
    exact_mod_cast this.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact e.toHomeomorph.isOpenMap _ hKo
  · exact hKc.image e.continuous
  · rintro _ ⟨k, hk, rfl⟩ g'
    refine ⟨?_, ?_⟩
    · show f (e.symm (e k * g')) = f (e.symm g')
      rw [map_mul, ContinuousMulEquiv.symm_apply_apply]
      exact (hbi k hk (e.symm g')).1
    · show f (e.symm (g' * e k)) = f (e.symm g')
      rw [map_mul, ContinuousMulEquiv.symm_apply_apply]
      exact (hbi k hk (e.symm g')).2
  · rw [← hfix]; exact hfin
  · intro v hv
    rw [← hfix] at hv ⊢
    have := (fixedSpace (π.comapCME e) K).smul_mem (((haarFactor e : ℝ) : ℂ))⁻¹ (hpres v hv)
    rw [opOf_comapCME, FunLike.coe_smul, Pi.smul_apply, smul_smul,
      inv_mul_cancel₀ hc, one_smul] at this
    exact this

theorem TraceDatum.of_comapCME {f' : G' → ℂ} {K' : Subgroup G'} (h : TraceDatum π f' K') :
    TraceDatum (π.comapCME e) (f' ∘ e) (K'.comap (e : G ≃* G').toMonoidHom) := by
  obtain ⟨hKo, hKc, hbi, hfin, hpres⟩ := h
  have hfix : fixedSpace (π.comapCME e) (K'.comap (e : G ≃* G').toMonoidHom) = fixedSpace π K' := by
    rw [fixedSpace_comapCME, map_comap_cme]
  have hop : opOf (π.comapCME e) (f' ∘ e) = ((haarFactor e : ℝ) : ℂ) • opOf π f' := by
    rw [opOf_comapCME]
    congr 2
    funext y; simp
  refine ⟨hKo.preimage e.continuous, ?_, ?_, ?_, ?_⟩
  · have : ((K'.comap (e : G ≃* G').toMonoidHom : Subgroup G) : Set G) = e.symm '' K' := by
      ext x
      simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, Set.mem_image]
      constructor
      · intro hx; exact ⟨e x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        show e (e.symm y) ∈ K'
        rw [ContinuousMulEquiv.apply_symm_apply]; exact hy
    rw [this]
    exact hKc.image e.symm.continuous
  · intro k hk g
    simp only [Function.comp_apply, map_mul]
    exact hbi (e k) hk (e g)
  · rw [hfix]; exact hfin
  · intro v hv
    rw [hfix] at hv ⊢
    rw [hop, FunLike.coe_smul, Pi.smul_apply]
    exact (fixedSpace π K').smul_mem _ (hpres v hv)

/-- `tr (π∘e)(f) = c · tr π(f ∘ e⁻¹)`. -/
theorem traceOf_comapCME (f : G → ℂ) :
    traceOf (π.comapCME e) f = ((haarFactor e : ℝ) : ℂ) * traceOf π (f ∘ e.symm) := by
  by_cases hex : ∃ K : Subgroup G, TraceDatum (π.comapCME e) f K
  · obtain ⟨K, hK⟩ := hex
    have hK' := TraceDatum.comapCME e π hK
    rw [traceOf_eq _ f K hK, traceOf_eq _ _ _ hK']
    have : FiniteDimensional ℂ ↥(fixedSpace π (K.map (e : G ≃* G').toMonoidHom)) := hK'.2.2.2.1
    exact trace_restrict_smul (fixedSpace_comapCME e π K) _ _ _
      (by rw [opOf_comapCME]; rfl) _ _
  · have hex' : ¬ ∃ K' : Subgroup G', TraceDatum π (f ∘ e.symm) K' := by
      rintro ⟨K', hK'⟩
      have := TraceDatum.of_comapCME e π hK'
      have hf : (f ∘ e.symm) ∘ e = f := by funext x; simp
      rw [hf] at this
      exact hex ⟨_, this⟩
    simp only [traceOf, hex, hex', dite_false, mul_zero]

/-- A character `θ'` of `π` pulls back to a character `θ' ∘ e` of `π ∘ e`: the Haar constant `c`
cancels between the trace and the integral. -/
theorem IsCharacterOf.comapCME {θ' : G' → ℂ} (h : IsCharacterOf π θ') :
    IsCharacterOf (π.comapCME e) (θ' ∘ e) := by
  refine ⟨(locallyIntegrable_comp_cme_iff e θ').2 h.1, fun f hf => ?_⟩
  have hf' : f ∘ e.symm ∈ testFunctions G' :=
    ⟨hf.1.comp_continuous e.symm.continuous, hf.2.comp_homeomorph e.symm.toHomeomorph⟩
  have := integral_comp_cme e (fun y => θ' y * (f ∘ e.symm) y)
  simp only [Function.comp_apply, ContinuousMulEquiv.symm_apply_apply] at this
  have h2 := h.2 _ hf'
  simp only [Function.comp_apply] at h2 ⊢
  rw [this, h2, traceOf_comapCME, ← Complex.coe_smul, smul_eq_mul]

end UnitaryRep

/-- Matrix coefficients of the left regular representations correspond under `e`: for every
`w' ∈ L²(G')` there is `w ∈ L²(G)` (namely `c^{-1/2} · w' ∘ e`) with
`⟨λ(g) w, w⟩ = ⟨λ'(e g) w', w'⟩` for all `g`. -/
theorem exists_coeff_leftRegular (e : G ≃ₜ* G') (w' : (leftRegular G').H) :
    ∃ w : (leftRegular G).H, ∀ g : G,
      ⟪(leftRegular G).ρ g w, w⟫_ℂ = ⟪(leftRegular G').ρ (e g) w', w'⟫_ℂ := by
  let W' : Lp ℂ 2 (Measure.haar : Measure G') := w'
  suffices ∃ W : Lp ℂ 2 (Measure.haar : Measure G), ∀ g : G,
      ⟪leftTranslate g W, W⟫_ℂ = ⟪leftTranslate (e g) W', W'⟫_ℂ from this
  set c : ℝ := (haarFactor e : ℝ) with hc_def
  have hc : 0 < c := by simpa [hc_def] using haarFactor_pos e
  set s : ℂ := (((Real.sqrt c)⁻¹ : ℝ) : ℂ) with hs_def
  have hss : (starRingEnd ℂ) s * s * (c : ℂ) = 1 := by
    rw [hs_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt hc.le, inv_mul_cancel₀ hc.ne', Complex.ofReal_one]
  -- the function `s · w' ∘ e` is in `L²(G)`
  have hmem : MemLp (fun x => s • (W' : G' → ℂ) (e x)) 2 (Measure.haar : Measure G) := by
    have h1 : MemLp (W' : G' → ℂ) 2 (Measure.map e (Measure.haar : Measure G)) := by
      rw [map_haar_eq]
      exact (Lp.memLp W').smul_measure (haarFactor_ne_top e)
    have h2 := (e.toHomeomorph.toMeasurableEquiv.memLp_map_measure_iff (μ := Measure.haar)
      (g := (W' : G' → ℂ)) (p := 2)).1 (by rw [Homeomorph.toMeasurableEquiv_coe]; exact h1)
    rw [Homeomorph.toMeasurableEquiv_coe] at h2
    exact h2.const_smul s
  refine ⟨hmem.toLp _, fun g => ?_⟩
  set w := hmem.toLp _
  have hw : (w : G → ℂ) =ᵐ[Measure.haar] fun x => s • (W' : G' → ℂ) (e x) := hmem.coeFn_toLp
  -- left translates
  have hmp : MeasurePreserving (fun x : G => g⁻¹ * x) Measure.haar Measure.haar :=
    measurePreserving_mul_left _ g⁻¹
  have hmp' : MeasurePreserving (fun y : G' => (e g)⁻¹ * y) Measure.haar Measure.haar :=
    measurePreserving_mul_left _ (e g)⁻¹
  have hL : (leftTranslate g w : G → ℂ) =ᵐ[Measure.haar]
      fun x => s • (W' : G' → ℂ) ((e g)⁻¹ * e x) := by
    have a1 : (leftTranslate g w : G → ℂ) =ᵐ[Measure.haar] (w : G → ℂ) ∘ fun x => g⁻¹ * x :=
      Lp.coeFn_compMeasurePreserving w hmp
    have a2 := hmp.quasiMeasurePreserving.ae_eq_comp hw
    filter_upwards [a1, a2] with x h1 h2
    rw [h1, h2]
    simp [map_mul, map_inv]
  have hL' : (leftTranslate (e g) W' : G' → ℂ) =ᵐ[Measure.haar]
      fun y => (W' : G' → ℂ) ((e g)⁻¹ * y) := Lp.coeFn_compMeasurePreserving W' hmp'
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have lhs : ∫ x, ⟪(leftTranslate g w : G → ℂ) x, (w : G → ℂ) x⟫_ℂ ∂Measure.haar =
      ∫ x, (starRingEnd ℂ) s * s *
        ⟪(W' : G' → ℂ) ((e g)⁻¹ * e x), (W' : G' → ℂ) (e x)⟫_ℂ ∂Measure.haar := by
    refine integral_congr_ae ?_
    filter_upwards [hL, hw] with x h1 h2
    rw [h1, h2, inner_smul_left, inner_smul_right, ← mul_assoc]
  have rhs : ∫ y, ⟪(leftTranslate (e g) W' : G' → ℂ) y, (W' : G' → ℂ) y⟫_ℂ ∂Measure.haar =
      ∫ y, ⟪(W' : G' → ℂ) ((e g)⁻¹ * y), (W' : G' → ℂ) y⟫_ℂ ∂Measure.haar := by
    refine integral_congr_ae ?_
    filter_upwards [hL'] with y h1
    rw [h1]
  rw [lhs, rhs, integral_const_mul,
    integral_comp_cme e (fun y => ⟪(W' : G' → ℂ) ((e g)⁻¹ * y), (W' : G' → ℂ) y⟫_ℂ),
    ← Complex.coe_smul, smul_eq_mul, ← mul_assoc, ← hc_def, hss, one_mul]

/-- Weak containment in the regular representation is preserved by pulling back along `e`
(Thesis §3.1.2: temperedness). -/
theorem weaklyContainedIn_comapCME_iff [SecondCountableTopology G] (e : G ≃ₜ* G')
    (π : UnitaryRep G') :
    WeaklyContainedIn (π.comapCME e) (leftRegular G) ↔ WeaklyContainedIn π (leftRegular G') := by
  constructor
  · intro h v K hK ε hε
    obtain ⟨n, w, hw⟩ := h v (e.symm '' K) (hK.image e.symm.continuous) ε hε
    choose w' hw' using fun i => exists_coeff_leftRegular e.symm (w i)
    refine ⟨n, w', fun g' hg' => ?_⟩
    have := hw (e.symm g') ⟨g', hg', rfl⟩
    rw [UnitaryRep.comapCME_ρ, ContinuousMulEquiv.apply_symm_apply] at this
    simp only [hw']
    exact this
  · intro h v K hK ε hε
    obtain ⟨n, w', hw⟩ := h v (e '' K) (hK.image e.continuous) ε hε
    choose w hw' using fun i => exists_coeff_leftRegular e (w' i)
    refine ⟨n, w, fun g hg => ?_⟩
    have := hw (e g) ⟨g, hg, rfl⟩
    simp only [hw']
    exact this

/-- Temperedness is preserved by pulling back along an isomorphism of topological groups. -/
theorem isTempered_comapCME_iff [SecondCountableTopology G] (e : G ≃ₜ* G') (π : UnitaryRep G') :
    IsTempered (π.comapCME e) ↔ IsTempered π :=
  and_congr (UnitaryRep.isIrreducible_comapCME e π) (weaklyContainedIn_comapCME_iff e π)

end HaarTransport

/-! ## 4. Transport of `m`, temperedness, `θ_π` and `m_geom` along a GGP isomorphism -/

namespace GGPIso

variable {d d' : GGPData F}

/-- `π' ↦ π' ∘ e`: tempered representations of `G'(F)` pulled back to `G(F)`. -/
abbrev pullback (Φ : GGPIso d d') (π' : UnitaryRep ↥d'.G) : UnitaryRep ↥d.G :=
  π'.comapCME Φ.toCME

/-- **Transport of the multiplicity**: `m(π' ∘ e) = m(π')` for a GGP
isomorphism `e`, since `e(H) = H'` and `ξ' ∘ e = ξ` (Thesis §5.5: `m(π) = dim Hom_H(π^∞, ξ)`). -/
theorem mult_congr_iso (Φ : GGPIso d d') (ψ : NontrivialAddChar F) (π' : UnitaryRep ↥d'.G) :
    mult ψ d (Φ.pullback π') = mult ψ d' π' :=
  multiplicity_comapCME Φ.toCME π' d.H d'.H Φ.mem_H_iff _ _ fun s => Φ.xi_e ψ.toAddChar s

/-- **Transport of temperedness** (Thesis §3.1.2: irreducible and weakly
contained in the regular representation): `π' ∘ e` is tempered iff `π'` is.  The Haar measures
of `G(F)` and `G'(F)` differ by the constant `haarFactor`, which is absorbed by rescaling
`L²`-vectors (`exists_coeff_leftRegular`). -/
theorem isTempered_congr_iso (Φ : GGPIso d d') (π' : UnitaryRep ↥d'.G) :
    IsTempered (Φ.pullback π') ↔ IsTempered π' :=
  isTempered_comapCME_iff Φ.toCME π'

/-- **Transport of the character** (Thesis Ch. 1): for tempered
`π'`, `θ_{π'∘e} = θ_{π'} ∘ e` on the regular set `G_reg(F)`.  Proof: `θ_{π'} ∘ e` is a character of
`π' ∘ e` (the Haar constant cancels, `UnitaryRep.IsCharacterOf.comapCME`) and is continuous on
`G_reg(F) = e⁻¹(G'_reg(F))`; two such characters agree almost everywhere, hence on the open set
`G_reg(F)` (`hc_regularSet_open_conull`).  Off `G_reg(F)` both sides are unnormalized
representatives, so no statement is made there. -/
theorem charG_congr_iso (Φ : GGPIso d d') (π' : UnitaryRep ↥d'.G) (hπ' : IsTempered π') :
    ∀ g ∈ regularSet d.G d.lie, charG d (Φ.pullback π') g = charG d' π' (Φ.e g) := by
  obtain ⟨hchar', hcont'⟩ := hc_character d' π' hπ'
  set θ' := charG d' π'
  have hchar : IsCharacterOf (Φ.pullback π') (θ' ∘ Φ.toCME) :=
    UnitaryRep.IsCharacterOf.comapCME Φ.toCME π' hchar'
  have hcont : ContinuousOn (θ' ∘ Φ.toCME) (regularSet d.G d.lie) :=
    hcont'.comp Φ.continuous_e.continuousOn fun g hg => (Φ.mem_regularSet_iff g).2 hg
  obtain ⟨hcharG, hcontG⟩ := characterOn_spec (Φ.pullback π') (regularSet d.G d.lie)
    ⟨θ' ∘ Φ.toCME, hchar, hcont⟩
  have : TotallyDisconnectedSpace ↥d.G := totallyDisconnectedSpace_subgroup F d.ambient d.G
  have hae := hcharG.ae_eq hchar
  have hopen := (hc_regularSet_open_conull d).1
  exact Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae) hopen hcontG hcont

/-- **Transport of the geometric multiplicity**:
`m_geom(θ' ∘ e) = m_geom(θ')` for a quasi-character `θ'` of `G'(F)` (Thesis §7.2, Prop 12.1.1).
Stated for quasi-characters only: `m_geom` is built from germs, which exist only for
quasi-characters (for other `θ'` the definition returns unnormalized junk, and its transport is not
a meaningful statement).

Why it should hold, and what the proof needs: `e(H) = H'` and `e` carries the unipotent radical
`N` of `H` onto that of `H'`, hence the Levi factor `GSpin(W)` (diagonal) onto an `N'(F)`-conjugate
of `GSpin(W')`; quasi-characters are conjugation invariant; the germs are transported by `alg`, which
carries `𝔤`, `bilin` (`bilin_alg`) and the nilpotent orbits; and `Γ(G,H)`, `weylCard`, `Δ` and the
probability measures on `T(F)/A(F)` are intrinsic.  Each step needs the transport of `orbitChoice`
and of `ĵ`; not yet done. -/
theorem mGeom_congr_iso (Φ : GGPIso d d') (ψ : NontrivialAddChar F) (θ' : ↥d'.G → ℂ)
    (hθ' : IsQuasiCharacter d'.G d'.lie d'.bilin ψ θ') :
    mGeom ψ d (θ' ∘ Φ.e) = mGeom ψ d' θ' := by
  sorry

end GGPIso

/-! ## 4a. Quadratic-space lemmas for the Levi datum (own)

`H^{a+b} ≅ H^a ⊥ H^b` (`hypAddEquiv`), `H^r ⊥ ⟨ν⟩ ≅ Z_{r,ν}` (`splitOddIso`), `⟨ν⟩ ⊥ ⟨-ν⟩ ≅ H`
(`hypLineIso`), and the hyperbolic splitting of a nondegenerate space along a totally isotropic
subspace (`exists_hypSplit`, from the Witt decomposition).  Used by `GGPData.exists_leviSpec`. -/

namespace LeviAux

variable {K : Type*} [Field K]

theorem hypForm_apply (n : ℕ) (v : Fin (2 * n) → K) :
    hypForm K n v = ∑ i, v i * v i.rev := by
  unfold hypForm Matrix.toQuadraticForm'
  simp only [LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply', dotProduct,
    Matrix.mulVec, hypMatrix]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single i.rev]
  · have h : (i : ℕ) + (i.rev : ℕ) + 1 = 2 * n := by simp [Fin.val_rev]; omega
    simp only [h, ↓reduceIte, one_mul]
  · intro j _ hj
    have h : ¬ ((i : ℕ) + (j : ℕ) + 1 = 2 * n) := by
      intro h; apply hj; ext; simp [Fin.val_rev]; omega
    simp only [h, ↓reduceIte, zero_mul, mul_zero]
  · simp

/-- The block permutation `Fin (2a) ⊕ Fin (2b) → Fin (2(a+b))`: the outer block carries `H^a`,
the middle block `H^b`. -/
def hypBlock (a b : ℕ) : Fin (2 * a) ⊕ Fin (2 * b) → Fin (2 * (a + b))
  | Sum.inl i => ⟨if (i : ℕ) < a then i else i + 2 * b, by split_ifs <;> omega⟩
  | Sum.inr j => ⟨a + j, by omega⟩

theorem hypBlock_injective (a b : ℕ) : Function.Injective (hypBlock a b) := by
  rintro (i | i) (j | j) h <;> simp only [hypBlock, Fin.mk.injEq] at h
  · congr 1; ext; split_ifs at h <;> omega
  · split_ifs at h <;> omega
  · split_ifs at h <;> omega
  · congr 1; ext; omega

def hypBlockEquiv (a b : ℕ) : Fin (2 * a) ⊕ Fin (2 * b) ≃ Fin (2 * (a + b)) :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).2
    ⟨hypBlock_injective a b, by simp; ring⟩)

theorem hypBlock_rev (a b : ℕ) (s : Fin (2 * a) ⊕ Fin (2 * b)) :
    (hypBlock a b s).rev = hypBlock a b (Sum.map Fin.rev Fin.rev s) := by
  rcases s with i | j
  · ext; simp only [hypBlock, Fin.val_rev, Sum.map_inl]; split_ifs <;> omega
  · ext; simp only [hypBlock, Fin.val_rev, Sum.map_inr]; omega

/-- `H^{a+b} ≅ H^a ⊥ H^b`. -/
def hypAddEquiv (a b : ℕ) :
    ((hypForm K a).prod (hypForm K b)).IsometryEquiv (hypForm K (a + b)) where
  toLinearEquiv := (LinearEquiv.sumArrowLequivProdArrow _ _ K K).symm.trans
    (LinearEquiv.funCongrLeft K K (hypBlockEquiv a b).symm)
  map_app' v := by
    obtain ⟨v₁, v₂⟩ := v
    rw [hypForm_apply]
    simp only [QuadraticMap.prod_apply, hypForm_apply]
    rw [← (hypBlockEquiv a b).sum_comp, Fintype.sum_sum_type]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;>
      simp [LinearMap.funLeft, hypBlockEquiv, hypBlock_rev, LinearEquiv.sumArrowLequivProdArrow,
        Equiv.sumArrowEquivProdArrow_symm_apply_inl, Equiv.sumArrowEquivProdArrow_symm_apply_inr]


section Nondeg

variable [Invertible (2 : K)]
variable {X Y : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem bform_isometryEquiv {Q : QuadraticForm K X} {Q' : QuadraticForm K Y}
    (e : Q.IsometryEquiv Q') (x y : X) : bform Q' (e x) (e y) = bform Q x y := by
  simp only [bform, QuadraticMap.associated_apply]
  rw [← map_add, e.map_app, e.map_app, e.map_app]

theorem isNondeg_of_isometryEquiv {Q : QuadraticForm K X} {Q' : QuadraticForm K Y}
    (e : Q.IsometryEquiv Q') (hQ : IsNondeg Q) : IsNondeg Q' := by
  rw [isNondeg_iff] at hQ ⊢
  intro y hy
  have : e.symm y = 0 := hQ _ fun x => by
    rw [← bform_isometryEquiv e, e.apply_symm_apply]; exact hy _
  simpa using congrArg e this

theorem isNondeg_prod_right {Q₁ : QuadraticForm K X} {Q₂ : QuadraticForm K Y}
    (h : IsNondeg (Q₁.prod Q₂)) : IsNondeg Q₂ := by
  rw [isNondeg_iff] at h ⊢
  intro y hy
  have := h (0, y) fun z => by
    rw [bform_prod]
    simp [hy z.2]
  exact congrArg Prod.snd this

end Nondeg

/-- `(Q₁ ⊥ Q₂) ⊥ Q₃ ≅ Q₁ ⊥ (Q₂ ⊥ Q₃)`. -/
def prodAssocIso {X Y Z : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    [AddCommGroup Z] [Module K Z] (Q₁ : QuadraticForm K X) (Q₂ : QuadraticForm K Y)
    (Q₃ : QuadraticForm K Z) : ((Q₁.prod Q₂).prod Q₃).IsometryEquiv (Q₁.prod (Q₂.prod Q₃)) where
  toLinearEquiv := LinearEquiv.prodAssoc K X Y Z
  map_app' x := by simp [add_assoc]

/-- Coordinates `F^m × F^n ≅ F^{m+n}`. -/
def appendEquiv (m n : ℕ) : ((Fin m → K) × (Fin n → K)) ≃ₗ[K] (Fin (m + n) → K) :=
  (LinearEquiv.sumArrowLequivProdArrow _ _ K K).symm.trans
    (LinearEquiv.funCongrLeft K K finSumFinEquiv.symm)

/-- A form on `X` transported to coordinates along a linear equivalence. -/
def transportIso {X : Type*} [AddCommGroup X] [Module K X] {k : ℕ} (Q : QuadraticForm K X)
    (e : X ≃ₗ[K] (Fin k → K)) : Q.IsometryEquiv (Q.comp (e.symm : (Fin k → K) →ₗ[K] X)) where
  toLinearEquiv := e
  map_app' x := by simp


theorem splitOddForm_apply (r : ℕ) (ν : K) (w : Fin (2 * r + 1) → K) :
    splitOddForm r ν w = ν * ∑ i, w i * w i.rev := by
  unfold splitOddForm Matrix.toQuadraticForm'
  simp only [LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply', dotProduct,
    Matrix.mulVec, splitOddMatrix, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i.rev]
  · have h : (i : ℕ) + (i.rev : ℕ) = 2 * r := by simp [Fin.val_rev]; omega
    simp only [h, ↓reduceIte]; ring
  · intro j _ hj
    have h : ¬ ((i : ℕ) + (j : ℕ) = 2 * r) := by
      intro h; apply hj; ext; simp [Fin.val_rev]; omega
    simp only [h, ↓reduceIte, zero_mul, mul_zero]
  · simp

/-- The block map `Fin (2r) ⊕ Fin 1 → Fin (2r+1)`: `H^r` on the outer indices, the anisotropic
line `⟨z_0⟩` in the middle. -/
def oddBlock (r : ℕ) : Fin (2 * r) ⊕ Fin (2 * 0 + 1) → Fin (2 * r + 1)
  | Sum.inl i => ⟨if (i : ℕ) < r then i else i + 1, by split_ifs <;> omega⟩
  | Sum.inr _ => ⟨r, by omega⟩

theorem oddBlock_injective (r : ℕ) : Function.Injective (oddBlock r) := by
  rintro (i | i) (j | j) h <;> simp only [oddBlock, Fin.mk.injEq] at h
  · congr 1; ext; split_ifs at h <;> omega
  · split_ifs at h <;> omega
  · split_ifs at h <;> omega
  · congr 1; ext; omega

def oddBlockEquiv (r : ℕ) : Fin (2 * r) ⊕ Fin (2 * 0 + 1) ≃ Fin (2 * r + 1) :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).2
    ⟨oddBlock_injective r, by simp⟩)

theorem oddBlock_rev (r : ℕ) (s : Fin (2 * r) ⊕ Fin (2 * 0 + 1)) :
    (oddBlock r s).rev = oddBlock r (Sum.map Fin.rev id s) := by
  rcases s with i | j
  · ext; simp only [oddBlock, Fin.val_rev, Sum.map_inl]; split_ifs <;> omega
  · ext; simp only [oddBlock, Fin.val_rev, Sum.map_inr]; omega

/-- The scaling used to identify `ν·H` with `H`: `ν⁻¹` on the upper half of the hyperbolic block. -/
def oddScale (r : ℕ) (ν : K) : Fin (2 * r) ⊕ Fin (2 * 0 + 1) → K
  | Sum.inl i => if (i : ℕ) < r then 1 else ν⁻¹
  | Sum.inr _ => 1

theorem oddScale_ne_zero (r : ℕ) {ν : K} (hν : ν ≠ 0) (s : Fin (2 * r) ⊕ Fin (2 * 0 + 1)) :
    oddScale r ν s ≠ 0 := by
  rcases s with i | j <;> simp only [oddScale] <;> (try split_ifs) <;> simp [hν]

theorem oddScale_mul_rev (r : ℕ) {ν : K} (hν : ν ≠ 0) (i : Fin (2 * r)) :
    ν * (oddScale r ν (Sum.inl i) * oddScale r ν (Sum.inl i.rev)) = 1 := by
  simp only [oddScale, Fin.val_rev]
  split_ifs <;> first | omega | field_simp

/-- The underlying linear equivalence of `splitOddIso`. -/
def oddLin (r : ℕ) {ν : K} (hν : ν ≠ 0) :
    ((Fin (2 * r) → K) × (Fin (2 * 0 + 1) → K)) ≃ₗ[K] (Fin (2 * r + 1) → K) :=
  ((LinearEquiv.sumArrowLequivProdArrow _ _ K K).symm.trans
    (LinearEquiv.piCongrRight fun s => LinearEquiv.smulOfNeZero K K _
      (oddScale_ne_zero r hν s))).trans
    (LinearEquiv.funCongrLeft K K (oddBlockEquiv r).symm)

theorem oddLin_apply (r : ℕ) {ν : K} (hν : ν ≠ 0) (v : (Fin (2 * r) → K) × (Fin (2 * 0 + 1) → K))
    (s : Fin (2 * r) ⊕ Fin (2 * 0 + 1)) :
    oddLin r hν v (oddBlock r s) = oddScale r ν s * Sum.elim v.1 v.2 s := by
  have h : oddBlock r s = oddBlockEquiv r s := rfl
  rw [h, oddLin, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply]
  simp only [LinearMap.funLeft_apply, Equiv.symm_apply_apply, LinearEquiv.trans_apply,
    LinearEquiv.piCongrRight_apply, LinearEquiv.smulOfNeZero_apply, smul_eq_mul]
  rcases v with ⟨v₁, v₂⟩
  rcases s with i | j <;> rfl

/-- `H^r ⊥ ⟨ν⟩ ≅ Z_{r,ν}` (`splitOddForm r ν`; Thesis (5.2.1): `Z = ⊕_{i=1}^r ⟨z_i, z_{-i}⟩ ⊥ ⟨z_0⟩`
with `b(z_i, z_{-i}) = ν`, and `ν·H ≅ H`). -/
def splitOddIso (r : ℕ) {ν : K} (hν : ν ≠ 0) :
    ((hypForm K r).prod (splitOddForm 0 ν)).IsometryEquiv (splitOddForm r ν) where
  toLinearEquiv := oddLin r hν
  map_app' v := by
    obtain ⟨v₁, v₂⟩ := v
    change splitOddForm r ν (oddLin r hν (v₁, v₂)) = _
    rw [splitOddForm_apply, QuadraticMap.prod_apply, hypForm_apply, splitOddForm_apply,
      ← (oddBlockEquiv r).sum_comp, Fintype.sum_sum_type, mul_add]
    simp only [Finset.mul_sum]
    have hrev : ∀ s, ((oddBlockEquiv r) s).rev = oddBlockEquiv r (Sum.map Fin.rev id s) :=
      oddBlock_rev r
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hrev]
      have e1 : oddBlockEquiv r (Sum.inl i) = oddBlock r (Sum.inl i) := rfl
      have e2 : oddBlockEquiv r (Sum.map Fin.rev id (Sum.inl i)) = oddBlock r (Sum.inl i.rev) := rfl
      rw [e1, e2, oddLin_apply, oddLin_apply]
      simp only [Sum.elim_inl]
      calc ν * (oddScale r ν (Sum.inl i) * v₁ i * (oddScale r ν (Sum.inl i.rev) * v₁ i.rev))
          = (ν * (oddScale r ν (Sum.inl i) * oddScale r ν (Sum.inl i.rev))) *
              (v₁ i * v₁ i.rev) := by
            ring
        _ = v₁ i * v₁ i.rev := by rw [oddScale_mul_rev r hν, one_mul]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [hrev]
      have e1 : oddBlockEquiv r (Sum.inr j) = oddBlock r (Sum.inr j) := rfl
      have e2 : oddBlockEquiv r (Sum.map Fin.rev id (Sum.inr j)) = oddBlock r (Sum.inr j.rev) := by
        have : j.rev = j := Fin.ext (by have := j.isLt; simp)
        rw [this]; rfl
      rw [e1, e2, oddLin_apply, oddLin_apply]
      simp [oddScale]


section HypLine

variable [Invertible (2 : K)]

/-- `⟨ν⟩ ⊥ ⟨-ν⟩ ≅ H` (`H ≅ ⟨ν⟩ ⊥ ⟨-ν⟩`, Lam Ch. I; used in the swapped case of
`exists_leviSpec`): `(x, y) ↦ (ν(x - y)/2, x + y)`. -/
def hypLineLin {ν : K} (hν : ν ≠ 0) :
    ((Fin (2 * 0 + 1) → K) × (Fin (2 * 0 + 1) → K)) ≃ₗ[K] (Fin (2 * 1) → K) where
  toFun v i := if (i : ℕ) = 0 then ν * (v.1 0 - v.2 0) / 2 else v.1 0 + v.2 0
  map_add' v w := by
    funext i; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; split_ifs <;> ring
  map_smul' c v := by
    funext i; simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring
  invFun u := (fun _ => (u 1 + 2 * u 0 / ν) / 2, fun _ => (u 1 - 2 * u 0 / ν) / 2)
  left_inv v := by
    have h2 : (2 : K) ≠ 0 := Invertible.ne_zero (2 : K)
    obtain ⟨v₁, v₂⟩ := v
    have e1 : ∀ j : Fin (2 * 0 + 1), j = 0 := fun j => Fin.ext (by have := j.isLt; simp)
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      simp only [Fin.isValue, Fin.val_one, Fin.val_zero, one_ne_zero, ↓reduceIte] <;>
      rw [e1 j] <;> field_simp <;> ring
  right_inv u := by
    have h2 : (2 : K) ≠ 0 := Invertible.ne_zero (2 : K)
    funext i
    have hi : i = 0 ∨ i = 1 := by
      rcases i with ⟨i, hi⟩; rcases i with _ | _ | i
      · left; rfl
      · right; rfl
      · omega
    rcases hi with rfl | rfl <;> simp <;> field_simp <;> ring

omit [Invertible (2 : K)] in
theorem hypForm_one_apply (u : Fin (2 * 1) → K) : hypForm K 1 u = 2 * (u 0 * u 1) := by
  rw [hypForm_apply, Fin.sum_univ_two]
  have h0 : (0 : Fin (2 * 1)).rev = 1 := rfl
  have h1 : (1 : Fin (2 * 1)).rev = 0 := rfl
  rw [h0, h1]; ring

omit [Invertible (2 : K)] in
theorem splitOddForm_zero_apply' (ν : K) (x : Fin (2 * 0 + 1) → K) :
    splitOddForm 0 ν x = ν * (x 0 * x 0) := by
  rw [splitOddForm_apply, Fin.sum_univ_one]
  rfl

/-- `⟨ν⟩ ⊥ ⟨-ν⟩ ≅ H^1`. -/
def hypLineIso {ν : K} (hν : ν ≠ 0) :
    ((splitOddForm 0 ν).prod (splitOddForm 0 (-ν))).IsometryEquiv (hypForm K 1) where
  toLinearEquiv := hypLineLin hν
  map_app' v := by
    have h2 : (2 : K) ≠ 0 := Invertible.ne_zero (2 : K)
    change hypForm K 1 (hypLineLin hν v) = _
    rw [hypForm_one_apply, QuadraticMap.prod_apply, splitOddForm_zero_apply',
      splitOddForm_zero_apply']
    simp only [hypLineLin, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Fin.isValue,
      Fin.val_zero, Fin.val_one, one_ne_zero, ↓reduceIte]
    field_simp
    ring

end HypLine


section Split

variable [Invertible (2 : K)]

open QuadraticMap

omit [Invertible (2 : K)] in
theorem equiv_assoc {X Y Z : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    [AddCommGroup Z] [Module K Z] (Q₁ : QuadraticForm K X) (Q₂ : QuadraticForm K Y)
    (Q₃ : QuadraticForm K Z) : ((Q₁.prod Q₂).prod Q₃).Equivalent (Q₁.prod (Q₂.prod Q₃)) :=
  ⟨prodAssocIso Q₁ Q₂ Q₃⟩

omit [Invertible (2 : K)] in
theorem equiv_comm {X Y : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (Q₁ : QuadraticForm K X) (Q₂ : QuadraticForm K Y) : (Q₁.prod Q₂).Equivalent (Q₂.prod Q₁) :=
  ⟨IsometryEquiv.prodComm Q₁ Q₂⟩

omit [Invertible (2 : K)] in
theorem equiv_prod {X Y X' Y' : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    [AddCommGroup X'] [Module K X'] [AddCommGroup Y'] [Module K Y']
    {Q₁ : QuadraticForm K X} {Q₂ : QuadraticForm K Y} {Q₁' : QuadraticForm K X'}
    {Q₂' : QuadraticForm K Y'} (h₁ : Q₁.Equivalent Q₁') (h₂ : Q₂.Equivalent Q₂') :
    (Q₁.prod Q₂).Equivalent (Q₁'.prod Q₂') :=
  h₁.prod h₂

omit [Invertible (2 : K)] in
theorem equiv_hypAdd (a b : ℕ) :
    (hypForm K (a + b)).Equivalent ((hypForm K a).prod (hypForm K b)) :=
  ⟨(hypAddEquiv a b).symm⟩

omit [Invertible (2 : K)] in
theorem finrank_le_wittIndex {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (U : Submodule K V) (hU : IsTotallyIsotropic Q U) :
    Module.finrank K U ≤ wittIndex Q := by
  refine le_csSup ⟨Module.finrank K V, ?_⟩ ⟨U, hU, rfl⟩
  rintro n ⟨U', -, rfl⟩
  exact Submodule.finrank_le U'

/-- **Hyperbolic splitting off a totally isotropic subspace** (Lam Ch. I §3–4; Thesis §5.1.2:
`V = (Z ⊕ Z') ⊥ Ṽ` with `Z ⊕ Z' ≅ H^{dim Z}`): a nondegenerate `Q` with a totally isotropic `U` is
`H^{dim U} ⊥ Q'` with `Q'` nondegenerate (in coordinates).  From the Witt decomposition. -/
theorem exists_hypSplit {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : IsNondeg Q) (U : Submodule K V) (hU : IsTotallyIsotropic Q U) :
    ∃ (k : ℕ) (Q' : QuadraticForm K (Fin k → K)), IsNondeg Q' ∧
      Q.Equivalent ((hypForm K (Module.finrank K U)).prod Q') := by
  obtain ⟨k₀, Qa, -, he, -⟩ := witt_decomposition Q hQ
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (finrank_le_wittIndex Q U hU)
  rw [hc] at he
  let E := appendEquiv (K := K) (2 * c) k₀
  let Q' : QuadraticForm K (Fin (2 * c + k₀) → K) :=
    ((hypForm K c).prod Qa).comp (E.symm : (Fin (2 * c + k₀) → K) →ₗ[K] _)
  have hQ' : ((hypForm K c).prod Qa).Equivalent Q' := ⟨transportIso _ E⟩
  have key : Q.Equivalent ((hypForm K (Module.finrank K U)).prod Q') :=
    (Equivalent.trans (Q₁ := Q) he (equiv_prod (equiv_hypAdd _ _) (Equivalent.refl _))).trans
      ((equiv_assoc _ _ _).trans (equiv_prod (Equivalent.refl _) hQ'))
  obtain ⟨e⟩ := key
  exact ⟨_, Q', isNondeg_prod_right (isNondeg_of_isometryEquiv e hQ), ⟨e⟩⟩

end Split

end LeviAux

/-! ## 5. The Levi subgroups of `G` (Thesis §5.1.2, §9.3 (9.3.1)–(9.3.3)) -/

section Levi

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- The graded piece `Z_{i+1}/Z_i` of an isotropic flag; its `GL` is the `i`-th general linear
factor of the Levi subgroup (Thesis §5.1.2: `Z_{i+1} = Z_i ⊕ Z'_{i+1}`, `M ≅ ∏ GL(Z'_i) × GSpin(Ṽ)`). -/
abbrev IsotropicFlag.gr {Q : QuadraticForm F V} (FL : IsotropicFlag Q) (i : Fin FL.len) : Type _ :=
  ↥(FL.sub i.succ) ⧸ (FL.sub i.castSucc).comap (FL.sub i.succ).subtype

/-- `∏_i GL(Z_{i+1}/Z_i)`, the general linear part of the Levi of `P_F`. -/
abbrev IsotropicFlag.glPart {Q : QuadraticForm F V} (FL : IsotropicFlag Q) : Type _ :=
  (i : Fin FL.len) → LinearMap.GeneralLinearGroup F (FL.gr i)

omit [PAdicField F] in
/-- The largest member of a nonempty isotropic flag is nonzero. -/
theorem IsotropicFlag.one_le_finrank_top [FiniteDimensional F V] {Q : QuadraticForm F V}
    (FL : IsotropicFlag Q) (h : 0 < FL.len) : 1 ≤ finrank F ↥FL.top := by
  rw [Submodule.one_le_finrank_iff]
  intro htop
  have hlt : FL.sub 0 < FL.sub (Fin.last FL.len) :=
    FL.strictMono (show (0 : Fin (FL.len + 1)) < Fin.last FL.len from by
      rw [Fin.lt_def]; simp; omega)
  rw [FL.sub_zero] at hlt
  exact hlt.ne' htop

namespace GGPData

variable (d : GGPData F)

/-- The unipotent radical `U = N_{F_W} × N_{F_V}` lies in `P = P_{F_W} × P_{F_V}`
(Thesis §5.1.2). -/
theorem whittU_le_whittB (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) :
    d.whittU FW FV ≤ d.whittB FW FV :=
  fun _ hg => ⟨flagUnip_le_flagStab FW hg.1, flagUnip_le_flagStab FV hg.2⟩

/-- `U` is normal in `P` (Thesis §5.1.2, §5.2: `N` is the unipotent radical of `P`). -/
instance whittU_normal (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) :
    ((d.whittU FW FV).subgroupOf (d.whittB FW FV)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (d.whittU_le_whittB FW FV)]
  intro h k hh hk
  refine ⟨?_, ?_⟩
  · show d.fst (k * h * k⁻¹) ∈ flagUnip FW
    rw [map_mul, map_mul, map_inv]
    exact flagUnip_conj hk.1 hh.1
  · show d.snd (k * h * k⁻¹) ∈ flagUnip FV
    rw [map_mul, map_mul, map_inv]
    exact flagUnip_conj hk.2 hh.2

/-- The Levi quotient `P/U ≅ M` of `P = P_{F_W} × P_{F_V}`.  We use the canonical quotient rather
than a Levi complement (which would need a choice of complementary isotropic subspaces). -/
abbrev LeviQuot (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) : Type _ :=
  ↥(d.whittB FW FV) ⧸ (d.whittU FW FV).subgroupOf (d.whittB FW FV)

/-- **The GGP datum of a Levi subgroup** (Thesis §9.3, after (9.3.3)).
`d'` realizes the pair `(W̃, Ṽ)` of the Levi of `P = P_{F_W} × P_{F_V}`, where
`W ≅ H^{a_W} ⊥ W̃`, `V ≅ H^{a_V} ⊥ Ṽ`, `a_W = dim F_W.top`, `a_V = dim F_V.top`
(Thesis §5.1.2: `W̃` is the orthogonal complement of `⊕ (Z'_i ⊕ Z'_{-i})`, a hyperbolic space of
dimension `2 a_W`).  By Witt cancellation `W̃`, `Ṽ` are determined up to isometry.

"Admissible up to permutation" (Thesis §9.3): either `d'.W ≅ W̃` and
`d'.V ≅ Ṽ` (first disjunct), or the roles are exchanged, `d'.W ≅ Ṽ`, `d'.V ≅ W̃` (second
disjunct, a factor swap). -/
def LeviSpec (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) (d' : GGPData F) : Prop :=
  (Nonempty (d.QW.IsometryEquiv ((hypForm F (finrank F ↥FW.top)).prod d'.QW)) ∧
    Nonempty (d.QV.IsometryEquiv ((hypForm F (finrank F ↥FV.top)).prod d'.QV))) ∨
  (Nonempty (d.QW.IsometryEquiv ((hypForm F (finrank F ↥FW.top)).prod d'.QV)) ∧
    Nonempty (d.QV.IsometryEquiv ((hypForm F (finrank F ↥FV.top)).prod d'.QW)))

open LeviAux QuadraticMap in
/-- **Existence of the Levi GGP datum** (Thesis §5.1.2 and §9.3: "the pair `(W̃, Ṽ)` is easily
seen to be admissible up to permutation").  Proof: split `W ≅ H^{a_W} ⊥ W̃` and
`V ≅ H^{a_V} ⊥ Ṽ` off the tops of the flags (`exists_hypSplit`); `V = W ⊥ Z` and
`Z ≅ H^r ⊥ ⟨ν⟩` give `V ≅ H^{a_W + r} ⊥ (W̃ ⊥ ⟨ν⟩)`.  If `a_V ≤ a_W + r`, Witt cancellation gives
`Ṽ ≅ W̃ ⊥ Z_{a_W + r - a_V, ν}` (first disjunct).  Otherwise `a_V = a_W + r + t + 1`, cancellation
gives `H^{t+1} ⊥ Ṽ ≅ W̃ ⊥ ⟨ν⟩`, and with `H ≅ ⟨-ν⟩ ⊥ ⟨ν⟩` and a second cancellation of `⟨ν⟩`,
`W̃ ≅ Ṽ ⊥ Z_{t, -ν}` (second disjunct, with `ν' = -ν`).  Uses the cited
`witt_decomposition` and `witt_cancellation` only. -/
theorem exists_leviSpec (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) :
    ∃ d' : GGPData F, d.LeviSpec FW FV d' := by
  have hν : (d.ν : F) ≠ 0 := d.ν.ne_zero
  have hQV : IsNondeg d.QV := isNondeg_prod d.nondeg (isNondeg_splitOddForm d.r hν)
  obtain ⟨kW, W', hW', eW⟩ := exists_hypSplit d.QW d.nondeg FW.top (FW.isotropic _)
  obtain ⟨kV, V', hV', eV⟩ := exists_hypSplit d.QV hQV FV.top (FV.isotropic _)
  set aW := Module.finrank F ↥FW.top with haW
  set aV := Module.finrank F ↥FV.top with haV
  -- `V = W ⊥ Z ≅ H^{a_W + r} ⊥ (W̃ ⊥ ⟨ν⟩)`
  have eQV : d.QV.Equivalent
      ((hypForm F (aW + d.r)).prod (W'.prod (splitOddForm 0 (d.ν : F)))) := by
    have h1 : d.QV.Equivalent (((hypForm F aW).prod W').prod
        ((hypForm F d.r).prod (splitOddForm 0 (d.ν : F)))) :=
      equiv_prod eW ⟨(splitOddIso d.r hν).symm⟩
    exact (h1.trans ⟨IsometryEquiv.prodProdProdComm _ _ _ _⟩).trans
      (equiv_prod (equiv_hypAdd aW d.r).symm (Equivalent.refl _))
  by_cases hcase : aV ≤ aW + d.r
  · -- first disjunct: `Ṽ ≅ W̃ ⊥ Z_{s,ν}`, `s = a_W + r - a_V`
    obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hcase
    rw [hs] at eQV
    have e1 : ((hypForm F aV).prod V').Equivalent ((hypForm F aV).prod
        ((hypForm F s).prod (W'.prod (splitOddForm 0 (d.ν : F))))) :=
      (eV.symm.trans eQV).trans
        ((equiv_prod (equiv_hypAdd aV s) (Equivalent.refl _)).trans (equiv_assoc _ _ _))
    have c : V'.Equivalent ((hypForm F s).prod (W'.prod (splitOddForm 0 (d.ν : F)))) :=
      witt_cancellation _ _ _ e1
    have c2 : ((hypForm F s).prod (W'.prod (splitOddForm 0 (d.ν : F)))).Equivalent
        (W'.prod (splitOddForm s (d.ν : F))) :=
      by
      have a1 := (equiv_assoc (hypForm F s) W' (splitOddForm 0 (d.ν : F))).symm
      have a2 := equiv_prod (equiv_comm (hypForm F s) W')
        (Equivalent.refl (splitOddForm 0 (d.ν : F)))
      have a3 := equiv_assoc W' (hypForm F s) (splitOddForm 0 (d.ν : F))
      have a4 := equiv_prod (Equivalent.refl W') (⟨splitOddIso s hν⟩ :
        ((hypForm F s).prod (splitOddForm 0 (d.ν : F))).Equivalent (splitOddForm s (d.ν : F)))
      exact a1.trans (a2.trans (a3.trans a4))
    let d' : GGPData F := ⟨kW, W', hW', s, d.ν⟩
    have hd'V : d'.QV = W'.prod (splitOddForm s (d.ν : F)) := rfl
    refine ⟨d', Or.inl ⟨eW, ?_⟩⟩
    have := eV.trans (equiv_prod (Equivalent.refl _) (c.trans c2))
    rw [← hd'V] at this
    exact this
  · -- second disjunct (factor swap): `W̃ ≅ Ṽ ⊥ Z_{t,-ν}`, `a_V = a_W + r + t + 1`
    obtain ⟨t, ht⟩ : ∃ t, aV = aW + d.r + (t + 1) := ⟨aV - (aW + d.r) - 1, by omega⟩
    have eV' := eV
    rw [ht] at eV'
    have e1 : ((hypForm F (aW + d.r)).prod ((hypForm F (t + 1)).prod V')).Equivalent
        ((hypForm F (aW + d.r)).prod (W'.prod (splitOddForm 0 (d.ν : F)))) :=
      by
      have b1 := (equiv_assoc (hypForm F (aW + d.r)) (hypForm F (t + 1)) V').symm
      have b2 := equiv_prod (equiv_hypAdd (K := F) (aW + d.r) (t + 1)).symm (Equivalent.refl V')
      exact (b1.trans (b2.trans eV'.symm)).trans eQV
    have c : ((hypForm F (t + 1)).prod V').Equivalent (W'.prod (splitOddForm 0 (d.ν : F))) :=
      witt_cancellation _ _ _ e1
    have hν' : (-(d.ν : F)) ≠ 0 := neg_ne_zero.mpr hν
    have hl : (hypForm F 1).Equivalent
        ((splitOddForm 0 (-(d.ν : F))).prod (splitOddForm 0 (d.ν : F))) := by
      have h := hypLineIso (K := F) hν'
      rw [neg_neg] at h
      exact ⟨h.symm⟩
    have hX : (((hypForm F t).prod (splitOddForm 0 (-(d.ν : F)))).prod
        (splitOddForm 0 (d.ν : F))).Equivalent (hypForm F (t + 1)) :=
      by
      have b1 := equiv_assoc (hypForm F t) (splitOddForm 0 (-(d.ν : F)))
        (splitOddForm 0 (d.ν : F))
      have b2 := equiv_prod (Equivalent.refl (hypForm F t)) hl.symm
      have b3 := (equiv_hypAdd (K := F) t 1).symm
      exact b1.trans (b2.trans b3)
    have e2 : ((splitOddForm 0 (d.ν : F)).prod (V'.prod (splitOddForm t (-(d.ν : F))))).Equivalent
        ((splitOddForm 0 (d.ν : F)).prod W') := by
      have s1 := equiv_prod (Equivalent.refl (splitOddForm 0 (d.ν : F)))
        (equiv_prod (Equivalent.refl V') (⟨(splitOddIso t hν').symm⟩ :
          (splitOddForm t (-(d.ν : F))).Equivalent
            ((hypForm F t).prod (splitOddForm 0 (-(d.ν : F))))))
      have s2 := equiv_comm (splitOddForm 0 (d.ν : F))
        (V'.prod ((hypForm F t).prod (splitOddForm 0 (-(d.ν : F)))))
      have s3 := equiv_assoc V' ((hypForm F t).prod (splitOddForm 0 (-(d.ν : F))))
        (splitOddForm 0 (d.ν : F))
      have s4 := equiv_comm V' (((hypForm F t).prod (splitOddForm 0 (-(d.ν : F)))).prod
        (splitOddForm 0 (d.ν : F)))
      have s5 := equiv_prod hX (Equivalent.refl V')
      have s6 := equiv_comm W' (splitOddForm 0 (d.ν : F))
      exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (c.trans s6)))))
    have c3 : (V'.prod (splitOddForm t (-(d.ν : F)))).Equivalent W' :=
      witt_cancellation _ _ _ e2
    let d' : GGPData F := ⟨kV, V', hV', t, -d.ν⟩
    have hd'V : d'.QV = V'.prod (splitOddForm t (-(d.ν : F))) := rfl
    refine ⟨d', Or.inr ⟨?_, eV⟩⟩
    have := eW.trans (equiv_prod (Equivalent.refl _) c3.symm)
    rw [← hd'V] at this
    exact this

/-- The GGP datum `(G̃, H̃, ξ̃)` attached to the Levi of `P = P_{F_W} × P_{F_V}` (Thesis §9.3,
§7.3 "`L = L^{GL} × G̃`"), well defined up to isomorphism.  Epsilon pattern
on `LeviSpec`; the junk value `d` is never used, by `exists_leviSpec`. -/
def leviSmall (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) : GGPData F :=
  if h : ∃ d' : GGPData F, d.LeviSpec FW FV d' then h.choose else d

theorem leviSmall_spec (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) :
    d.LeviSpec FW FV (d.leviSmall FW FV) := by
  unfold leviSmall
  split
  · rename_i h'; exact h'.choose_spec
  · rename_i h'; exact absurd (d.exists_leviSpec FW FV) h'

/-- `dim GSpin(n + 2) = dim GSpin(n) + 2n + 1`. -/
theorem dimGSpin_add_two (n : ℕ) : dimGSpin (n + 2) = dimGSpin n + (2 * n + 1) := by
  unfold dimGSpin
  rcases n with _ | n
  · rfl
  · have h1 : (n + 1 + 2) * (n + 1 + 2 - 1) = (n + 1) * (n + 1 - 1) + 2 * (2 * (n + 1) + 1) := by
      rw [show n + 1 + 2 - 1 = n + 2 by omega, show n + 1 - 1 = n by omega]
      ring
    rw [h1, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    ring

theorem dimGSpin_mono {a b : ℕ} (h : a ≤ b) : dimGSpin a ≤ dimGSpin b := by
  unfold dimGSpin
  have : a * (a - 1) ≤ b * (b - 1) := Nat.mul_le_mul h (Nat.sub_le_sub_right h 1)
  have := Nat.div_le_div_right (c := 2) this
  omega

theorem dimGSpin_lt_add_two_mul {n a : ℕ} (ha : 1 ≤ a) : dimGSpin n < dimGSpin (n + 2 * a) := by
  have h1 : dimGSpin n < dimGSpin (n + 2) := by rw [dimGSpin_add_two]; omega
  exact lt_of_lt_of_le h1 (dimGSpin_mono (by omega))

/-- Dimension count for a Levi datum: `dim W = 2 a_W + dim W̃`, `dim V = 2 a_V + dim Ṽ`, and
`dim G̃ = dim GSpin(W̃) + dim GSpin(Ṽ)` whichever way round `(W̃, Ṽ)` is realized. -/
theorem dimG_of_leviSpec {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV} {d' : GGPData F}
    (h : d.LeviSpec FW FV d') :
    ∃ mW mV : ℕ, d.m = 2 * finrank F ↥FW.top + mW ∧
      d.m + 2 * d.r + 1 = 2 * finrank F ↥FV.top + mV ∧ d'.dimG = dimGSpin mW + dimGSpin mV := by
  have hfW : ∀ (Q' : QuadraticForm F (Fin d.m → F)) {X : Type _} [AddCommGroup X] [Module F X]
      [Module.Free F X] [Module.Finite F X] (QX : QuadraticForm F X) (k : ℕ),
      Nonempty (Q'.IsometryEquiv ((hypForm F k).prod QX)) → d.m = 2 * k + finrank F X := by
    rintro Q' X _ _ _ _ QX k ⟨φ⟩
    have := φ.toLinearEquiv.finrank_eq
    simpa [Module.finrank_prod] using this
  have hfV : ∀ (Q' : QuadraticForm F d.V) {X : Type _} [AddCommGroup X] [Module F X]
      [Module.Free F X] [Module.Finite F X] (QX : QuadraticForm F X) (k : ℕ),
      Nonempty (Q'.IsometryEquiv ((hypForm F k).prod QX)) →
        d.m + (2 * d.r + 1) = 2 * k + finrank F X := by
    rintro Q' X _ _ _ _ QX k ⟨φ⟩
    have := φ.toLinearEquiv.finrank_eq
    simpa [Module.finrank_prod] using this
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨d'.m, d'.m + 2 * d'.r + 1, by simpa using hfW _ _ _ h1, ?_, rfl⟩
    have := hfV _ _ _ h2
    simp only [Module.finrank_prod, Module.finrank_fin_fun] at this
    omega
  · refine ⟨d'.m + 2 * d'.r + 1, d'.m, ?_, ?_, by rw [GGPData.dimG]; ring⟩
    · have := hfW _ _ _ h1
      simp only [Module.finrank_prod, Module.finrank_fin_fun] at this
      omega
    · have := hfV _ _ _ h2
      simp only [Module.finrank_fin_fun] at this
      omega

/-- **The Levi datum is strictly smaller** (Thesis §7.2: the induction hypothesis (HYP) applies
to the GGP triples of proper Levi subgroups): for a proper flag pair,
`dim G̃ < dim G`.  Arithmetic from `dimG_of_leviSpec`: a nonempty flag has `a ≥ 1`.  Stated with
the explicit hypothesis "one flag is nonempty", which a proper flag pair satisfies
(`IsProperFlagPair.len_pos`). -/
theorem dimG_lt_of_leviSpec {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV} {d' : GGPData F}
    (h : d.LeviSpec FW FV d') (hP : 0 < FW.len ∨ 0 < FV.len) : d'.dimG < d.dimG := by
  obtain ⟨mW, mV, hW, hV, hd'⟩ := d.dimG_of_leviSpec h
  rw [hd', GGPData.dimG]
  have eW : d.m = mW + 2 * finrank F ↥FW.top := by omega
  have eV : d.m + 2 * d.r + 1 = mV + 2 * finrank F ↥FV.top := by omega
  have k1 : dimGSpin d.m = dimGSpin (mW + 2 * finrank F ↥FW.top) := congrArg dimGSpin eW
  have k2 : dimGSpin (d.m + 2 * d.r + 1) = dimGSpin (mV + 2 * finrank F ↥FV.top) :=
    congrArg dimGSpin eV
  rw [k2, k1]
  rcases hP with hP | hP
  · have := FW.one_le_finrank_top hP
    exact Nat.add_lt_add_of_lt_of_le (dimGSpin_lt_add_two_mul this) (dimGSpin_mono (by omega))
  · have := FV.one_le_finrank_top hP
    exact Nat.add_lt_add_of_le_of_lt (dimGSpin_mono (by omega)) (dimGSpin_lt_add_two_mul this)

/-- `dim G̃ < dim G` for the Levi datum of a proper parabolic. -/
theorem dimG_leviSmall_lt {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV}
    (hP : d.IsProperFlagPair FW FV) : (d.leviSmall FW FV).dimG < d.dimG :=
  d.dimG_lt_of_leviSpec (d.leviSmall_spec FW FV) hP.len_pos

/-- **The Levi decomposition** (Thesis §5.1.2 "natural isomorphism
`M ≃ GL(Z'_1) × ⋯ × GL(Z'_k) × GSpin(Ṽ)`", §9.3 (9.3.1)–(9.3.3)): for any GGP
datum `d'` realizing the Levi pair `(W̃, Ṽ)`, there is a surjective homomorphism from the Levi
quotient `P/U` of `P = P_{F_W} × P_{F_V}` onto `∏ GL(Z_{i+1,W}/Z_{i,W}) × ∏ GL(Z_{j+1,V}/Z_{j,V}) × G̃(F)`
with central kernel.  (The literature gives an isomorphism, Asgari's description of the Levi
subgroups of `GSpin`; the weaker form is what is used here.)  Left as
`sorry`: it needs the Clifford-algebra description of the Levi (the `GL` factors sit in
`GSpin(Z'_i ⊕ Z'_{-i})`), which is not formalized.

Caveat for its use in Thesis Cor 9.5.1 / Prop 7.4.1(i) (`mult_parInd_eq_mGeom`, Spectral): those
need the `G̃(F)`-component to be the Levi projection
`M ≅ ∏ GL(Z'_i) × GSpin(Ṽ)` built from a character `λ` of the split part with `λ(c) = c` on the
centre (not restriction to `Ṽ`), carrying the image of `H_{Q̄}`
onto `H̃` and
`A_{G,H}` onto `A_{G̃,H̃}`.  "Some surjection with central kernel" does not pin that down; a
strengthened sibling recording these compatibilities is needed before Cor 9.5.1 can be stated. -/
theorem exists_leviHom_of_leviSpec (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV)
    (d' : GGPData F) (h : d.LeviSpec FW FV d') :
    ∃ φ : d.LeviQuot FW FV →* FW.glPart × FV.glPart × ↥d'.G,
      Function.Surjective φ ∧ φ.ker ≤ Subgroup.center (d.LeviQuot FW FV) := by
  sorry

/-- The Levi decomposition for `leviSmall`. -/
theorem exists_leviHom (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) :
    ∃ φ : d.LeviQuot FW FV →* FW.glPart × FV.glPart × ↥(d.leviSmall FW FV).G,
      Function.Surjective φ ∧ φ.ker ≤ Subgroup.center (d.LeviQuot FW FV) :=
  d.exists_leviHom_of_leviSpec FW FV _ (d.leviSmall_spec FW FV)

end GGPData

end Levi


/-! ## 6. Parabolic induction (Thesis §3.2, §5.1.2; BZ 1977 §2; BP §1.5)

Normalized parabolic induction `i_P^G(σ)` from a unitary representation `σ` of the Levi quotient
`M = P/U` of `P = P_{F_W} × P_{F_V}`, as a `UnitaryRep` of `G(F)` (real data): the completion of
the smooth induced space for the norm `∫_K ‖f(k)‖² dk`, `G(F) = P(F) K`, with `G(F)` acting by right
translation.  Proved: the inner-product structure, `ρ(1) = 1`, `ρ(gh) = ρ(g)ρ(h)`, unitarity of
each `ρ(g)`, the invariance of the inner product under right translation
(`ParIndData.preInner_rightTrans`, the place where `δ_P^{1/2}` and `G = PK` enter; from the
literature axiom `integral_eq_mul_integral_compact_integral` and the unimodularity of `G(F)`) and strong
continuity (`ParIndData.continuous_rho_apply`). -/

namespace GGPData

variable (d : GGPData F)

section LeviTop

variable (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV)

instance locallyCompactSpace_whittB : LocallyCompactSpace ↥(d.whittB FW FV) :=
  (d.isClosed_whittB FW FV).locallyCompactSpace

instance isClosed_whittU_subgroupOf :
    IsClosed (((d.whittU FW FV).subgroupOf (d.whittB FW FV) : Subgroup ↥(d.whittB FW FV)) :
      Set ↥(d.whittB FW FV)) :=
  (d.isClosed_whittU FW FV).preimage continuous_subtype_val

instance t3Space_leviQuot : T3Space (d.LeviQuot FW FV) :=
  @QuotientGroup.instT3Space _ _ _ _ ((d.whittU FW FV).subgroupOf (d.whittB FW FV)) _
    (d.isClosed_whittU_subgroupOf FW FV)

instance t2Space_leviQuot : T2Space (d.LeviQuot FW FV) :=
  (d.t3Space_leviQuot FW FV).t25Space.t2Space

/-- The Borel σ-algebra on `M = P/U` (priority over Mathlib's quotient σ-algebra, as for
`GmodAG` in `TraceFormula/Basic.lean`; the two agree for Polish groups, which is not needed). -/
instance (priority := 1100) measurableSpace_leviQuot : MeasurableSpace (d.LeviQuot FW FV) :=
  borel _

instance borelSpace_leviQuot : BorelSpace (d.LeviQuot FW FV) := ⟨rfl⟩

/-- `P(F)` is second countable (a subspace of `G(F)`). -/
instance secondCountableTopology_whittB : SecondCountableTopology ↥(d.whittB FW FV) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

/-- The modular character `δ_P` of `P(F) = P_{F_W} × P_{F_V}` (BP §1.5; Mathlib's
`modularCharacter`, `μ(E p⁻¹) = δ_P(p) μ(E)` for a left Haar measure `μ`, so that
`δ_P(p) = |det Ad(p)|_{𝔲}|`; the same convention as `IwasawaDatum.deltaP0` in
`TraceFormula/Analytic.lean`, checked there on `F^× ⋉ F`). -/
def deltaP (p : ↥(d.whittB FW FV)) : ℝ := (Measure.modularCharacter p : ℝ)

end LeviTop

/-- **Data of a parabolically induced representation** `i_P^G(σ)` (Thesis §3.2, §5.1.2; BP §1.5):
a parabolic subgroup `P = P_{F_W} × P_{F_V}` (`whittB`, Thesis §5.1.2: every parabolic subgroup of
`G` is of this form up to conjugacy), a compact open subgroup `K` with `G(F) = P(F) K` (the norm
of `i_P^G(σ)` is taken on `K`; Bruhat–Tits gives such a `K`, a good maximal compact subgroup, but
this is not needed to *define* `i_P^G(σ)`), and a unitary representation `σ` of the Levi quotient
`M = P/U` (`LeviQuot`, the canonical model of the Levi factor). -/
structure ParIndData where
  FW : IsotropicFlag d.QW
  FV : IsotropicFlag d.QV
  K : Subgroup ↥d.G
  isOpen_K : IsOpen (K : Set ↥d.G)
  isCompact_K : IsCompact (K : Set ↥d.G)
  mul_eq : ∀ g : ↥d.G, ∃ p ∈ d.whittB FW FV, ∃ k ∈ K, g = p * k
  σ : UnitaryRep (d.LeviQuot FW FV)

namespace ParIndData

variable {d} (D : d.ParIndData)

/-- The parabolic subgroup `P(F)`. -/
abbrev P : Subgroup ↥d.G := d.whittB D.FW D.FV

/-- The smooth vectors of `i_P^G(σ)`: functions `f : G(F) → H_σ` with
`f(pg) = δ_P(p)^{1/2} σ(pU) f(g)` that are right invariant under an open subgroup (BZ 1977 §2,
Thesis §3.2). -/
def smoothSpace : Submodule ℂ (↥d.G → D.σ.H) where
  carrier := {f | (∀ (p : ↥D.P) (g : ↥d.G),
      f ((p : ↥d.G) * g) =
        ((Real.sqrt (d.deltaP D.FW D.FV p) : ℝ) : ℂ) • D.σ.ρ (QuotientGroup.mk p) (f g)) ∧
    ∃ K' : Subgroup ↥d.G, IsOpen (K' : Set ↥d.G) ∧ ∀ g : ↥d.G, ∀ k ∈ K', f (g * k) = f g}
  zero_mem' := ⟨fun p g => by simp, ⊤, isOpen_univ, fun _ _ _ => rfl⟩
  add_mem' := by
    rintro f₁ f₂ ⟨h₁, K₁, hK₁, i₁⟩ ⟨h₂, K₂, hK₂, i₂⟩
    refine ⟨fun p g => ?_, K₁ ⊓ K₂, hK₁.inter hK₂, fun g k hk => ?_⟩
    · simp only [Pi.add_apply, h₁ p g, h₂ p g, map_add, smul_add]
    · simp only [Pi.add_apply, i₁ g k hk.1, i₂ g k hk.2]
  smul_mem' := by
    rintro c f ⟨h, K', hK', i⟩
    refine ⟨fun p g => ?_, K', hK', fun g k hk => ?_⟩
    · simp only [Pi.smul_apply, h p g, map_smul, smul_comm c]
    · simp only [Pi.smul_apply, i g k hk]

theorem continuous_of_mem_smoothSpace {f : ↥d.G → D.σ.H} (hf : f ∈ D.smoothSpace) :
    Continuous f := by
  obtain ⟨-, K', hK', i⟩ := hf
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hmem : {x : ↥d.G | g⁻¹ * x ∈ K'} ∈ 𝓝 g := by
    refine (hK'.preimage (continuous_const.mul continuous_id)).mem_nhds ?_
    simp [K'.one_mem]
  refine (continuousAt_const (y := f g)).congr (Filter.eventually_of_mem hmem fun x hx => ?_)
  have := i g _ hx
  rw [mul_inv_cancel_left] at this
  exact this.symm

/-- The pre-Hilbert space of smooth vectors (a type synonym, so that the `Pi` topology of
`G(F) → H_σ` does not leak into the norm topology). -/
def Pre : Type := ↥D.smoothSpace

instance : AddCommGroup D.Pre := inferInstanceAs (AddCommGroup ↥D.smoothSpace)
instance : Module ℂ D.Pre := inferInstanceAs (Module ℂ ↥D.smoothSpace)

/-- The underlying function. -/
def toFun (f : D.Pre) : ↥d.G → D.σ.H := (f : ↥D.smoothSpace).1

@[simp] theorem toFun_add (f₁ f₂ : D.Pre) : D.toFun (f₁ + f₂) = D.toFun f₁ + D.toFun f₂ := rfl
@[simp] theorem toFun_smul (c : ℂ) (f : D.Pre) : D.toFun (c • f) = c • D.toFun f := rfl

theorem toFun_mem (f : D.Pre) : D.toFun f ∈ D.smoothSpace := (f : ↥D.smoothSpace).2

instance compactSpace_K : CompactSpace ↥D.K := isCompact_iff_compactSpace.mp D.isCompact_K

/-- `⟨f₁, f₂⟩ = ∫_K ⟨f₁(k), f₂(k)⟩ dk` (any Haar measure on `K`; the normalization only rescales
the norm). -/
def preInner (f₁ f₂ : D.Pre) : ℂ :=
  ∫ k : ↥D.K, inner ℂ (D.toFun f₁ k) (D.toFun f₂ k) ∂(Measure.haar : Measure ↥D.K)

/-- Smooth vectors are continuous (locally constant), hence `⟨f₁, f₂⟩` is integrable on the
compact `K`. -/
theorem integrable_inner (f₁ f₂ : D.Pre) :
    Integrable (fun k : ↥D.K => inner ℂ (D.toFun f₁ k) (D.toFun f₂ k))
      (Measure.haar : Measure ↥D.K) := by
  have h₁ := D.continuous_of_mem_smoothSpace (D.toFun_mem f₁)
  have h₂ := D.continuous_of_mem_smoothSpace (D.toFun_mem f₂)
  have hc : Continuous (fun k : ↥D.K => inner ℂ (D.toFun f₁ k) (D.toFun f₂ k)) :=
    (h₁.comp continuous_subtype_val).inner (h₂.comp continuous_subtype_val)
  exact integrableOn_univ.1 (hc.continuousOn.integrableOn_compact isCompact_univ)

theorem preInner_conj_symm (f₁ f₂ : D.Pre) :
    (starRingEnd ℂ) (D.preInner f₂ f₁) = D.preInner f₁ f₂ := by
  unfold preInner
  have h := integral_conj (μ := (Measure.haar : Measure ↥D.K))
    (f := fun k : ↥D.K => inner ℂ (D.toFun f₂ k) (D.toFun f₁ k))
  refine h.symm.trans ?_
  congr 1
  funext k
  exact inner_conj_symm _ _

theorem preInner_re_nonneg (f : D.Pre) : 0 ≤ RCLike.re (D.preInner f f) := by
  unfold preInner
  rw [← integral_re (D.integrable_inner f f)]
  exact integral_nonneg fun k => inner_self_nonneg

theorem preInner_add_left (f₁ f₂ f₃ : D.Pre) :
    D.preInner (f₁ + f₂) f₃ = D.preInner f₁ f₃ + D.preInner f₂ f₃ := by
  unfold preInner
  refine Eq.trans ?_ (integral_add (D.integrable_inner f₁ f₃) (D.integrable_inner f₂ f₃))
  congr 1
  funext k
  exact inner_add_left _ _ _

theorem preInner_smul_left (f₁ f₂ : D.Pre) (c : ℂ) :
    D.preInner (c • f₁) f₂ = (starRingEnd ℂ) c * D.preInner f₁ f₂ := by
  unfold preInner
  refine Eq.trans ?_ (integral_const_mul (μ := (Measure.haar : Measure ↥D.K)) ((starRingEnd ℂ) c)
    (fun k : ↥D.K => inner ℂ (D.toFun f₁ k) (D.toFun f₂ k)))
  congr 1
  funext k
  exact inner_smul_left _ _ _

/-- The pre-inner product `⟨f₁, f₂⟩ = ∫_K ⟨f₁(k), f₂(k)⟩ dk` (positive semidefinite; it is
definite, by `G = PK` and local constancy, but this is not needed: Mathlib's completion of a
seminormed space is Hausdorff). -/
@[instance_reducible]
def core : PreInnerProductSpace.Core ℂ D.Pre where
  inner := D.preInner
  conj_inner_symm := D.preInner_conj_symm
  re_inner_nonneg := D.preInner_re_nonneg
  add_left := D.preInner_add_left
  smul_left := D.preInner_smul_left

instance seminormed : SeminormedAddCommGroup D.Pre :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ D.Pre _ _ _ D.core

instance innerProductSpace : InnerProductSpace ℂ D.Pre := InnerProductSpace.ofCore D.core

theorem inner_def (f₁ f₂ : D.Pre) : inner ℂ f₁ f₂ = D.preInner f₁ f₂ := rfl

theorem norm_def (f : D.Pre) : ‖f‖ = Real.sqrt (RCLike.re (D.preInner f f)) := rfl

/-- Right translation preserves the smooth induced space. -/
theorem rightTrans_mem (g : ↥d.G) {f : ↥d.G → D.σ.H} (hf : f ∈ D.smoothSpace) :
    (fun x => f (x * g)) ∈ D.smoothSpace := by
  obtain ⟨h, K', hK', i⟩ := hf
  refine ⟨fun p x => by simp only [mul_assoc, h p (x * g)], K'.comap (MulAut.conj g⁻¹).toMonoidHom,
    hK'.preimage (show Continuous fun k : ↥d.G => g⁻¹ * k * g⁻¹⁻¹ from by fun_prop),
    fun x k hk => ?_⟩
  have hk' : g⁻¹ * k * g ∈ K' := by simpa [MulAut.conj_apply] using hk
  have := i (x * g) _ hk'
  simp only [mul_assoc, mul_inv_cancel_left] at this ⊢
  exact this

/-- Right translation `R_g f (x) = f(x g)` on the smooth induced space. -/
def rightTransLin (g : ↥d.G) : D.Pre →ₗ[ℂ] D.Pre where
  toFun f := (⟨fun x => D.toFun f (x * g), D.rightTrans_mem g (D.toFun_mem f)⟩ : ↥D.smoothSpace)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toFun_rightTransLin (g : ↥d.G) (f : D.Pre) (x : ↥d.G) :
    D.toFun (D.rightTransLin g f) x = D.toFun f (x * g) := rfl

/-! ### The invariant form on `δ_P`-equivariant functions (for `preInner_rightTrans`) -/

/-- `⟨c U a, c U b⟩ = r ⟨a, b⟩` for `U` unitary and `c = √r`, `r ≥ 0`. -/
theorem inner_sqrt_smul_unitary {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E)) {r : ℝ} (hr : 0 ≤ r)
    (a b : E) :
    inner ℂ (((Real.sqrt r : ℝ) : ℂ) • U a) (((Real.sqrt r : ℝ) : ℂ) • U b) =
      (r : ℂ) * inner ℂ a b := by
  rw [inner_smul_left, inner_smul_right, ContinuousLinearMap.inner_map_map_of_mem_unitary hU,
    Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt hr]

/-- The equivariance `f(p x) = δ_P(p)^{1/2} σ(p) f(x)` of a smooth vector. -/
theorem apply_mul_of_mem {f : ↥d.G → D.σ.H} (hf : f ∈ D.smoothSpace) (p : ↥D.P) (x : ↥d.G) :
    f ((p : ↥d.G) * x) =
      ((Real.sqrt (d.deltaP D.FW D.FV p) : ℝ) : ℂ) • D.σ.ρ (QuotientGroup.mk p) (f x) := by
  obtain ⟨h, -⟩ := hf
  exact h p x

/-- `⟨f₁(p x), f₂(p x)⟩ = δ_P(p) ⟨f₁(x), f₂(x)⟩` (`σ` is unitary and `δ_P^{1/2}` is real). -/
theorem inner_toFun_mul (f₁ f₂ : D.Pre) (p : ↥D.P) (x : ↥d.G) :
    inner ℂ (D.toFun f₁ ((p : ↥d.G) * x)) (D.toFun f₂ ((p : ↥d.G) * x)) =
      (d.deltaP D.FW D.FV p : ℂ) * inner ℂ (D.toFun f₁ x) (D.toFun f₂ x) := by
  have e1 := D.apply_mul_of_mem (D.toFun_mem f₁) p x
  have e2 := D.apply_mul_of_mem (D.toFun_mem f₂) p x
  have h := inner_sqrt_smul_unitary (D.σ.unitary_ρ (QuotientGroup.mk p))
    (NNReal.coe_nonneg (Measure.modularCharacter p)) (D.toFun f₁ x) (D.toFun f₂ x)
  exact (congrArg₂ (fun a b => inner ℂ a b) e1 e2).trans h

/-- `P(F) ∩ K`, as a subset of `P(F)`. -/
def PK : Set ↥D.P := {p | (p : ↥d.G) ∈ D.K}

theorem isOpen_PK : IsOpen D.PK := D.isOpen_K.preimage continuous_subtype_val

theorem isCompact_PK : IsCompact D.PK :=
  (d.isClosed_whittB D.FW D.FV).isClosedEmbedding_subtypeVal.isCompact_preimage D.isCompact_K

/-- `0 < μ_P(P ∩ K) < ∞` (`P ∩ K` is open, nonempty and compact in `P`). -/
theorem haar_real_PK_pos : 0 < (Measure.haar : Measure ↥D.P).real D.PK := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (D.isOpen_PK.measure_pos _ ⟨1, D.K.one_mem⟩).ne'
    D.isCompact_PK.measure_lt_top.ne

/-- `map (· * q) μ_P = δ_P(q) • μ_P` (the defining property of the modular character). -/
theorem map_mul_right_haar_P (q : ↥D.P) :
    Measure.map (· * q) (Measure.haar : Measure ↥D.P) =
      Measure.modularCharacter q • (Measure.haar : Measure ↥D.P) := by
  show _ = Measure.modularCharacterFun q • _
  rw [Measure.modularCharacterFun_eq_haarScalarFactor Measure.haar q]
  exact Measure.isMulLeftInvariant_eq_smul _ _

set_option maxHeartbeats 1000000 in
/-- `δ_P = 1` on the compact open subgroup `P(F) ∩ K`. -/
theorem deltaP_eq_one {s : ↥D.P} (hs : s ∈ D.PK) : d.deltaP D.FW D.FV s = 1 := by
  have hmeas : MeasurableSet D.PK := D.isOpen_PK.measurableSet
  have h := congrArg (fun μ : Measure ↥D.P => μ D.PK) (D.map_mul_right_haar_P s)
  beta_reduce at h
  have hpre : (· * s) ⁻¹' D.PK = D.PK := by
    ext p
    simp only [Set.mem_preimage, PK, Set.mem_ofPred_eq, Subgroup.coe_mul]
    exact ⟨fun h => by simpa using D.K.mul_mem h (D.K.inv_mem hs), fun h => D.K.mul_mem h hs⟩
  rw [Measure.map_apply (measurable_mul_const s) hmeas, hpre, Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul] at h
  have h0 := (D.isOpen_PK.measure_pos (Measure.haar : Measure ↥D.P) ⟨1, D.K.one_mem⟩).ne'
  have htop := D.isCompact_PK.measure_lt_top (μ := (Measure.haar : Measure ↥D.P)).ne
  have h1 : ((Measure.modularCharacter s : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj h0 htop).1 (h.symm.trans (one_mul _).symm)
  unfold deltaP
  rw [ENNReal.coe_eq_one] at h1
  rw [h1, NNReal.coe_one]

set_option maxHeartbeats 1000000 in
/-- `∫_P 1_{P ∩ K}(p q) dp = δ_P(q) μ_P(P ∩ K)`. -/
theorem integral_indicator_PK_mul_right (q : ↥D.P) :
    ∫ p : ↥D.P, D.PK.indicator (fun _ => (1 : ℂ)) (p * q) ∂(Measure.haar : Measure ↥D.P) =
      (d.deltaP D.FW D.FV q : ℂ) * ((Measure.haar : Measure ↥D.P).real D.PK : ℂ) := by
  have hmeas : MeasurableSet D.PK := D.isOpen_PK.measurableSet
  have hm := integral_map (μ := (Measure.haar : Measure ↥D.P))
    (measurable_mul_const q).aemeasurable
    ((measurable_const.indicator hmeas).aestronglyMeasurable (f := D.PK.indicator fun _ => (1 : ℂ)))
  rw [← hm, D.map_mul_right_haar_P q, integral_smul_nnreal_measure, integral_indicator_const _ hmeas]
  unfold deltaP
  rw [NNReal.smul_def, Complex.real_smul, Complex.real_smul, mul_one]

set_option maxHeartbeats 1000000 in
/-- **The `G = P K` invariance**: for continuous `φ` on `G(F)` with `φ(p x) = δ_P(p) φ(x)`,
`∫_K φ(k g) dk = ∫_K φ(k) dk`.  Proof: `β = 1_K φ` is continuous with compact support, and
`∫_P β(p x) dp = μ_P(P ∩ K) φ(x)` for every `x` (write `x = q k₀`, `G = P K`, and use
`δ_P = 1` on `P ∩ K`); then the integration formula for `G = P K` and the right invariance of the
Haar measure of `G(F)` give `μ_P(P ∩ K) ∫_K φ(k g) dk = c⁻¹ ∫_G β(x g) dx = c⁻¹ ∫_G β(x) dx =
μ_P(P ∩ K) ∫_K φ(k) dk`. -/
theorem integral_K_mul_right {φ : ↥d.G → ℂ} (hφ : Continuous φ)
    (hφP : ∀ (p : ↥D.P) (x : ↥d.G), φ ((p : ↥d.G) * x) = (d.deltaP D.FW D.FV p : ℂ) * φ x)
    (g : ↥d.G) :
    ∫ k : ↥D.K, φ ((k : ↥d.G) * g) ∂(Measure.haar : Measure ↥D.K) =
      ∫ k : ↥D.K, φ k ∂(Measure.haar : Measure ↥D.K) := by
  set mS : ℝ := (Measure.haar : Measure ↥D.P).real D.PK with hmS
  set β : ↥d.G → ℂ := (D.K : Set ↥d.G).indicator φ with hβ
  have hKclopen : IsClopen (D.K : Set ↥d.G) := ⟨D.K.isClosed_of_isOpen D.isOpen_K, D.isOpen_K⟩
  have hβc : Continuous β :=
    continuous_indicator (by simp [hKclopen.frontier_eq]) hφ.continuousOn
  have hβs : HasCompactSupport β :=
    HasCompactSupport.intro D.isCompact_K fun x hx => Set.indicator_of_notMem hx _
  have hfib : ∀ x : ↥d.G,
      ∫ p : ↥D.P, β ((p : ↥d.G) * x) ∂(Measure.haar : Measure ↥D.P) = (mS : ℂ) * φ x := by
    intro x
    obtain ⟨q, hq, k₀, hk₀, rfl⟩ := D.mul_eq x
    have e : ∀ p : ↥D.P, β ((p : ↥d.G) * (q * k₀)) =
        D.PK.indicator (fun _ => (1 : ℂ)) (p * ⟨q, hq⟩) * φ k₀ := by
      intro p
      by_cases hp : p * ⟨q, hq⟩ ∈ D.PK
      · have hp' : (p : ↥d.G) * q ∈ D.K := hp
        have hmem : (p : ↥d.G) * (q * k₀) ∈ D.K := by
          rw [← mul_assoc]; exact D.K.mul_mem hp' hk₀
        rw [hβ, Set.indicator_of_mem hmem, Set.indicator_of_mem hp, one_mul, ← mul_assoc]
        have := hφP (p * ⟨q, hq⟩) k₀
        rw [D.deltaP_eq_one hp, Complex.ofReal_one, one_mul] at this
        exact this
      · have hmem : (p : ↥d.G) * (q * k₀) ∉ D.K := fun h => hp (by
          have := D.K.mul_mem h (D.K.inv_mem hk₀)
          rw [← mul_assoc, mul_inv_cancel_right] at this
          exact this)
        rw [hβ, Set.indicator_of_notMem hmem, Set.indicator_of_notMem hp, zero_mul]
    rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_mul_const,
      D.integral_indicator_PK_mul_right]
    have := hφP ⟨q, hq⟩ k₀
    rw [show ((⟨q, hq⟩ : ↥D.P) : ↥d.G) = q from rfl] at this
    rw [this]
    ring
  obtain ⟨c, hc, hformula⟩ := integral_eq_mul_integral_compact_integral (G := ↥d.G) D.P D.K
    (d.isClosed_whittB D.FW D.FV) D.mul_eq
  have hβg : Continuous fun x => β (x * g) := hβc.comp (continuous_id.mul continuous_const)
  have hβgs : HasCompactSupport fun x => β (x * g) := hβs.comp_homeomorph (Homeomorph.mulRight g)
  have h1 := hformula _ hβg hβgs
  have h2 := hformula _ hβc hβs
  rw [integral_mul_right_eq_self β g] at h1
  have e1 : ∀ k : ↥D.K, ∫ p : ↥D.P, β ((p : ↥d.G) * (k : ↥d.G) * g)
      ∂(Measure.haar : Measure ↥D.P) = (mS : ℂ) * φ ((k : ↥d.G) * g) := fun k => by
    simp only [mul_assoc]
    exact hfib _
  have e2 : ∀ k : ↥D.K, ∫ p : ↥D.P, β ((p : ↥d.G) * (k : ↥d.G))
      ∂(Measure.haar : Measure ↥D.P) = (mS : ℂ) * φ k := fun k => hfib _
  rw [integral_congr_ae (Filter.Eventually.of_forall e1), integral_const_mul] at h1
  rw [integral_congr_ae (Filter.Eventually.of_forall e2), integral_const_mul] at h2
  have hne : (c : ℂ) * (mS : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 hc.ne') (Complex.ofReal_ne_zero.2 D.haar_real_PK_pos.ne')
  apply mul_left_cancel₀ hne
  calc (c : ℂ) * mS * ∫ k : ↥D.K, φ ((k : ↥d.G) * g) ∂(Measure.haar : Measure ↥D.K)
      = (c : ℂ) * (mS * ∫ k : ↥D.K, φ ((k : ↥d.G) * g) ∂(Measure.haar : Measure ↥D.K)) := by ring
    _ = (c : ℂ) * (mS * ∫ k : ↥D.K, φ k ∂(Measure.haar : Measure ↥D.K)) := h1.symm.trans h2
    _ = (c : ℂ) * mS * ∫ k : ↥D.K, φ k ∂(Measure.haar : Measure ↥D.K) := by ring

/-- **Normalized parabolic induction is unitary** (Bernstein–Zelevinsky 1977 §2; Casselman,
*Introduction to the theory of admissible representations*, Prop. 3.1.2 (number unverified)):
for `G(F) = P(F) K` and `f(pg) = δ_P(p)^{1/2} σ(p) f(g)`, the form `∫_K ⟨f₁(k), f₂(k)⟩ dk` is
invariant under right translation.  This is where the normalization by `δ_P^{1/2}` (with
`δ_P` the modular character in the convention `μ(E p⁻¹) = δ_P(p) μ(E)`, so that
`δ_P(p) = |det Ad(p)|_{𝔲}|`) and `G = PK` enter.

Convention check (as for `IwasawaDatum.deltaP0`): for `P = F^× ⋉ F`, `(a, x)(b, y) = (ab, x + ay)`,
the left Haar measure is `|a|⁻¹ d^×a dx` and `μ(E p⁻¹) = |b| μ(E)` for `p = (b, y)`, i.e.
`δ_P(b, y) = |b| = |det Ad(p)|_𝔲|`, the normalization for which `δ_P^{1/2}` makes the induction
unitary.  Status: proved from `integral_K_mul_right` (the integration formula for `G = P K`,
literature axiom `integral_eq_mul_integral_compact_integral`, and the unimodularity of `G(F)`,
axiom `haar_G_isMulRightInvariant`); the convention for `δ_P` is the one for which the proof
goes through, so no convention is assumed. -/
theorem preInner_rightTrans (g : ↥d.G) (f₁ f₂ : D.Pre) :
    D.preInner (D.rightTransLin g f₁) (D.rightTransLin g f₂) = D.preInner f₁ f₂ := by
  have hc₁ := D.continuous_of_mem_smoothSpace (D.toFun_mem f₁)
  have hc₂ := D.continuous_of_mem_smoothSpace (D.toFun_mem f₂)
  exact D.integral_K_mul_right (φ := fun x => inner ℂ (D.toFun f₁ x) (D.toFun f₂ x))
    (hc₁.inner hc₂) (fun p x => D.inner_toFun_mul f₁ f₂ p x) g

theorem norm_rightTransLin (g : ↥d.G) (f : D.Pre) : ‖D.rightTransLin g f‖ = ‖f‖ := by
  rw [norm_def, norm_def, preInner_rightTrans]

/-- `R_g` as a continuous linear map (an isometry). -/
def rightTransCLM (g : ↥d.G) : D.Pre →L[ℂ] D.Pre :=
  (D.rightTransLin g).mkContinuous 1 fun f => by rw [one_mul, norm_rightTransLin]

theorem rightTransCLM_apply (g : ↥d.G) (f : D.Pre) :
    D.rightTransCLM g f = D.rightTransLin g f := rfl

theorem rightTransLin_one (f : D.Pre) : D.rightTransLin 1 f = f := by
  apply Subtype.ext
  funext x
  exact congrArg (D.toFun f) (mul_one x)

theorem rightTransLin_mul (g h : ↥d.G) (f : D.Pre) :
    D.rightTransLin (g * h) f = D.rightTransLin g (D.rightTransLin h f) := by
  apply Subtype.ext
  funext x
  exact congrArg (D.toFun f) (mul_assoc x g h).symm

/-- The Hilbert space of `i_P^G(σ)`: the completion of the smooth induced space. -/
abbrev Hil : Type := UniformSpace.Completion D.Pre

/-- The action of `g` on `i_P^G(σ)`. -/
def rho (g : ↥d.G) : D.Hil →L[ℂ] D.Hil := (D.rightTransCLM g).completion

theorem rho_coe (g : ↥d.G) (f : D.Pre) :
    D.rho g (f : D.Hil) = ((D.rightTransLin g f : D.Pre) : D.Hil) := by
  rw [rho, ContinuousLinearMap.completion_apply_coe, rightTransCLM_apply]

theorem rho_ext {A B : D.Hil →L[ℂ] D.Hil} (h : ∀ f : D.Pre, A (f : D.Hil) = B (f : D.Hil)) :
    A = B := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq A.continuous B.continuous
  | ih f => exact h f

theorem rho_one : D.rho 1 = 1 :=
  D.rho_ext fun f => by rw [rho_coe, rightTransLin_one]; rfl

theorem rho_mul (g h : ↥d.G) : D.rho (g * h) = D.rho g * D.rho h :=
  D.rho_ext fun f => by
    change D.rho (g * h) f = D.rho g (D.rho h f)
    rw [rho_coe, rho_coe, rho_coe, rightTransLin_mul]

theorem inner_rho (g : ↥d.G) (x y : D.Hil) : inner ℂ (D.rho g x) (D.rho g y) = inner ℂ x y := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp =>
    exact isClosed_eq (((D.rho g).continuous.comp _root_.continuous_fst).inner
      ((D.rho g).continuous.comp _root_.continuous_snd))
      (_root_.continuous_fst.inner _root_.continuous_snd)
  | ih f₁ f₂ =>
    rw [rho_coe, rho_coe, UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe,
      inner_def, inner_def, preInner_rightTrans]

theorem rho_mem_unitary (g : ↥d.G) : D.rho g ∈ unitary (D.Hil →L[ℂ] D.Hil) := by
  have hstar : star (D.rho g) * D.rho g = 1 := by
    ext x
    refine ext_inner_left ℂ fun y => ?_
    change inner ℂ y (star (D.rho g) (D.rho g x)) = inner ℂ y x
    rw [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, inner_rho]
  have hinv : D.rho g * D.rho g⁻¹ = 1 := by rw [← rho_mul, mul_inv_cancel, rho_one]
  have hs : star (D.rho g) = D.rho g⁻¹ := by
    calc star (D.rho g) = star (D.rho g) * (D.rho g * D.rho g⁻¹) := by rw [hinv, mul_one]
      _ = D.rho g⁻¹ := by rw [← mul_assoc, hstar, one_mul]
  exact Unitary.mem_iff.2 ⟨hstar, by rw [hs, hinv]⟩

/-- Each `ρ(g)` is an isometry of `i_P^G(σ)`. -/
theorem norm_rho_apply (g : ↥d.G) (v : D.Hil) : ‖D.rho g v‖ = ‖v‖ := by
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, inner_rho]

/-- On a smooth vector `f`, `g ↦ ρ(g) f` is locally constant: `f` is right invariant under an
open subgroup `K'`, so `ρ(g k) f = ρ(g) f` for `k ∈ K'`. -/
theorem continuous_rho_coe (f : D.Pre) : Continuous fun g : ↥d.G => D.rho g (f : D.Hil) := by
  obtain ⟨-, K', hK', i⟩ := D.toFun_mem f
  have hfix : ∀ k ∈ K', D.rightTransLin k f = f := fun k hk => by
    apply Subtype.ext
    funext x
    exact i x k hk
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hmem : {x : ↥d.G | g⁻¹ * x ∈ K'} ∈ 𝓝 g := by
    refine (hK'.preimage (continuous_const.mul continuous_id)).mem_nhds ?_
    simp [K'.one_mem]
  refine (continuousAt_const (y := D.rho g (f : D.Hil))).congr
    (Filter.eventually_of_mem hmem fun x hx => ?_)
  show D.rho g (f : D.Hil) = D.rho x (f : D.Hil)
  have e : x = g * (g⁻¹ * x) := (mul_inv_cancel_left g x).symm
  have h2 : D.rho (g⁻¹ * x) (f : D.Hil) = (f : D.Hil) := by
    rw [rho_coe, hfix _ hx]
  calc D.rho g (f : D.Hil) = D.rho g (D.rho (g⁻¹ * x) (f : D.Hil)) := by rw [h2]
    _ = D.rho (g * (g⁻¹ * x)) (f : D.Hil) := by rw [D.rho_mul g (g⁻¹ * x)]; rfl
    _ = D.rho x (f : D.Hil) := by rw [← e]

/-- **Strong continuity** of `i_P^G(σ)`: `g ↦ ρ(g) v` is continuous.  On smooth vectors it is
locally constant (`f` is right-invariant under an open subgroup); the general case follows by
density, the `ρ(g)` being isometries.  Status: proved (modulo `preInner_rightTrans`, through
the isometry property). -/
theorem continuous_rho_apply (v : D.Hil) : Continuous fun g : ↥d.G => D.rho g v := by
  induction v using UniformSpace.Completion.induction_on with
  | hp =>
    refine isClosed_of_closure_subset fun v hv => ?_
    refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
    obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
    obtain ⟨w, hw, hvw⟩ := Metric.mem_closure_iff.1 hv ε hε
    refine ⟨fun g => D.rho g w, hw, fun g => hεu ?_⟩
    rw [dist_eq_norm, ← map_sub, D.norm_rho_apply, ← dist_eq_norm]
    exact hvw
  | ih f => exact D.continuous_rho_coe f

end ParIndData

/-- **Normalized parabolic induction** `i_P^G(σ)` (BZ 1977 §2; BP §1.5; Thesis §3.2): the
completion of the space of smooth `f : G(F) → H_σ` with `f(pg) = δ_P(p)^{1/2} σ(p) f(g)`, for the
norm `‖f‖² = ∫_K ‖f(k)‖² dk`, with `G(F)` acting by right translation. -/
def parInd (D : d.ParIndData) : UnitaryRep ↥d.G where
  H := D.Hil
  ρ := { toFun := D.rho, map_one' := D.rho_one, map_mul' := D.rho_mul }
  unitary_ρ := D.rho_mem_unitary
  strongCont := D.continuous_rho_apply

/-! ## 7. Properly induced virtual representations `R_ind(G, η)` (BP §2.7; Thesis §3.4, §7.4) -/

/-- `i_P^G(σ)` is **properly induced from a tempered representation with central character `η`**
(BP §2.7; Thesis §7.4, proof of Prop 7.4.1(i): "`π = i_Q^G(σ)`, `Q` proper, `σ ∈ Temp(L, χ)`"):
`P` is proper, `σ` is irreducible tempered on `M = P/U`, and `A_G(F) ⊆ P(F)` acts through `σ` by
`η`.  (`A_G ⊆ P` holds for every parabolic subgroup; it is recorded as a field, as in
`IwasawaDatum.AG_le_P0`.) -/
structure IsTempIndData (η : CentralCharOn d) (D : d.ParIndData) : Prop where
  proper : d.IsProperFlagPair D.FW D.FV
  tempered : IsTempered D.σ
  AG_le : d.AG ≤ D.P
  centralChar : ∀ a : ↥d.AG,
    D.σ.ρ (QuotientGroup.mk (⟨(a : ↥d.G), AG_le a.2⟩ : ↥D.P)) = ((η.toHom a : Circle) : ℂ) • 1

/-- **`R_ind(G, η)`, the properly induced virtual representations** (BP §2.7; Thesis §7.4):
the span of the virtual tempered representations whose character is, on `G_reg(F)`, the character
of some `i_P^G(σ)` with `P` proper and `σ` tempered with central character `η`.  Stated at the level
of characters: the virtual representation *equal* to `i_P^G(σ)` in `R_temp(G, η)` is the one with
the same character (Harish-Chandra's linear independence of characters; it exists since
`i_P^G(σ)` has finite length with tempered constituents).  Real definition, no axiom. -/
def Rind (η : CentralCharOn d) : Submodule ℂ (VirtualTemp d η) :=
  Submodule.span ℂ {P | ∃ D : d.ParIndData, d.IsTempIndData η D ∧
    Set.EqOn (vChar d P) (charG d (d.parInd D)) (regularSet d.G d.lie)}

theorem subset_Rind {η : CentralCharOn d} {P : VirtualTemp d η} {D : d.ParIndData}
    (hD : d.IsTempIndData η D)
    (hP : Set.EqOn (vChar d P) (charG d (d.parInd D)) (regularSet d.G d.lie)) :
    P ∈ d.Rind η :=
  Submodule.subset_span ⟨D, hD, hP⟩

end GGPData

end GSpinGGP
