/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.CentralizerTransport
import GSpinGGP.TraceFormula.TorusDescent

/-!
# Transfer of germs to inner forms

Strongly stably conjugate semisimple `x ∈ GSpin(W)(F)`, `y ∈ GSpin(W_α)(F)` have isomorphic descent
data (`exists_centralizerIso_of_stronglyStablyConjW`, Thesis §6.1), so the local expansions of a
quasi-character and of its transfer correspond (`bp_germAvg_transfer`, `bp_germ_transfer`, Thesis
(6.1.2)).
-/

open Topology Filter

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

open TorusTransfer HarishChandra

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- The trace form on `A × B` is the sum of the trace forms. -/
theorem trace_mulLeft_prod {A B : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [Ring B]
    [Algebra F B] [Module.Finite F B] (a : A × B) :
    LinearMap.trace F (A × B) (LinearMap.mulLeft F a) =
      LinearMap.trace F A (LinearMap.mulLeft F a.1) +
        LinearMap.trace F B (LinearMap.mulLeft F a.2) := by
  rw [← LinearMap.trace_prodMap']
  rfl

set_option maxHeartbeats 1000000 in
-- One proof assembling both Clifford factors; the default budget is exceeded.
/-- **Strongly stably conjugate elements have isomorphic descent data** (Thesis §6.1). Let
`x ∈ GSpin(W)(F)`, `y ∈ GSpin(W_α)(F)` be semisimple and strongly stably conjugate (`hxy`): there is
`g ∈ G_α(F̄)` with `y = g ψ_α(x) g⁻¹` such that `ι = Ad(g) ∘ ψ_α : G_x ≃ G_{α,y}` is defined over
`F` (`ψ_α = C(φ) × C(φ ⊕ id_Z)`; `x`, `y` embedded diagonally). Then `ι` induces an isomorphism of
descent data `CentralizerIso` at `x` and `y`, and for `X ∈ 𝔤_x(F)` small and regular the elements
`x e^X ∈ G_reg(F)` and `y e^{ι X} ∈ G_{α,reg}(F)` are stably conjugate (through `ψ_α`, by the same
`g`).

Proof. Let `Φ : a ↦ g ψ_α(a) g⁻¹` on each Clifford factor, base changed to `F̄`, and let `R ⊆ A`
be the subalgebra of the `a` with `Φ(ā)` rational (`TorusTransfer.ratSub`); `lin` is
`a ↦ Φ(ā)` on `R`, extended `F`-linearly (`TorusTransfer.transL`), an algebra isomorphism from `R`
onto the corresponding subalgebra for `Φ⁻¹`. The Galois condition puts `G_x(F)` in `R` and maps it
onto `G_{α,y}(F)` (`TorusTransfer.exists_transport`). For `X ∈ 𝔤_x(F)` and `c ≠ 0` small,
`e^{cX} ∈ G_x(F)`, so `cX ∈ R` (a subalgebra containing `e^{cX}` contains `cX`,
`exists_nhds_mem_of_expA_mem`) and `e^{c lin X} = lin(e^{cX}) ∈ G_{α,y}(F)` gives
`lin X ∈ 𝔤_{α,y}(F)` (`TorusTransfer.mem_ratSub_of_mem_gspin`). `Φ` preserves the trace forms
`tr(L_{XY})` (computed over `F̄`, `TorusTransfer.trace_mulLeft_transL`). The fields of
`CentralizerIso` follow (`CentralizerIso.ofSubalgebra`). For `X ∈ 𝔤_x(F)` small, `e^X ∈ G(F)`
(`eventually_expA_mem_G`), `x e^X` is regular when `X` is regular in `𝔤_x`, and likewise
`y e^{ι X}` (`exists_nhds_isRegularSS_mul_expA`); and `g ψ_α(x e^X) g⁻¹ = y e^{ι X}`.

**Status: proved** (transport along `ι`, defined in Thesis §6.1; this argument is not in the
thesis). -/
theorem exists_centralizerIso_of_stronglyStablyConjW (d : GGPData F) (τ : InnerTwist d.QW)
    (x : GSpin d.QW) (y : GSpin (d.twist τ).QW)
    (hx : IsSS F (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient))
    (hy : IsSS F ((((d.twist τ).diag y : ↥(d.twist τ).G) : (d.twist τ).ambientˣ) :
      (d.twist τ).ambient))
    (hxy : d.StronglyStablyConjW τ x y) :
    ∃ ι : CentralizerIso d.G d.lie d.bilin (d.twist τ).G (d.twist τ).lie (d.twist τ).bilin
        ((d.diag x : ↥d.G) : d.ambientˣ) (((d.twist τ).diag y : ↥(d.twist τ).G) :
          (d.twist τ).ambientˣ),
      ∃ ω ∈ 𝓝 (0 : d.ambient), ∀ X ∈ ω,
        X ∈ lieCentralizer d.lie (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient) →
        IsRegularSS (lieCentralizer d.lie (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient)) X →
        ∀ y' : ↥(d.twist τ).G, ((y' : (d.twist τ).ambientˣ) : (d.twist τ).ambient) =
            ((((d.twist τ).diag y : ↥(d.twist τ).G) : (d.twist τ).ambientˣ) :
              (d.twist τ).ambient) * expA F (ι.lin X) →
          ∃ z : ↥d.G, ((z : d.ambientˣ) : d.ambient) =
              (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient) * expA F X ∧
            z ∈ regularSet d.G d.lie ∧ y' ∈ regularSet (d.twist τ).G (d.twist τ).lie ∧
            d.StablyConjG τ z y' := by
  obtain ⟨U₁, hU₁, hreg₁⟩ := exists_nhds_isRegularSS_mul_expA F d.lie hx (Units.isUnit _)
  obtain ⟨U₂, hU₂, hreg₂⟩ := exists_nhds_isRegularSS_mul_expA F (d.twist τ).lie hy (Units.isUnit _)
  have hexpG := eventually_expA_mem_G d
  obtain ⟨⟨gW, hgW, hcW, hrW⟩, ⟨gV, hgV, hcV, hrV⟩⟩ := hxy
  let d' := d.twist τ
  let xW : GSpin d.QW := d.fst (d.diag x)
  let xV : GSpin d.QV := d.snd (d.diag x)
  let yW : GSpin d'.QW := d'.fst (d'.diag y)
  let yV : GSpin d'.QV := d'.snd (d'.diag y)
  let φW := τ.φ
  let φV := d.twistV τ
  let gW' := cliffUnits φW.symm gW⁻¹
  let gV' := cliffUnits φV.symm gV⁻¹
  have hrW' : RatAt φW.symm gW' ((yW : _) : (CliffordAlgebra d'.QW)ˣ) := ratAt_symm hgW hrW hcW
  have hrV' : RatAt φV.symm gV' ((yV : _) : (CliffordAlgebra d'.QV)ˣ) := ratAt_symm hgV hrV hcV
  have hgW' : gW' ∈ GSpin _ := cliffUnits_mem_GSpin φW.symm ((GSpin _).inv_mem hgW)
  have hgV' : gV' ∈ GSpin _ := cliffUnits_mem_GSpin φV.symm ((GSpin _).inv_mem hgV)
  have hcW₀ : psiA φW gW (bcHom d.QW ((xW : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) =
      bcHom d'.QW ((yW : (CliffordAlgebra d'.QW)ˣ) : CliffordAlgebra d'.QW) :=
    congrArg Units.val hcW
  have hcV₀ : psiA φV gV (bcHom d.QV ((xV : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) =
      bcHom d'.QV ((yV : (CliffordAlgebra d'.QV)ˣ) : CliffordAlgebra d'.QV) :=
    congrArg Units.val hcV
  have hcW₁ : psiA φW.symm gW' (bcHom d'.QW ((yW : (CliffordAlgebra d'.QW)ˣ) :
      CliffordAlgebra d'.QW)) =
        bcHom d.QW ((xW : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) := by
    rw [← hcW₀, psiA_symm_psiA]
  have hcV₁ : psiA φV.symm gV' (bcHom d'.QV ((yV : (CliffordAlgebra d'.QV)ˣ) :
      CliffordAlgebra d'.QV)) =
        bcHom d.QV ((xV : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) := by
    rw [← hcV₀, psiA_symm_psiA]
  have hW := psiA_symm_psiA φW gW
  have hW' := psiA_psiA_symm φW gW
  have hV := psiA_symm_psiA φV gV
  have hV' := psiA_psiA_symm φV gV
  let S : Subalgebra F d.ambient := (ratSub φW gW).prod (ratSub φV gV)
  let S' : Subalgebra F d'.ambient := (ratSub φW.symm gW').prod (ratSub φV.symm gV')
  let f : d.ambient →ₗ[F] d'.ambient := (transL φW gW).prodMap (transL φV gV)
  let f' : d'.ambient →ₗ[F] d.ambient := (transL φW.symm gW').prodMap (transL φV.symm gV')
  have hfS : ∀ a ∈ S, f a ∈ S' := fun a ha =>
    ⟨transL_mem_ratSub hW ha.1, transL_mem_ratSub hV ha.2⟩
  have hf'S : ∀ a ∈ S', f' a ∈ S := fun a ha =>
    ⟨transL_mem_ratSub hW' ha.1, transL_mem_ratSub hV' ha.2⟩
  have hone : f 1 = 1 := Prod.ext transL_one transL_one
  have hmul : ∀ a ∈ S, ∀ c ∈ S, f (a * c) = f a * f c := fun a ha c hc =>
    Prod.ext (transL_mul ha.1 hc.1) (transL_mul ha.2 hc.2)
  have hinv : ∀ a ∈ S, f' (f a) = a := fun a ha =>
    Prod.ext (transL_transL hW ha.1) (transL_transL hV ha.2)
  have hinv' : ∀ a ∈ S', f (f' a) = a := fun a ha =>
    Prod.ext (transL_transL hW' ha.1) (transL_transL hV' ha.2)
  -- the Lie algebras
  have hlie : ∀ X ∈ lieCentralizer d.lie (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient),
      X ∈ S ∧ f X ∈ lieCentralizer d'.lie (((d'.diag y : ↥d'.G) : d'.ambientˣ) : d'.ambient) := by
    intro X hX
    obtain ⟨⟨h1, h2⟩, hc⟩ := mem_lieCentralizer.mp hX
    have hc1 : X.1 * ((xW : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) =
        ((xW : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X.1 := (congrArg Prod.fst hc).symm
    have hc2 : X.2 * ((xV : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) =
        ((xV : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) * X.2 := (congrArg Prod.snd hc).symm
    obtain ⟨m1, g1⟩ := mem_ratSub_of_mem_gspin hgW hrW h1 hc1
    obtain ⟨m2, g2⟩ := mem_ratSub_of_mem_gspin hgV hrV h2 hc2
    exact ⟨⟨m1, m2⟩, mem_lieCentralizer.mpr ⟨⟨g1, g2⟩, Prod.ext
      (transL_mul_comm hgW hrW hcW₀ m1 hc1).symm (transL_mul_comm hgV hrV hcV₀ m2 hc2).symm⟩⟩
  have hlie' : ∀ X ∈ lieCentralizer d'.lie (((d'.diag y : ↥d'.G) : d'.ambientˣ) : d'.ambient),
      X ∈ S' ∧ f' X ∈ lieCentralizer d.lie (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient) := by
    intro X hX
    obtain ⟨⟨h1, h2⟩, hc⟩ := mem_lieCentralizer.mp hX
    have hc1 : X.1 * ((yW : (CliffordAlgebra d'.QW)ˣ) : CliffordAlgebra d'.QW) =
        ((yW : (CliffordAlgebra d'.QW)ˣ) : CliffordAlgebra d'.QW) * X.1 :=
      (congrArg Prod.fst hc).symm
    have hc2 : X.2 * ((yV : (CliffordAlgebra d'.QV)ˣ) : CliffordAlgebra d'.QV) =
        ((yV : (CliffordAlgebra d'.QV)ˣ) : CliffordAlgebra d'.QV) * X.2 :=
      (congrArg Prod.snd hc).symm
    obtain ⟨m1, g1⟩ := mem_ratSub_of_mem_gspin hgW' hrW' h1 hc1
    obtain ⟨m2, g2⟩ := mem_ratSub_of_mem_gspin hgV' hrV' h2 hc2
    exact ⟨⟨m1, m2⟩, mem_lieCentralizer.mpr ⟨⟨g1, g2⟩, Prod.ext
      (transL_mul_comm hgW' hrW' hcW₁ m1 hc1).symm (transL_mul_comm hgV' hrV' hcV₁ m2 hc2).symm⟩⟩
  -- the groups
  have hgrp : ∀ u ∈ grpCentralizer d.G ((d.diag x : ↥d.G) : d.ambientˣ), (u : d.ambient) ∈ S ∧
      ∀ v : d'.ambientˣ, (v : d'.ambient) = f u →
        v ∈ grpCentralizer d'.G ((d'.diag y : ↥d'.G) : d'.ambientˣ) := by
    rintro u ⟨huG, huc⟩
    have hc : u * ((d.diag x : ↥d.G) : d.ambientˣ) = ((d.diag x : ↥d.G) : d.ambientˣ) * u :=
      (Subgroup.mem_centralizer_iff.mp huc _ rfl).symm
    have hc' := congrArg Units.val hc
    rw [Units.val_mul, Units.val_mul] at hc'
    have huG' := Subgroup.mem_prod.mp (Subgroup.mem_comap.mp huG)
    let t₁ : GSpin d.QW := ⟨(MulEquiv.prodUnits u).1, huG'.1⟩
    let t₂ : GSpin d.QV := ⟨(MulEquiv.prodUnits u).2, huG'.2⟩
    have hc1 : (u : d.ambient).1 * ((xW : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) =
        ((xW : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * (u : d.ambient).1 :=
      congrArg Prod.fst hc'
    have hc2 : (u : d.ambient).2 * ((xV : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) =
        ((xV : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) * (u : d.ambient).2 :=
      congrArg Prod.snd hc'
    obtain ⟨m1, b1, hb1⟩ := exists_transL_eq_of_commute hgW hrW t₁ (Units.ext hc1)
    obtain ⟨m2, b2, hb2⟩ := exists_transL_eq_of_commute hgV hrV t₂ (Units.ext hc2)
    refine ⟨⟨m1, m2⟩, fun v hv => ⟨?_, ?_⟩⟩
    · refine Subgroup.mem_comap.mpr (Subgroup.mem_prod.mpr ⟨?_, ?_⟩)
      · have : (MulEquiv.prodUnits v).1 = (b1 : (CliffordAlgebra d'.QW)ˣ) :=
          Units.ext ((congrArg Prod.fst hv).trans hb1.symm)
        rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, this]
        exact b1.2
      · have : (MulEquiv.prodUnits v).2 = (b2 : (CliffordAlgebra d'.QV)ˣ) :=
          Units.ext ((congrArg Prod.snd hv).trans hb2.symm)
        rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, this]
        exact b2.2
    · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff.mp hh]
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul, hv]
      exact Prod.ext (transL_mul_comm hgW hrW hcW₀ m1 hc1).symm
        (transL_mul_comm hgV hrV hcV₀ m2 hc2).symm
  have hgrp' : ∀ v ∈ grpCentralizer d'.G ((d'.diag y : ↥d'.G) : d'.ambientˣ),
      (v : d'.ambient) ∈ S' ∧
      ∀ u : d.ambientˣ, (u : d.ambient) = f' v →
        u ∈ grpCentralizer d.G ((d.diag x : ↥d.G) : d.ambientˣ) := by
    rintro u ⟨huG, huc⟩
    have hc : u * ((d'.diag y : ↥d'.G) : d'.ambientˣ) = ((d'.diag y : ↥d'.G) : d'.ambientˣ) * u :=
      (Subgroup.mem_centralizer_iff.mp huc _ rfl).symm
    have hc' := congrArg Units.val hc
    rw [Units.val_mul, Units.val_mul] at hc'
    have huG' := Subgroup.mem_prod.mp (Subgroup.mem_comap.mp huG)
    let t₁ : GSpin d'.QW := ⟨(MulEquiv.prodUnits u).1, huG'.1⟩
    let t₂ : GSpin d'.QV := ⟨(MulEquiv.prodUnits u).2, huG'.2⟩
    have hc1 : (u : d'.ambient).1 * ((yW : (CliffordAlgebra d'.QW)ˣ) : CliffordAlgebra d'.QW) =
        ((yW : (CliffordAlgebra d'.QW)ˣ) : CliffordAlgebra d'.QW) * (u : d'.ambient).1 :=
      congrArg Prod.fst hc'
    have hc2 : (u : d'.ambient).2 * ((yV : (CliffordAlgebra d'.QV)ˣ) : CliffordAlgebra d'.QV) =
        ((yV : (CliffordAlgebra d'.QV)ˣ) : CliffordAlgebra d'.QV) * (u : d'.ambient).2 :=
      congrArg Prod.snd hc'
    obtain ⟨m1, b1, hb1⟩ := exists_transL_eq_of_commute hgW' hrW' t₁ (Units.ext hc1)
    obtain ⟨m2, b2, hb2⟩ := exists_transL_eq_of_commute hgV' hrV' t₂ (Units.ext hc2)
    refine ⟨⟨m1, m2⟩, fun v hv => ⟨?_, ?_⟩⟩
    · refine Subgroup.mem_comap.mpr (Subgroup.mem_prod.mpr ⟨?_, ?_⟩)
      · have : (MulEquiv.prodUnits v).1 = (b1 : (CliffordAlgebra d.QW)ˣ) :=
          Units.ext ((congrArg Prod.fst hv).trans hb1.symm)
        rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, this]
        exact b1.2
      · have : (MulEquiv.prodUnits v).2 = (b2 : (CliffordAlgebra d.QV)ˣ) :=
          Units.ext ((congrArg Prod.snd hv).trans hb2.symm)
        rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, this]
        exact b2.2
    · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff.mp hh]
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul, hv]
      exact Prod.ext (transL_mul_comm hgW' hrW' hcW₁ m1 hc1).symm
        (transL_mul_comm hgV' hrV' hcV₁ m2 hc2).symm
  -- the forms
  have hb : ∀ X ∈ lieCentralizer d.lie (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient),
      ∀ Y ∈ lieCentralizer d.lie (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient),
        d'.bilin (f X) (f Y) = d.bilin X Y := by
    intro X hX Y hY
    have hXY : X * Y ∈ S := S.mul_mem (hlie X hX).1 (hlie Y hY).1
    rw [GGPData.bilin_apply, GGPData.bilin_apply, ← hmul _ (hlie X hX).1 _ (hlie Y hY).1,
      trace_mulLeft_prod, trace_mulLeft_prod]
    exact congrArg₂ (· + ·) (trace_mulLeft_transL hXY.1) (trace_mulLeft_transL hXY.2)
  let ι : CentralizerIso d.G d.lie d.bilin d'.G d'.lie d'.bilin
      ((d.diag x : ↥d.G) : d.ambientˣ) ((d'.diag y : ↥d'.G) : d'.ambientˣ) :=
    CentralizerIso.ofSubalgebra S S' f f' hfS hf'S hone hmul hinv hinv'
      (fun X hX => (hlie X hX).1) (fun X hX => (hlie' X hX).1) (fun X hX => (hlie X hX).2)
      (fun X hX => (hlie' X hX).2) (fun u hu => (hgrp u hu).1) (fun v hv => (hgrp' v hv).1)
      (fun u hu => (hgrp u hu).2) (fun v hv => (hgrp' v hv).2) hb
  refine ⟨ι, ?_⟩
  -- the local statement
  have hfc : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have hU₂' : f ⁻¹' U₂ ∈ 𝓝 (0 : d.ambient) :=
    hfc.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hU₂)
  refine ⟨U₁ ∩ f ⁻¹' U₂ ∩ {X | X ∈ d.lie → ∃ e : ↥d.G, ((e : d.ambientˣ) : d.ambient) = expA F X},
    inter_mem (inter_mem hU₁ hU₂') hexpG, ?_⟩
  rintro X ⟨⟨hX₁, hX₂⟩, hX₃⟩ hXc hXr y' hy'
  have hXS : X ∈ S := (hlie X hXc).1
  obtain ⟨e, he⟩ := hX₃ (mem_lieCentralizer.mp hXc).1
  have hfexp : f (expA F X) = expA F (f X) :=
    map_expA_of_leftInverse f f' (map_pow_of_mul hone hmul hXS) (fun n => hinv _ (S.pow_mem hXS n))
  have heS : expA F X ∈ S := expA_mem_subalgebra S hXS
  have hιX : ι.lin X = f X := rfl
  refine ⟨d.diag x * e, by rw [Subgroup.coe_mul, Units.val_mul, he], ?_, ?_, ?_⟩
  · change IsRegularSS d.lie _
    rw [Subgroup.coe_mul, Units.val_mul, he]
    exact hreg₁ X hX₁ hXc hXr
  · change IsRegularSS d'.lie _
    rw [hy', hιX]
    exact hreg₂ (f X) hX₂ (ι.bijOn.mapsTo hXc) ((ι.isRegularSS_iff X hXc).mpr hXr)
  · have hy'' : ((y' : d'.ambientˣ) : d'.ambient) =
        (((d'.diag y : ↥d'.G) : d'.ambientˣ) : d'.ambient) * f (expA F X) := by
      rw [hy', hιX, hfexp]
    refine ⟨⟨gW, hgW, Units.ext ?_⟩, ⟨gV, hgV, Units.ext ?_⟩⟩
    · change psiA φW gW (bcHom d.QW
        ((((d.diag x * e : ↥d.G) : d.ambientˣ) : d.ambient)).1) =
          bcHom d'.QW (((y' : d'.ambientˣ) : d'.ambient)).1
      rw [hy'', Subgroup.coe_mul, Units.val_mul, he, Prod.fst_mul, Prod.fst_mul, map_mul, psiA_mul,
        map_mul]
      exact congrArg₂ (· * ·) hcW₀ (bcHom_transL heS.1).symm
    · change psiA φV gV (bcHom d.QV
        ((((d.diag x * e : ↥d.G) : d.ambientˣ) : d.ambient)).2) =
          bcHom d'.QV (((y' : d'.ambientˣ) : d'.ambient)).2
      rw [hy'', Subgroup.coe_mul, Units.val_mul, he, Prod.snd_mul, Prod.snd_mul, map_mul, psiA_mul,
        map_mul]
      exact congrArg₂ (· * ·) hcV₀ (bcHom_transL heS.2).symm

set_option linter.unusedVariables false in
/-- **Beuzart-Plessis (12.1.2), averaged form, for the inner twists of `GSpin`** (Thesis (6.1.2)).
Let `G` be quasi-split, `τ` an inner twist (`G_α = (d.twist τ).G`), `θ` a stable quasi-character on
`G(F)` and `θ'` a stable quasi-character on `G_α(F)` which is a transfer of `θ`: `θ'(y) = θ(x)`
whenever `x ∈ G_reg(F)`, `y ∈ G_{α,reg}(F)` are stably conjugate through `ψ_α = C(φ) × C(φ ⊕
id_Z)`. Then for `x ∈ GSpin(W)(F)`, `y ∈ GSpin(W_α)(F)` semisimple and strongly stably conjugate
(embedded diagonally), `c_{θ'}(y) = c_θ(x)`, where `c_θ(x) = |Nil_reg(𝔤_x)|⁻¹ Σ_{O ∈ Nil_reg(𝔤_x)}
c_{θ,O}(x)` (`germAvg`).

Source: Beuzart-Plessis, Astérisque 418 (2020), (12.1.2), p. 260, stated for a connected reductive
`G` and its *pure* inner forms. The inner forms here have cocycles valued in `SO(W) × SO(V)`, and
those with the other Hasse invariant are not pure inner forms of `GSpin(W) × GSpin(V)`. The proof
here does not use purity, nor the limit formula BP Prop 4.5.1 1.(ii) used in BP's and the thesis's
proofs: the `F`-isomorphism `ι = Ad(g) ∘ ψ_α : G_x ≃ G_{α,y}` is an isomorphism of descent data
(`exists_centralizerIso_of_stronglyStablyConjW`), `x e^X` and `y e^{ι X}` are stably conjugate for
`X ∈ 𝔤_x(F)` small and regular, so `θ'(y e^{ι X}) = θ(x e^X)`, and the local expansions correspond
orbit by orbit (`germAvg_eq_of_centralizerIso`). Stability and transfer are written out inline;
`hqs`, `hθ'` and the stability hypotheses are not needed by this argument. Only diagonal elements
are needed (Thesis §6.7).

**Status: proved** from `exists_centralizerIso_of_stronglyStablyConjW` and `jHat_centralizerIso`. -/
theorem bp_germAvg_transfer (d : GGPData F) (hqs : d.IsQuasiSplit) (ψ : NontrivialAddChar F)
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
    germAvg (d.twist τ).G (d.twist τ).lie (d.twist τ).bilin ψ θ' ((d.twist τ).diag y) =
      germAvg d.G d.lie d.bilin ψ θ (d.diag x) := by
  obtain ⟨ι, ω, hω, hloc⟩ := exists_centralizerIso_of_stronglyStablyConjW d τ x y hx hy hxy
  refine germAvg_eq_of_centralizerIso d (d.twist τ) ψ θ θ' hθ _ _ hx hy ι
    ⟨ω, hω, fun X hXω hX hXr y' hy' => ?_⟩
  obtain ⟨z, hz, hzr, hy'r, hst⟩ := hloc X hXω hX hXr y' hy'
  exact ⟨z, hz, htrans z hzr y' hy'r hst⟩

/-- **Beuzart-Plessis (12.1.2) for each regular orbit** (Thesis (6.1.2)), for the inner twists of
`GSpin`: under the hypotheses of `bp_germAvg_transfer`, `c_{θ',O'}(y) = c_{θ,O}(x)` for all `O ∈
Nil_reg(𝔤_x)`, `O' ∈ Nil_reg(𝔤_{α,y})`. From the averaged form `bp_germAvg_transfer`, since for the
stable `θ`, `θ'` every regular germ equals the average (`germ_eq_germ_of_stable`, `finite_nilReg`). -/
theorem bp_germ_transfer (d : GGPData F) (hqs : d.IsQuasiSplit) (ψ : NontrivialAddChar F)
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
        germ d.G d.lie d.bilin ψ θ (d.diag x) O := by
  intro O hO O' hO'
  have e : germAvg d.G d.lie d.bilin ψ θ (d.diag x) = germ d.G d.lie d.bilin ψ θ (d.diag x) O :=
    germAvg_eq_germ_of_forall_eq (finite_nilReg d _ hx) hO
      fun O₂ h₂ => germ_eq_germ_of_stable d ψ θ hθ hstab _ hx O₂ h₂ O hO
  have e' : germAvg (d.twist τ).G (d.twist τ).lie (d.twist τ).bilin ψ θ' ((d.twist τ).diag y) =
      germ (d.twist τ).G (d.twist τ).lie (d.twist τ).bilin ψ θ' ((d.twist τ).diag y) O' :=
    germAvg_eq_germ_of_forall_eq (finite_nilReg (d.twist τ) _ hy) hO'
      fun O₂ h₂ => germ_eq_germ_of_stable (d.twist τ) ψ θ' hθ' hstab' _ hy O₂ h₂ O' hO'
  rw [← e', ← e, bp_germAvg_transfer d hqs ψ τ θ θ' hθ hθ' hstab hstab' htrans x y hx hy hxy]

end GSpinGGP
