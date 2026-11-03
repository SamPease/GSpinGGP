/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.HarishChandra
import GSpinGGP.Foundations.Determinant
import GSpinGGP.GGP.RegularRank
import GSpinGGP.GGP.LieRank

/-!
# The regular set and the transfer of germs

The regular set of `G = GSpin(W) × GSpin(V)` is open and conull (from Harish-Chandra's theorem
`hc_regular_open_dense_conull` and the identification of his regular set with `regularSet`, a
`sorry` theorem), and germs are preserved under transfer to inner forms (BP Astérisque 418,
(12.1.2), which is stated for pure inner forms; a `sorry` theorem with a proof sketch).
-/

open MeasureTheory Topology Filter

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

open HarishChandra

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- `𝔤 = gspin(W) × gspin(V)` is `Ad(G)`-stable. -/
theorem lie_conj_stable (d : GGPData F) (t : ↥d.G) :
    ∀ X ∈ d.lie.toSubmodule, conjAd F (t : d.ambientˣ) X ∈ d.lie.toSubmodule := fun _ hX =>
  ⟨conj_mem_gspin d.QW (d.fst t) hX.1, conj_mem_gspin d.QV (d.snd t) hX.2⟩

/-- `1 − Ad(t)` on `𝔤`. -/
abbrev oneSubAd (d : GGPData F) (t : ↥d.G) : d.lie.toSubmodule →ₗ[F] d.lie.toSubmodule :=
  1 - (conjAd F (t : d.ambientˣ)).toLinearEquiv.toLinearMap.restrict (lie_conj_stable d t)

/-- `1 − Ad g` is semisimple on `𝔤` for semisimple `g ∈ G(F)`. -/
theorem isSemisimple_oneSubAd (d : GGPData F) (g : ↥d.G) (hg : IsSS F ((g : d.ambientˣ) : d.ambient)) :
    Module.End.IsSemisimple (oneSubAd d g) := by
  set a : d.ambient := ((g : d.ambientˣ) : d.ambient)
  set ai : d.ambient := (((g : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient)
  have hAd : Module.End.IsSemisimple (LinearMap.mulLeft F a * LinearMap.mulRight F ai) :=
    isSemisimple_conj_of_mulLeft hg
  have hp' : ∀ X ∈ d.lie.toSubmodule,
      (LinearMap.mulLeft F a * LinearMap.mulRight F ai) X ∈ d.lie.toSubmodule := fun X hX => by
    have := lie_conj_stable d g X hX
    simpa [mul_assoc] using this
  have hp : d.lie.toSubmodule ∈ Module.End.invtSubmodule
      (LinearMap.mulLeft F a * LinearMap.mulRight F ai) :=
    (Module.End.mem_invtSubmodule _).mpr hp'
  have hres := hAd.restrict hp
  have heq : (conjAd F (g : d.ambientˣ)).toLinearEquiv.toLinearMap.restrict (lie_conj_stable d g) =
      (LinearMap.mulLeft F a * LinearMap.mulRight F ai).restrict hp' :=
    LinearMap.ext fun X => Subtype.ext (mul_assoc _ _ _)
  rw [oneSubAd, heq]
  exact Module.End.IsSemisimple.sub_of_commute (Commute.one_left _) Module.End.isSemisimple_id hres

/-- `𝔤_{(a,b)} = gspin(W)_a × gspin(V)_b`. -/
theorem finrank_lieCentralizer_lie (d : GGPData F) (X : d.ambient) :
    Module.finrank F ↥(lieCentralizer d.lie X) =
      Module.finrank F ↥(lieCentralizer (gspin d.QW) X.1) +
        Module.finrank F ↥(lieCentralizer (gspin d.QV) X.2) := by
  have h : (lieCentralizer d.lie X).toSubmodule =
      (lieCentralizer (gspin d.QW) X.1).toSubmodule.prod (lieCentralizer (gspin d.QV) X.2).toSubmodule := by
    ext Y
    simp only [LieSubalgebra.mem_toSubmodule, Submodule.mem_prod, mem_lieCentralizer, Prod.ext_iff,
      Prod.fst_mul, Prod.snd_mul]
    exact ⟨fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨h1, h3⟩, h2, h4⟩, fun ⟨⟨h1, h3⟩, h2, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩⟩
  show Module.finrank F ↥(lieCentralizer d.lie X).toSubmodule =
    Module.finrank F ↥(lieCentralizer (gspin d.QW) X.1).toSubmodule +
      Module.finrank F ↥(lieCentralizer (gspin d.QV) X.2).toSubmodule
  rw [h, (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]

/-- `rank 𝔤 = rank gspin(W) + rank gspin(V)`. -/
theorem lieRank_lie (d : GGPData F) :
    lieRank d.lie = lieRank (gspin d.QW) + lieRank (gspin d.QV) := by
  have : Nonempty ↥d.lie := ⟨0⟩
  apply le_antisymm
  · obtain ⟨a, ha⟩ := Nat.sInf_mem (Set.range_nonempty
      fun X : gspin d.QW => Module.finrank F (lieCentralizer (gspin d.QW) (X : CliffordAlgebra d.QW)))
    obtain ⟨b, hb⟩ := Nat.sInf_mem (Set.range_nonempty
      fun X : gspin d.QV => Module.finrank F (lieCentralizer (gspin d.QV) (X : CliffordAlgebra d.QV)))
    refine (ciInf_le (OrderBot.bddBelow _) (⟨((a : CliffordAlgebra d.QW), (b : CliffordAlgebra d.QV)),
      a.2, b.2⟩ : ↥d.lie)).trans_eq ?_
    rw [finrank_lieCentralizer_lie]
    exact congrArg₂ (· + ·) ha hb
  · refine le_ciInf fun Y => ?_
    rw [finrank_lieCentralizer_lie]
    exact add_le_add (ciInf_le (OrderBot.bddBelow _) (⟨(Y : d.ambient).1, Y.2.1⟩ : ↥(gspin d.QW)))
      (ciInf_le (OrderBot.bddBelow _) (⟨(Y : d.ambient).2, Y.2.2⟩ : ↥(gspin d.QV)))

/-- If `𝔤_{(a,b)}` is abelian, so are `gspin(W)_a` and `gspin(V)_b`. -/
theorem isLieAbelian_lieCentralizer_fst_snd (d : GGPData F) {X : d.ambient}
    (hab : IsLieAbelian (lieCentralizer d.lie X)) :
    IsLieAbelian (lieCentralizer (gspin d.QW) X.1) ∧
      IsLieAbelian (lieCentralizer (gspin d.QV) X.2) := by
  constructor
  · refine ⟨fun Y₁ Y₂ => Subtype.ext ?_⟩
    obtain ⟨h₁, c₁⟩ := mem_lieCentralizer.mp Y₁.2
    obtain ⟨h₂, c₂⟩ := mem_lieCentralizer.mp Y₂.2
    have m : ∀ Y ∈ lieCentralizer (gspin d.QW) X.1, ((Y, 0) : d.ambient) ∈ lieCentralizer d.lie X :=
      fun Y hY => mem_lieCentralizer.2 ⟨⟨(mem_lieCentralizer.mp hY).1, zero_mem _⟩,
        Prod.ext (mem_lieCentralizer.mp hY).2 (by simp)⟩
    have := congrArg (fun Z : lieCentralizer d.lie X => (Z : d.ambient).1)
      (hab.trivial ⟨_, m _ Y₁.2⟩ ⟨_, m _ Y₂.2⟩)
    simpa [LieSubalgebra.coe_bracket, Ring.lie_def] using this
  · refine ⟨fun Y₁ Y₂ => Subtype.ext ?_⟩
    have m : ∀ Y ∈ lieCentralizer (gspin d.QV) X.2, ((0, Y) : d.ambient) ∈ lieCentralizer d.lie X :=
      fun Y hY => mem_lieCentralizer.2 ⟨⟨zero_mem _, (mem_lieCentralizer.mp hY).1⟩,
        Prod.ext (by simp) (mem_lieCentralizer.mp hY).2⟩
    have := congrArg (fun Z : lieCentralizer d.lie X => (Z : d.ambient).2)
      (hab.trivial ⟨_, m _ Y₁.2⟩ ⟨_, m _ Y₂.2⟩)
    simpa [LieSubalgebra.coe_bracket, Ring.lie_def] using this

/-- **The centralizer of a regular semisimple element has the dimension of the rank**: for
`x ∈ G_reg(F)` (semisimple, `𝔤_x` abelian), `dim 𝔤_x = lieRank 𝔤 = min_{X ∈ 𝔤} dim 𝔤_X`. Both sides
split over `𝔤 = gspin(W) × gspin(V)`; on each factor the centralizer of a regular semisimple
`g ∈ GSpin(U)` has dimension `⌊dim U/2⌋ + 1` (`finrank_lieCentralizer_gspin_of_isLieAbelian`),
which is `rank gspin(U)` (`lieRank_gspin`). -/
theorem finrank_lieCentralizer_eq_lieRank (d : GGPData F) {x : ↥d.G}
    (hx : x ∈ regularSet d.G d.lie) :
    Module.finrank F ↥(lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) = lieRank d.lie := by
  obtain ⟨hss, hab⟩ := hx
  have hssW := isSS_algHom (AlgHom.fst F _ _) hss
  have hssV := isSS_algHom (AlgHom.snd F _ _) hss
  obtain ⟨habW, habV⟩ := isLieAbelian_lieCentralizer_fst_snd d hab
  rw [finrank_lieCentralizer_lie, lieRank_lie, lieRank_gspin d.nondeg, lieRank_gspin d.nondeg_QV]
  exact congrArg₂ (· + ·)
    (finrank_lieCentralizer_gspin_of_isLieAbelian d.nondeg (d.fst x) hssW habW)
    (finrank_lieCentralizer_gspin_of_isLieAbelian d.nondeg_QV (d.snd x) hssV habV)

/-- **Regular semisimple elements lie in Harish-Chandra's `G'`**: `D(x) ≠ 0` for
`x ∈ G_reg(F)`. `N = 1 − Ad x` is semisimple on `𝔤`, so the exact power of `t` dividing its
characteristic polynomial is `t^{dim ker N}` (Mathlib `finrank_maxGenEigenspace_zero_eq`), with
`ker N = 𝔤_x` and `dim 𝔤_x = lieRank 𝔤` (`finrank_lieCentralizer_eq_lieRank`). -/
theorem hcDisc_ne_zero_of_mem_regularSet (d : GGPData F) {x : ↥d.G}
    (hx : x ∈ regularSet d.G d.lie) : hcDisc d x ≠ 0 := by
  obtain ⟨N, hNdef⟩ : ∃ N, N = oneSubAd d x := ⟨_, rfl⟩
  have hss : Module.End.IsSemisimple N := hNdef ▸ isSemisimple_oneSubAd d x hx.1
  have hdeg : (LinearMap.charpoly N).natTrailingDegree = Module.finrank F ↥(LinearMap.ker N) := by
    rw [← LinearMap.finrank_maxGenEigenspace_zero_eq,
      hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace, Module.End.eigenspace_zero]
  -- `ker N = 𝔤_x`
  obtain ⟨a, ha⟩ : ∃ a : d.ambient, a = ((x : d.ambientˣ) : d.ambient) := ⟨_, rfl⟩
  obtain ⟨ai, hai'⟩ : ∃ ai : d.ambient, ai = (((x : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) :=
    ⟨_, rfl⟩
  have hia : ai * a = 1 := by rw [ha, hai']; exact Units.inv_mul _
  have hai : a * ai = 1 := by rw [ha, hai']; exact Units.mul_inv _
  have hN : ∀ X : d.lie.toSubmodule, ((N X : d.lie.toSubmodule) : d.ambient) =
      (X : d.ambient) - a * X * ai := fun X => by rw [hNdef, ha, hai']; rfl
  have hmap : (LinearMap.ker N).map d.lie.toSubmodule.subtype =
      (lieCentralizer d.lie a).toSubmodule := by
    ext X
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.subtype_apply]
    change _ ↔ X ∈ lieCentralizer d.lie a
    rw [mem_lieCentralizer]
    constructor
    · rintro ⟨Y, hY, rfl⟩
      have h0 := congrArg Subtype.val hY
      rw [hN, ZeroMemClass.coe_zero, sub_eq_zero] at h0
      refine ⟨Y.2, ?_⟩
      calc a * Y = a * Y * ai * a := by rw [mul_assoc _ ai, hia, mul_one]
        _ = Y * a := by rw [← h0]
    · rintro ⟨hX, hXa⟩
      refine ⟨⟨X, hX⟩, Subtype.ext ?_, rfl⟩
      rw [hN, ZeroMemClass.coe_zero, sub_eq_zero]
      change X = a * X * ai
      rw [hXa, mul_assoc, hai, mul_one]
  have hker : Module.finrank F ↥(LinearMap.ker N) =
      Module.finrank F ↥(lieCentralizer d.lie a) := by
    rw [(Submodule.equivMapOfInjective d.lie.toSubmodule.subtype
      d.lie.toSubmodule.injective_subtype (LinearMap.ker N)).finrank_eq]
    change Module.finrank F ↥((LinearMap.ker N).map d.lie.toSubmodule.subtype) = _
    rw [hmap]
    rfl
  have hker' : Module.finrank F ↥(LinearMap.ker N) =
      Module.finrank F ↥(lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) := by
    rw [← ha]; exact hker
  have key : (LinearMap.charpoly N).coeff (lieRank d.lie) ≠ 0 := by
    rw [← finrank_lieCentralizer_eq_lieRank d hx, ← hker', ← hdeg]
    change (LinearMap.charpoly N).trailingCoeff ≠ 0
    exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (LinearMap.charpoly_monic N).ne_zero
  rw [hNdef] at key
  unfold hcDisc
  rw [dite_eq_left (lie_conj_stable d x)]
  exact key

/-- **Harish-Chandra's `G'` consists of regular semisimple elements**: `D(x) ≠ 0` implies `x`
semisimple with `𝔤_x` abelian. Proof sketch. `D(x) ≠ 0` says the generalized `1`-eigenspace of
`Ad x` on `𝔤` has dimension `≤ ℓ = lieRank 𝔤`. For `x = su` (Jordan decomposition) that eigenspace is
`𝔤_s`, which contains a Cartan subalgebra, so `𝔤_s` is one and `s` is regular. Then `Z_G(s)⁰` is a
maximal torus, so the unipotent `u ∈ Z_G(s)⁰` is `1`: `x = s` is semisimple and `𝔤_x = 𝔤_s` is
abelian. Missing in the project: the Jordan decomposition in `G(F)` and the Cartan-subalgebra facts
above (as for `finrank_lieCentralizer_eq_lieRank`).
Status: SORRY (structure theory of `GSpin`). -/
theorem mem_regularSet_of_hcDisc_ne_zero (d : GGPData F) {x : ↥d.G} (hx : hcDisc d x ≠ 0) :
    x ∈ regularSet d.G d.lie := by
  sorry

/-- **Harish-Chandra's regular set is the regular semisimple set** (characteristic `0`):
`D(x) ≠ 0` (`hcDisc`) iff `x` is semisimple with abelian centralizer in `𝔤` (`regularSet`). -/
theorem hcDisc_ne_zero_iff_mem_regularSet (d : GGPData F) (x : ↥d.G) :
    hcDisc d x ≠ 0 ↔ x ∈ regularSet d.G d.lie :=
  ⟨mem_regularSet_of_hcDisc_ne_zero d, hcDisc_ne_zero_of_mem_regularSet d⟩

/-- `θ_π = characterOn π (regularSet d.G d.lie)` (Triple's `charG d π`) represents the character
of `π` and is continuous on `G_reg(F)`: Harish-Chandra's theorem (`hc_character_exists`) gives
continuity on `G' = {D ≠ 0}`, which contains `regularSet` (`hcDisc_ne_zero_of_mem_regularSet`). -/
theorem hc_character (d : GGPData F) (π : UnitaryRep ↥d.G) (hπ : IsTempered π) :
    IsCharacterOf π (characterOn π (regularSet d.G d.lie)) ∧
      ContinuousOn (characterOn π (regularSet d.G d.lie)) (regularSet d.G d.lie) := by
  obtain ⟨θ, hθ, hcont⟩ := hc_character_exists d π hπ
  exact characterOn_spec π _ ⟨θ, hθ,
    hcont.mono fun _ hx => hcDisc_ne_zero_of_mem_regularSet d hx⟩

/-- **The regular semisimple set `G_reg(F)` of `G = GSpin(W) × GSpin(V)` is open in `G(F)` and its
complement has Haar measure zero** (Thesis §2.1; BP Astérisque 418, §1). From Harish-Chandra's
theorem `hc_regular_open_dense_conull` (LNM 162, Part V §3, p. 54) and the identification of his
`G' = {D ≠ 0}` with `regularSet` (`hcDisc_ne_zero_iff_mem_regularSet`).

Its role in this project: two representatives of the character distribution that are continuous on
`G_reg(F)` agree on `G_reg(F)` (open, conull), so `characterOn π (regularSet …)` is canonical there.
Stated for the Haar measure `Measure.haar` used in `IsCharacterOf`. -/
theorem hc_regularSet_open_conull (d : GGPData F) :
    IsOpen (regularSet d.G d.lie) ∧
      (Measure.haar : Measure ↥d.G) (regularSet d.G d.lie)ᶜ = 0 := by
  have h := hc_regular_open_dense_conull d
  have hset : {x : ↥d.G | hcDisc d x ≠ 0} = regularSet d.G d.lie :=
    Set.ext (hcDisc_ne_zero_iff_mem_regularSet d)
  rw [hset] at h
  exact ⟨h.1, h.2.2⟩

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
`IsStableFn` is not visible here). Only diagonal elements are needed (Thesis §6.7).

**Status: `sorry`, not a literature axiom** (the statement is not verbatim in a source). BP (12.1.2)
is stated for any connected reductive group, but for *pure* inner forms. The inner forms here have
cocycles valued in `SO(W) × SO(V)`, and those with the other Hasse invariant are not pure inner
forms of `GSpin(W) × GSpin(V)`. BP's proof uses only BP Prop 4.5.1 1.(i),(ii) for `G` and `G_α`
separately, `D^G(x) = D^{G_α}(y)`, and the transport of a Borel pair of `G_x` by the `F`-isomorphism
`G_x ≅ G_{α,y}`. All of these hold here. -/
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
  sorry

end GSpinGGP
