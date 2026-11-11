/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.HarishChandra
import GSpinGGP.Foundations.Determinant
import GSpinGGP.GGP.LieRegular
import GSpinGGP.Foundations.CentralizerIso

/-!
# The regular set and the transfer of germs

The regular set of `G = GSpin(W) × GSpin(V)` is open and conull (from Harish-Chandra's theorem
`hc_regular_open_dense_conull` and the identification of his regular set with `regularSet`,
`hcDisc_ne_zero_iff_mem_regularSet`), and germs are preserved under transfer to inner forms
(`bp_germ_transfer`). The latter is proved from the averaged form of BP Astérisque 418, (12.1.2),
which is stated there for pure inner forms (`bp_germAvg_transfer`, proved here by transport of the
local expansions along the `F`-isomorphism `G_x ≃ G_{α,y}`: `germAvg_eq_of_centralizerIso`, from the
`sorry` theorems `exists_centralizerIso_of_stronglyStablyConjW` and `jHat_centralizerIso`); the
equality of the regular germs of a stable quasi-character (`germ_eq_germ_of_stable`); and the
finiteness of `Nil_reg(𝔤_x)` (`finite_nilReg`).
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
semisimple with `𝔤_x` abelian.  The coefficient of `t^ℓ` (`ℓ = lieRank 𝔤 = lieRankNat d`,
`lieRank_lie`, `lieRank_gspin`) of the characteristic polynomial of `N = 1 − Ad x` on `𝔤` is nonzero,
so the generalized kernel of `N` has dimension `≤ ℓ` (Mathlib `finrank_maxGenEigenspace_zero_eq`);
that kernel is `𝔤 ∩ ker (1 − Ad x)^D`, and `mem_regularSet_of_finrank_ker_le` (Jordan decomposition
in `G(F)` and the rank clauses for `GSpin`) concludes. -/
theorem mem_regularSet_of_hcDisc_ne_zero (d : GGPData F) {x : ↥d.G} (hx : hcDisc d x ≠ 0) :
    x ∈ regularSet d.G d.lie := by
  have hℓ : lieRank d.lie = lieRankNat d := by
    rw [lieRank_lie, lieRank_gspin d.nondeg, lieRank_gspin d.nondeg_QV]
    rfl
  set T : Module.End F d.ambient := 1 - (conjAd F (x : d.ambientˣ)).toLinearEquiv.toLinearMap
  set N := oneSubAd d x
  have hcoeff : (LinearMap.charpoly N).coeff (lieRank d.lie) ≠ 0 := by
    unfold hcDisc at hx
    rwa [dite_eq_left (lie_conj_stable d x)] at hx
  have hle : Module.finrank F ↥(Module.End.maxGenEigenspace N 0) ≤ lieRankNat d := by
    rw [LinearMap.finrank_maxGenEigenspace_zero_eq, ← hℓ]
    exact Polynomial.natTrailingDegree_le_of_ne_zero hcoeff
  set D := Module.finrank F d.ambient
  -- `N = T|_𝔤`, so `N^k v = T^k v` on `𝔤`
  have hT : ∀ X ∈ d.lie.toSubmodule, T X ∈ d.lie.toSubmodule := fun X hX =>
    d.lie.toSubmodule.sub_mem hX (lie_conj_stable d x X hX)
  have hN : N = T.restrict hT := LinearMap.ext fun v => rfl
  have hpow : ∀ (k : ℕ) (v : d.lie.toSubmodule), (((N ^ k) v : d.lie.toSubmodule) : d.ambient) =
      (T ^ k) (v : d.ambient) := fun k v => by
    rw [hN, Module.End.pow_restrict]
    rfl
  have hDle : Module.finrank F d.lie.toSubmodule ≤ D := Submodule.finrank_le _
  have hmax : Module.End.maxGenEigenspace N 0 = LinearMap.ker (N ^ D) := by
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.genEigenspace_nat,
      zero_smul, sub_zero, Module.End.ker_pow_eq_ker_pow_finrank_of_le hDle]
  have hmap : (LinearMap.ker (N ^ D)).map d.lie.toSubmodule.subtype =
      d.lie.toSubmodule ⊓ LinearMap.ker (T ^ D) := by
    ext X
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.subtype_apply, Submodule.mem_inf]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.2, by rw [← hpow, hv]; rfl⟩
    · rintro ⟨hX, hT⟩
      exact ⟨⟨X, hX⟩, Subtype.ext (by rw [hpow]; exact hT), rfl⟩
  apply mem_regularSet_of_finrank_ker_le d x
  rw [← hmap, Submodule.finrank_map_subtype_eq, ← hmax]
  exact hle

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

/-- **Finitely many regular nilpotent orbits.** For semisimple `x ∈ G(F)`, `G = GSpin(W) ×
GSpin(V)`, the set `Nil_reg(𝔤_x)` of regular nilpotent `G_x(F)`-orbits in `𝔤_x(F)` is finite.

Proof sketch (not formalized). `F` has characteristic `0`, so `𝔤_x` has finitely many nilpotent
orbits over `F̄`, and the regular nilpotent elements form one of them. Fix `N` in it with
`N ∈ 𝔤_x(F)`; the `G_x(F)`-orbits of such elements are in bijection with
`ker(H¹(F, Z_{G_x}(N)) → H¹(F, G_x))`, which is finite since `H¹(F, A)` is finite for every
linear algebraic group `A` over a `p`-adic field (Borel–Serre, Comment. Math. Helv. 39 (1964),
Thm 6.1, p. 153).

**Status: `sorry`** (standard; not stated verbatim for this group in a source). -/
theorem finite_nilReg (d : GGPData F) (x : ↥d.G) (hx : IsSS F ((x : d.ambientˣ) : d.ambient)) :
    (NilReg (grpCentralizer d.G x)
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))).Finite := by
  sorry

/-- **The regular germs of a stable quasi-character do not depend on the orbit.** Let `θ` be a
quasi-character on `G(F)` that is *stable* (`hstab`: `θ(x) = θ(x')` for stably conjugate regular
`x, x'`; BP Astérisque 418 §12.1, pp. 259–260), and `x ∈ G(F)` semisimple. Then
`c_{θ,O}(x) = c_{θ,O'}(x)` for all `O, O' ∈ Nil_reg(𝔤_x)`. Used in Thesis (6.1.2), whose proof
states it without proof.

Proof sketch (not formalized), as in the proof of BP (3.4.7), p. 71. There is
`g ∈ G_{x,ad}(F)` with `Ad(g) O = O'`: the adjoint group acts transitively on `Nil_reg(𝔤_x)`
(asserted in that proof). Lift `g` to `ĝ ∈ G_x(F̄)`. For `X ∈ 𝔤_x(F)` near `0` with `x e^X`
regular, `x e^{Ad(g) X} = ĝ (x e^X) ĝ⁻¹` is stably conjugate to `x e^X`, so
`θ(x e^{Ad(g) X}) = θ(x e^X)`. Since the trace form is `Ad(ĝ)`-invariant,
`ĵ(Ad(g) O'', Ad(g) X) = ĵ(O'', X)`, so `X ↦ Σ c_{θ,O''}(x) ĵ(Ad(g) O'', X)` is also a local
expansion of `θ` at `x`; by uniqueness of the expansion (`germ_unique`), `c_{θ,Ad(g) O}(x) =
c_{θ,O}(x)`.

**Status: `sorry`, not a literature axiom** (the transitivity and the argument are in BP's proof
of (3.4.7); the statement itself is not in a source). -/
theorem germ_eq_germ_of_stable (d : GGPData F) (ψ : NontrivialAddChar F) (θ : ↥d.G → ℂ)
    (hθ : IsQuasiCharacter d.G d.lie d.bilin ψ θ)
    (hstab : ∀ x ∈ regularSet d.G d.lie, ∀ x' ∈ regularSet d.G d.lie,
      d.StablyConj x x' → θ x = θ x')
    (x : ↥d.G) (hx : IsSS F ((x : d.ambientˣ) : d.ambient)) :
    ∀ O ∈ NilReg (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)),
    ∀ O' ∈ NilReg (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)),
      germ d.G d.lie d.bilin ψ θ x O = germ d.G d.lie d.bilin ψ θ x O' := by
  sorry

namespace GGPData

variable (d : GGPData F)

/-- `𝔤 = gspin(W) × gspin(V)` is `Ad(G)`-stable. -/
theorem conj_mem_lie (g : ↥d.G) {X : d.ambient} (hX : X ∈ d.lie) :
    ((g : d.ambientˣ) : d.ambient) * X * ((g⁻¹ : d.ambientˣ) : d.ambient) ∈ d.lie :=
  ⟨conj_mem_gspin d.QW (d.fst g) hX.1, conj_mem_gspin d.QV (d.snd g) hX.2⟩

/-- `conj_mem_lie` for units of the ambient algebra lying in `G`, in the form used by
`CentralizerIso`. -/
theorem conj_mem_lie_of_mem :
    ∀ g ∈ d.G, ∀ Y ∈ d.lie, (g : d.ambient) * Y * (↑g⁻¹ : d.ambient) ∈ d.lie :=
  fun g hg Y hY => d.conj_mem_lie ⟨g, hg⟩ hY

end GGPData

/-- **`ĵ` is transported by isomorphisms of descent data.** If `ι : (G_x, 𝔤_x) ≃ (G'_y, 𝔤'_y)`
respects the commutator, the trace forms, nilpotency, regular semisimplicity, the adjoint actions
and the maps `Y ↦ e^Y X e^{-Y}` (`CentralizerIso`), then `ĵ(ι O, ι X) = ĵ(O, X)` for every nilpotent
orbit `O` of `𝔤_x(F)` and every regular semisimple `X ∈ 𝔤_x(F)`.

Proof sketch (not formalized): transport of structure. `ι` is a linear homeomorphism
`𝔤_x(F) ≃ 𝔤'_y(F)` (finite dimension) carrying `b|_{𝔤_x}` to `b'|_{𝔤'_y}`, so it carries the
self-dual Haar measure and the Fourier transform of `𝔤_x(F)` to those of `𝔤'_y(F)`. It carries the
Kirillov forms `b(·, [X, ·])` and the charts `Y ↦ e^Y X e^{-Y}` to those at `ι X`, and intertwines the
actions of `G_x(F)` and `G'_y(F)`, so the push-forward of the orbit measure `μ_O` satisfies the
defining conditions of `μ_{ι O}`; these determine the measure (the charts cover the orbit). Hence
`X ↦ ĵ(O, ι⁻¹ X)` represents `f ↦ μ_{ι O}(f̂)`, and representatives agree on the open regular set
(`eqOn_of_isJHat`; the self-dual measure exists since `b` is nondegenerate on `𝔤_x`).

**Status: `sorry`** (formal transport of structure; no literature input). -/
theorem jHat_centralizerIso (d d' : GGPData F) (ψ : NontrivialAddChar F) (x : ↥d.G) (y : ↥d'.G)
    (hx : IsSS F ((x : d.ambientˣ) : d.ambient)) (hy : IsSS F ((y : d'.ambientˣ) : d'.ambient))
    (ι : CentralizerIso d.G d.lie d.bilin d'.G d'.lie d'.bilin (x : d.ambientˣ) (y : d'.ambientˣ))
    (O : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)))
    (X : d.ambient) (hX : X ∈ lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))
    (hXr : IsRegularSS (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) X) :
    jHat (grpCentralizer d'.G y) (lieCentralizer d'.lie ((y : d'.ambientˣ) : d'.ambient)) d'.bilin ψ
        (ι.nilOrbitEquiv d.conj_mem_lie_of_mem O) (ι.lin X) =
      jHat (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) d.bilin ψ
        O X := by
  sorry

/-- **Germs are transported by isomorphisms of descent data.** Let `ι : (G_x, 𝔤_x) ≃ (G'_y, 𝔤'_y)`
be as in `CentralizerIso`, `θ` a quasi-character on `G(F)` and `θ'` a function on `G'(F)` such that
`θ'(y e^{ι X}) = θ(x e^X)` for `X ∈ 𝔤_x(F)` small and regular. Then `c_{θ', ι O}(y) = c_{θ, O}(x)`
for every nilpotent orbit `O` of `𝔤_x(F)`: the local expansion of `θ` at `x`, transported by `ι`
(`jHat_centralizerIso`), is a local expansion of `θ'` at `y`, and germs are its coefficients
(`germ_unique`). -/
theorem germ_eq_germ_of_centralizerIso (d d' : GGPData F) (ψ : NontrivialAddChar F)
    (θ : ↥d.G → ℂ) (θ' : ↥d'.G → ℂ) (hθ : IsQuasiCharacter d.G d.lie d.bilin ψ θ)
    (x : ↥d.G) (y : ↥d'.G)
    (hx : IsSS F ((x : d.ambientˣ) : d.ambient)) (hy : IsSS F ((y : d'.ambientˣ) : d'.ambient))
    (ι : CentralizerIso d.G d.lie d.bilin d'.G d'.lie d'.bilin (x : d.ambientˣ) (y : d'.ambientˣ))
    (hloc : ∃ ω ∈ 𝓝 (0 : d.ambient), ∀ X ∈ ω,
      X ∈ lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient) →
      IsRegularSS (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) X →
      ∀ y' : ↥d'.G, ((y' : d'.ambientˣ) : d'.ambient) =
          ((y : d'.ambientˣ) : d'.ambient) * expA F (ι.lin X) →
        ∃ z : ↥d.G, ((z : d.ambientˣ) : d.ambient) = ((x : d.ambientˣ) : d.ambient) * expA F X ∧
          θ' y' = θ z)
    (O : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))) :
    germ d'.G d'.lie d'.bilin ψ θ' y (ι.nilOrbitEquiv d.conj_mem_lie_of_mem O) =
      germ d.G d.lie d.bilin ψ θ x O := by
  set E := ι.nilOrbitEquiv d.conj_mem_lie_of_mem
  have hreg := ι.nilOrbitEquiv_mem_nilReg_iff d.conj_mem_lie_of_mem d'.conj_mem_lie_of_mem
  obtain ⟨c, hcfin, ω₂, hω₂, hc⟩ := hθ.2 x hx
  obtain ⟨ω₁, hω₁, hl⟩ := hloc
  obtain ⟨ω', hω', hω'sub⟩ := ι.exists_nhds_of_mem_nhds (inter_mem hω₁ hω₂)
  -- the transported expansion
  have hc' : HasGermExpansion d'.G d'.lie d'.bilin ψ θ' y (c ∘ E.symm) := by
    refine ⟨hcfin.preimage E.symm.injective.injOn, ω', hω',
      fun X' hX'ω hX' hX'r y' hy' => ?_⟩
    obtain ⟨X, hX, rfl⟩ := ι.surjOn X' hX'
    have hXω : X ∈ ω₁ ∩ ω₂ := hω'sub X hX hX'ω
    have hXr := (ι.isRegularSS_iff X hX).mp hX'r
    obtain ⟨z, hz, hθz⟩ := hl X hXω.1 hX hXr y' hy'
    rw [hθz, hc X hXω.2 hX hXr z hz, ← finsum_comp_equiv E]
    refine finsum_congr fun O₁ => ?_
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [jHat_centralizerIso d d' ψ x y hx hy ι O₁ X hX hXr]
  by_cases hO : O ∈ NilReg _ _
  · have hO' : E O ∈ NilReg _ _ := (hreg O).mpr hO
    rw [germ_eq_of_hasGermExpansion d' ψ hy hc' hO',
      germ_eq_of_hasGermExpansion d ψ hx ⟨hcfin, ω₂, hω₂, hc⟩ hO]
    simp
  · rw [germ_of_not_mem hO, germ_of_not_mem fun h =>
      hO ((hreg O).mp h)]

/-- The averaged germs agree: `c_{θ'}(y) = c_θ(x)` under the hypotheses of
`germ_eq_germ_of_centralizerIso`, since `ι` maps `Nil_reg(𝔤_x)` bijectively onto `Nil_reg(𝔤'_y)`. -/
theorem germAvg_eq_of_centralizerIso (d d' : GGPData F) (ψ : NontrivialAddChar F)
    (θ : ↥d.G → ℂ) (θ' : ↥d'.G → ℂ) (hθ : IsQuasiCharacter d.G d.lie d.bilin ψ θ)
    (x : ↥d.G) (y : ↥d'.G)
    (hx : IsSS F ((x : d.ambientˣ) : d.ambient)) (hy : IsSS F ((y : d'.ambientˣ) : d'.ambient))
    (ι : CentralizerIso d.G d.lie d.bilin d'.G d'.lie d'.bilin (x : d.ambientˣ) (y : d'.ambientˣ))
    (hloc : ∃ ω ∈ 𝓝 (0 : d.ambient), ∀ X ∈ ω,
      X ∈ lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient) →
      IsRegularSS (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) X →
      ∀ y' : ↥d'.G, ((y' : d'.ambientˣ) : d'.ambient) =
          ((y : d'.ambientˣ) : d'.ambient) * expA F (ι.lin X) →
        ∃ z : ↥d.G, ((z : d.ambientˣ) : d.ambient) = ((x : d.ambientˣ) : d.ambient) * expA F X ∧
          θ' y' = θ z) :
    germAvg d'.G d'.lie d'.bilin ψ θ' y = germAvg d.G d.lie d.bilin ψ θ x := by
  set E := ι.nilOrbitEquiv d.conj_mem_lie_of_mem
  have hreg := ι.nilOrbitEquiv_mem_nilReg_iff d.conj_mem_lie_of_mem d'.conj_mem_lie_of_mem
  have hset : NilReg (grpCentralizer d'.G y) (lieCentralizer d'.lie ((y : d'.ambientˣ) : d'.ambient)) =
      E '' NilReg (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) := by
    ext O'
    refine ⟨fun h => ⟨E.symm O', ?_, E.apply_symm_apply O'⟩, ?_⟩
    · rw [← hreg (E.symm O')]
      simpa [E] using h
    · rintro ⟨O, hO, rfl⟩
      exact (hreg O).mpr hO
  unfold germAvg
  rw [hset, finsum_mem_image E.injective.injOn, Set.ncard_image_of_injective _ E.injective]
  congr 1
  exact finsum_mem_congr rfl fun O _ =>
    germ_eq_germ_of_centralizerIso d d' ψ θ θ' hθ x y hx hy ι hloc O

/-- **Strongly stably conjugate elements have isomorphic descent data** (Thesis §6.1). Let
`x ∈ GSpin(W)(F)`, `y ∈ GSpin(W_α)(F)` be semisimple and strongly stably conjugate (`hxy`): there is
`g ∈ G_α(F̄)` with `y = g ψ_α(x) g⁻¹` such that `ι = Ad(g) ∘ ψ_α : G_x ≃ G_{α,y}` is defined over `F`
(`ψ_α = C(φ) × C(φ ⊕ id_Z)`; `x`, `y` embedded diagonally). Then `ι` induces an isomorphism of
descent data `CentralizerIso` at `x` and `y`, and for `X ∈ 𝔤_x(F)` small and regular the elements
`x e^X ∈ G_reg(F)` and `y e^{ι X} ∈ G_{α,reg}(F)` are stably conjugate (through `ψ_α`, by the same
`g`).

Proof sketch (not formalized). `ι` is the restriction of the `F̄`-algebra isomorphism
`a ↦ g ψ_α(a) g⁻¹` of the ambient algebras (base changed to `F̄`); since `ι` commutes with the Galois
action on `G_x`, so does its differential on `𝔤_x`, and `ι` maps `G_x(F)`, `𝔤_x(F)` onto
`G_{α,y}(F)`, `𝔤_{α,y}(F)`. An algebra isomorphism preserves commutators, nilpotency,
semisimplicity (both are invariant under base change), centralizers, the trace forms
`tr(L_{XY})` and the exponential series, which gives the fields of `CentralizerIso`. For
`X ∈ 𝔤_x(F)` small, `x e^X ∈ G_x(F)` (Waldspurger's good neighbourhoods, `waldspurger_goodNbhd`),
it is regular when `X` is regular in `𝔤_x` (`exists_nhds_isRegularSS_mul_expA`), and
`g ψ_α(x e^X) g⁻¹ = y e^{ι X}`.

**Status: `sorry`** (the dissertation's own argument, Thesis §6.1). -/
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
  sorry

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
are needed (Thesis §6.7). -/
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
