/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.HarishChandra
import GSpinGGP.Foundations.Determinant
import GSpinGGP.GGP.LieRegular

/-!
# The regular set and the transfer of germs

The regular set of `G = GSpin(W) × GSpin(V)` is open and conull (from Harish-Chandra's theorem
`hc_regular_open_dense_conull` and the identification of his regular set with `regularSet`,
`hcDisc_ne_zero_iff_mem_regularSet`), and germs are preserved under transfer to inner forms (BP Astérisque 418,
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

/-- The average germ is any one germ when all regular germs agree: if `Nil_reg(𝔤_x)` is finite, `O
∈ Nil_reg(𝔤_x)` and `c_{θ,O'}(x) = c_{θ,O}(x)` for every `O' ∈ Nil_reg(𝔤_x)`, then `c_θ(x) =
c_{θ,O}(x)`. -/
theorem germAvg_eq_germ_of_forall_eq {A : Type*} [Ring A] [Algebra F A] [TopologicalSpace A]
    [Module.Finite F A] [IsModuleTopology F A]
    {G : Subgroup Aˣ} {𝔤 : LieSubalgebra F A} {b : LinearMap.BilinForm F A}
    {ψ : NontrivialAddChar F} {θ : ↥G → ℂ} {x : ↥G}
    (hfin : (NilReg (grpCentralizer G x) (lieCentralizer 𝔤 ((x : Aˣ) : A))).Finite)
    {O : NilOrbit (grpCentralizer G x) (lieCentralizer 𝔤 ((x : Aˣ) : A))}
    (hO : O ∈ NilReg (grpCentralizer G x) (lieCentralizer 𝔤 ((x : Aˣ) : A)))
    (h : ∀ O' ∈ NilReg (grpCentralizer G x) (lieCentralizer 𝔤 ((x : Aˣ) : A)),
      germ G 𝔤 b ψ θ x O' = germ G 𝔤 b ψ θ x O) :
    germAvg G 𝔤 b ψ θ x = germ G 𝔤 b ψ θ x O := by
  unfold germAvg
  rw [finsum_mem_congr rfl h, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const,
    Set.ncard_eq_toFinset_card _ hfin, nsmul_eq_mul]
  have : (hfin.toFinset.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨O, hfin.mem_toFinset.mpr hO⟩).ne'
  field_simp

/-- **Finitely many regular nilpotent orbits.** For semisimple `x ∈ G(F)`, `G = GSpin(W) ×
GSpin(V)`, the set `Nil_reg(𝔤_x)` of regular nilpotent `G_x(F)`-orbits in `𝔤_x(F)` is finite.

Proof sketch (not formalized). If it is nonempty, `G_x` is quasi-split. For a regular nilpotent `N
∈ 𝔤_x(F)` the centralizer is `Z(G_x) · U_N` with `U_N` connected unipotent (Kostant, *The principal
three-dimensional subgroup…*, Amer. J. Math. 81 (1959), Thm 5.3 and Cor. 5.6; Jantzen, *Nilpotent
orbits in representation theory* (2004), §6.7–6.8), and `H¹(F, U_N) = 0` (Springer–Steinberg, LNM
131, III.3.7). All regular nilpotent elements form one geometric orbit, so the `G_x(F)`-orbits in
it are in bijection with `ker(H¹(F, Z(G_x)) → H¹(F, G_x))`, which is finite (Borel–Serre, Comment.
Math. Helv. 39 (1964), Thm 6.1, p. 153: `H¹(F, A)` is finite for a linear algebraic group `A` over
a `p`-adic field). `G_x` is connected because the derived group of `GSpin` is simply connected
(Steinberg).

**Status: `sorry`** (standard; not stated verbatim for this group in a source). -/
theorem finite_nilReg (d : GGPData F) (x : ↥d.G) (hx : IsSS F ((x : d.ambientˣ) : d.ambient)) :
    (NilReg (grpCentralizer d.G x)
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))).Finite := by
  sorry

/-- **The regular germs of a stable quasi-character do not depend on the orbit.** Let `θ` be a
quasi-character on `G(F)` that is *stable* (`θ(x) = θ(x')` for stably conjugate regular `x, x'`; BP
Astérisque 418 §12.1, pp. 259–260), and `x ∈ G(F)` semisimple. Then `c_{θ,O}(x) = c_{θ,O'}(x)` for
all `O, O' ∈ Nil_reg(𝔤_x)`. Used in Thesis (6.1.2), whose proof states it without proof.

Proof sketch (not formalized). (1) For `X` in a small lattice ball `B ⊆ 𝔤_x(F)` around `0`, stable
conjugacy of regular `X, X'` in `𝔤_x` gives stable conjugacy of `x e^X, x e^{X'}` in `G`, so
`θ_x(X) = θ(x e^X)` is stable on `B ∩ 𝔤_{x,reg}`. (2) In the expansion `θ_x = Σ_O c_{θ,O}(x)
ĵ(O,·)` (BP §4.1, p. 74), homogeneity `ĵ(O, λX) = |λ|^{-dim O/2} ĵ(O, X)` for `λ ∈ F^{×2}` (BP
(1.8.5), p. 34) and a Vandermonde argument in `λ = ϖ^{2j}` show that the regular part `Φ = Σ_{O
regular} c_{θ,O}(x) ĵ(O,·)` is stable on all of `𝔤_{x,reg}`. (3) Pairing `Φ` with `h = (f₁ − f₁ ∘
Ad(g)⁻¹)^∨`, where `g ∈ G_{x,ad}(F)` and `f₁` is the indicator of a small compact open set meeting
the nilpotent cone only in one regular orbit `O₁`: the stable orbital integrals of `h` vanish, so
(Weyl integration grouped by stable classes, from Kottwitz, *Harmonic analysis on reductive
`p`-adic groups and Lie algebras*, Clay Math. Proc. 4 (2005), (7.7.1), p. 423) `0 = ∫ Φ h =
c_{θ,O₁}(x) − c_{θ,gO₁}(x)`. (4) `G_{x,ad}(F)` acts transitively on the regular nilpotent
`G_x(F)`-orbits (Langlands–Shelstad §5.1; Kostant's centralizer theorem and `H¹(F, U) = 0`).

**Status: `sorry`, not a literature axiom** (no source states it for general quasi-split groups;
the argument above is general). -/
theorem germ_eq_of_isStable (d : GGPData F) (ψ : NontrivialAddChar F) (θ : ↥d.G → ℂ)
    (hθ : IsQuasiCharacter d.G d.lie d.bilin ψ θ)
    (hstab : ∀ x ∈ regularSet d.G d.lie, ∀ x' ∈ regularSet d.G d.lie,
      d.StablyConj x x' → θ x = θ x')
    (x : ↥d.G) (hx : IsSS F ((x : d.ambientˣ) : d.ambient)) :
    ∀ O ∈ NilReg (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)),
    ∀ O' ∈ NilReg (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)),
      germ d.G d.lie d.bilin ψ θ x O = germ d.G d.lie d.bilin ψ θ x O' := by
  sorry

/-- **Beuzart-Plessis (12.1.2), averaged form, for the inner twists of `GSpin`** (Thesis (6.1.2)).
Let `G` be quasi-split, `τ` an inner twist (`G_α = (d.twist τ).G`), `θ` a stable quasi-character on
`G(F)` and `θ'` a stable quasi-character on `G_α(F)` which is a transfer of `θ`: `θ'(y) = θ(x)`
whenever `x ∈ G_reg(F)`, `y ∈ G_{α,reg}(F)` are stably conjugate through `ψ_α = C(φ) × C(φ ⊕
id_Z)`. Then for `x ∈ GSpin(W)(F)`, `y ∈ GSpin(W_α)(F)` semisimple and strongly stably conjugate
(embedded diagonally), `c_{θ'}(y) = c_θ(x)`, where `c_θ(x) = |Nil_reg(𝔤_x)|⁻¹ Σ_{O ∈ Nil_reg(𝔤_x)}
c_{θ,O}(x)` (`germAvg`).

Source: Beuzart-Plessis, Astérisque 418 (2020), (12.1.2), p. 260, stated for a connected reductive
`G` and its *pure* inner forms. The inner forms here have cocycles valued in `SO(W) × SO(V)`, and
those with the other Hasse invariant are not pure inner forms of `GSpin(W) × GSpin(V)`. BP's proof
does not use purity: if `G_x`, `G_{α,y}` are not quasi-split both sides are `0` (BP Prop 4.5.1
1.(i), p. 96); otherwise transport a Borel pair `(B_x, T_x)` of `G_x` along the `F`-isomorphism `ι
: G_x ≅ G_{α,y}`, apply the limit formula BP Prop 4.5.1 1.(ii) on both sides, and use that `x'` and
`ι(x')` are stably conjugate for regular `x' ∈ T_x(F)` (so `θ'(ι(x')) = θ(x')`), with `D^G(x') =
D^{G_α}(ι(x'))` and `|W(G_x, T_x)| = |W(G_{α,y}, T_y)|`. Stability and transfer are written out
inline. Only diagonal elements are needed (Thesis §6.7).

**Status: `sorry`, not a literature axiom** (stated in the source for pure inner forms only). -/
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
  sorry

/-- **Beuzart-Plessis (12.1.2) for each regular orbit** (Thesis (6.1.2)), for the inner twists of
`GSpin`: under the hypotheses of `bp_germAvg_transfer`, `c_{θ',O'}(y) = c_{θ,O}(x)` for all `O ∈
Nil_reg(𝔤_x)`, `O' ∈ Nil_reg(𝔤_{α,y})`. From the averaged form `bp_germAvg_transfer`, since for the
stable `θ`, `θ'` every regular germ equals the average (`germ_eq_of_isStable`, `finite_nilReg`). -/
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
      fun O₂ h₂ => germ_eq_of_isStable d ψ θ hθ hstab _ hx O₂ h₂ O hO
  have e' : germAvg (d.twist τ).G (d.twist τ).lie (d.twist τ).bilin ψ θ' ((d.twist τ).diag y) =
      germ (d.twist τ).G (d.twist τ).lie (d.twist τ).bilin ψ θ' ((d.twist τ).diag y) O' :=
    germAvg_eq_germ_of_forall_eq (finite_nilReg (d.twist τ) _ hy) hO'
      fun O₂ h₂ => germ_eq_of_isStable (d.twist τ) ψ θ' hθ' hstab' _ hy O₂ h₂ O' hO'
  rw [← e', ← e, bp_germAvg_transfer d hqs ψ τ θ θ' hθ hθ' hstab hstab' htrans x y hx hy hxy]

end GSpinGGP
