/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.LatticeK

/-!
# Special maximal compact subgroups in good position, in lattice form

Waldspurger (*Une formule intégrale reliée à la conjecture locale de Gross–Prasad*, Compositio
Math. 146 (2010); "W1", cited with the pagination of arXiv:0902.1875v1) and Beuzart-Plessis
(Astérisque 418, §1.10, §5.2) define `θ_f` with a **special** maximal compact subgroup `K` in good
position relative to a Levi subgroup `M`.  For orthogonal groups W1 describes these subgroups by
lattices (§7.1, arXiv p. 34; §7.2, arXiv pp. 34–35).  This file transcribes that description to
`G = GSpin(W) × GSpin(V)` and a flag Levi datum `L`.

## W1's special lattices (§7.1)

W1 writes `q(·,·)` for the bilinear form and `q(v) = ½ q(v, v)`.  Here W1's bilinear form is
`QuadraticMap.polar Q`, so W1's `q(v)` is `Q v`.  A *hyperbolic system* is a family
`(v_i)_{i = ±1, …, ±n}` with `q(v_i, v_j) = δ_{i,-j}`; here `v i = v_{i+1}` and `v' i = v_{-(i+1)}`.
Take an orthogonal decomposition `V = Z ⊕ V_an` with `Z` spanned by a hyperbolic system and
`q|_{V_an}` anisotropic, and `c ∈ ℤ` such that `val_F(q(v)) = c` for some `v ∈ V_an` (any `c` if
`V_an = 0`).  The lattice
`R = ⟨v_i, ϖ^c v_{-i}⟩_{𝒪_F} ⊕ {v ∈ V_an : val_F(q(v)) ≥ c}`
is *special*, and these lattices, for all such choices, are "par définition" the special
lattices.  In `SpecialLattice` the integer `c` is replaced by `r = |ϖ^c|`, a norm of a nonzero
element of `F`, so that no uniformizer is chosen: `val_F(x) ≥ c` is `‖x‖ ≤ r`.

The class of special lattices does not change when the form is scaled (the hyperbolic system and
`|ϖ^c|` rescale together).  So the convention `q(·,·) = polar Q` used here and the convention
`q(·,·) = bform Q` of `LuoDatum.IsSpecialLattice` (`TraceFormula/W1Lie.lean`) describe the same
lattices; inside one definition the convention is used consistently.

## The subgroup and the predicate

* `SpecialLattice.IsAdapted b wt`: each `v_{±i}` lies in one weight space of `(b, wt)` and
  `V_an` lies in the weight-`0` space.  Then the split torus `A` of the hyperbolic system
  (acting by `t_i` on `v_i`, `t_i⁻¹` on `v_{-i}`, trivially on `V_an`) preserves every weight space,
  so `A ⊆ M` (`M` is the stabilizer of the weight spaces, `mem_flagLevi_iff`).
* `GGPData.specialStab S_W S_V`: the `g ∈ G` with `H_G(g) = 0` (`hcG g = 1`) such that `P(g)`
  stabilizes `R_W` and `R_V` (`latticeStab`).
* `GGPData.GoodK.IsSpecial K`: `K` **equals** `specialStab S_W S_V` for special lattices adapted to
  `L`.

## Identification with "special, in good position relative to `M`"

1. *Special subgroups* are the stabilizers `G(F)^x` of special points `x` of the extended building
   (Tits, *Reductive groups over local fields*, Corvallis (PSPUM 33 Part 1), 3.1, p. 50, with the
   extended apartment of 1.2, pp. 31–32); they are maximal compact (3.2).
2. For `G = GSpin(W) × GSpin(V)` the building is the product of the buildings of the factors and
   special means special in each factor (Tits 2.1, p. 44; 1.9, p. 35; 1.12, p. 38).
3. `GSpin(U)` and `SO(U)` have the same reduced building, that of the adjoint group `PSO(U)`, with
   `GSpin(U)` acting through `P : GSpin(U) → SO(U)` (Bruhat–Tits, *Groupes réductifs sur un corps
   local II*, Publ. IHÉS 60 (1984), 4.2.15; for groups that are not quasi-split, 5.1.20 Remarque 1,
   and 5.1.29 for the extended building), and the same local Dynkin diagram, hence the same special
   points (Tits 1.12).  The stabilizer of `ℐ × {0}` in the extended building is
   `G(F)¹ = {g : ω(χ(g)) = 0 for all χ ∈ X_F(G)}` (BT II 4.2.16), which is `ker H_G` (`hcG`).
   Hence the special subgroups of `GSpin(U)(F)` are the `{g : H(g) = 0, P(g) ∈ K_SO}` for `K_SO`
   special in `SO(U)(F)`.  This is an identification through general Bruhat–Tits theory (stated
   there for all reductive groups), not a statement about `SO` carried over to `GSpin`.
4. For `R` special, the stabilizer of `R` in `SO(U)(F)` is a special compact subgroup (W1 §7.1,
   arXiv p. 34; **stated there without proof**; W1's hypotheses: `F` non-archimedean of
   characteristic `0`, any residue characteristic, `U` any nondegenerate quadratic space).
5. For `R` adapted to `M`, that stabilizer is in good position relative to `M_min = A·SO(V_an)`
   (W1 §7.2, arXiv pp. 34–35, **stated there without proof**).  W1 §7.2 takes `V = W' ⊕ D ⊕ Z`
   with `D` a line and `Z` hyperbolic with basis `v_{±1}, …, v_{±r}`, and `V₀ = W' ⊕ D`.  If
   `V_an ≠ 0`, apply it with `Z` the span of the whole hyperbolic system, `V₀ = V_an` and `D` any
   anisotropic line of `V_an`; then `M_min = A·SO(V_an)`.  If `V_an = 0` and `n ≥ 1`, apply it with
   `Z` spanned by `v_{±1}, …, v_{±(n−1)}` and `V₀` the plane of `v_{±n}`
   (`D = F(v_n + v_{−n})`, `W' = F(v_n − v_{−n})`, both anisotropic); then `M_min = A`, the torus of
   the whole system.  (If `V = 0` there is nothing to prove.)  In both cases good position holds
   relative to every Levi subgroup containing `A`, by W1's definition
   of good position (§1.1: `K` fixes a special point of the apartment of *some* maximal split torus
   of `M`), and `A ⊆ M` (see `IsAdapted`).

So `K.IsSpecial` implies that `K` is special and in good position relative to `M` in the sense of
W1 §1.1 and Beuzart-Plessis §1.10.  The converse (every special `K` in good position relative to
`M` has this form for `L`'s weight bases) is not printed and is not needed: the predicate is
meant to be used in the "for some and for every such `K`" form, where a smaller non-empty class is
harmless.

## Main results

* `GGPData.specialStab_eq_latticeK`: if `R_W`, `R_V` are the coordinate lattices `Λ_{e_W}`,
  `Λ_{e_V}` and neither `W` nor `V` is a hyperbolic plane, `specialStab = latticeK e_W e_V`.
* `GGPData.pair_scalarGSpin_mem_specialStab`: every special stabilizer contains the scalars of
  norm `1` of `GSpin(W)`; so a `GoodK` without them is not special (`Sanity/GL2SpecialK.lean`).
* `GGPData.exists_goodK_eq_specialStab` (`sorry`): the stabilizer of adapted special lattices is a
  `GoodK`.
* `GGPData.exists_specialK` (`sorry`): every reduced Levi datum has a special `GoodK`.

The checks at `gl2Data` are in `Sanity/GL2SpecialK.lean`: `gl2GoodK` is special, and a `GoodK` of
finite index in it is not.
-/

noncomputable section

open Module

namespace GSpinGGP

section SpecialLattice

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
  {V : Type*} [AddCommGroup V] [Module F V]

/-- **The polar-orthogonal of a hyperbolic system** `(v_i, v'_i)`: the `x` with
`polar Q (v i) x = polar Q (v' i) x = 0` for all `i`. -/
def hypOrth (Q : QuadraticForm F V) {n : ℕ} (v v' : Fin n → V) : Submodule F V :=
  ⨅ i, LinearMap.ker (QuadraticMap.polarBilin Q (v i)) ⊓
    LinearMap.ker (QuadraticMap.polarBilin Q (v' i))

omit [PAdicField F] in
theorem mem_hypOrth {Q : QuadraticForm F V} {n : ℕ} {v v' : Fin n → V} {x : V} :
    x ∈ hypOrth Q v v' ↔ ∀ i, QuadraticMap.polar Q (v i) x = 0 ∧ QuadraticMap.polar Q (v' i) x = 0 := by
  simp [hypOrth, Submodule.mem_iInf, QuadraticMap.polarBilin_apply_apply]

/-- **A special lattice of `(V, Q)`** (Waldspurger 2010, §7.1, arXiv p. 34, "réseaux spéciaux"),
as its data: a hyperbolic system `v i = v_{i+1}`, `v' i = v_{-(i+1)}` (`q(v_i, v_j) = δ_{i,-j}` for
W1's bilinear form `q(·,·) = polar Q`), anisotropic on its orthogonal `V_an = hypOrth Q v v'`, and
`r = |ϖ^c|` (a norm of a nonzero element of `F`) with `‖Q y‖ = r` for some `y ∈ V_an` when
`V_an ≠ 0` (W1: "soit `c ∈ ℤ` tel qu'il existe `v ∈ V_an` pour lequel `val_F(q(v)) = c`"; W1's
`q(v)` is `Q v`).  The lattice itself is `SpecialLattice.R`.  `V = Z ⊕ V_an` with `Z` the span of
the system holds automatically (`polar` is nondegenerate on `Z`). -/
structure SpecialLattice (Q : QuadraticForm F V) where
  /-- the length `n` of the hyperbolic system -/
  n : ℕ
  /-- `v i = v_{i+1}` -/
  v : Fin n → V
  /-- `v' i = v_{-(i+1)}` -/
  v' : Fin n → V
  polar_v_v' : ∀ i j, QuadraticMap.polar Q (v i) (v' j) = if i = j then 1 else 0
  polar_v_v : ∀ i j, QuadraticMap.polar Q (v i) (v j) = 0
  polar_v'_v' : ∀ i j, QuadraticMap.polar Q (v' i) (v' j) = 0
  /-- `q` is anisotropic on `V_an` -/
  aniso : ∀ x ∈ hypOrth Q v v', Q x = 0 → x = 0
  /-- `r = |ϖ^c|` -/
  r : ℝ
  exists_norm_eq : ∃ a : F, a ≠ 0 ∧ ‖a‖ = r
  /-- `c` is a value of `val_F ∘ q` on `V_an` (if `V_an ≠ 0`) -/
  attained : hypOrth Q v v' ≠ ⊥ → ∃ y ∈ hypOrth Q v v', ‖Q y‖ = r

namespace SpecialLattice

variable {Q : QuadraticForm F V} (S : SpecialLattice Q)

/-- `V_an`, the orthogonal of the hyperbolic system. -/
abbrev Van : Submodule F V := hypOrth Q S.v S.v'

/-- **The special lattice** `R = ⟨v_i, ϖ^c v_{-i}⟩_{𝒪_F} ⊕ {y ∈ V_an : val_F(q(y)) ≥ c}`
(W1 §7.1), with `|ϖ^c| = r`: coefficients of norm `≤ 1` on the `v i`, of norm `≤ r` on the
`v' i`, and a `y ∈ V_an` with `‖Q y‖ ≤ r`. -/
def R : Set V :=
  {x | ∃ (a b : Fin S.n → F) (y : V), (∀ i, ‖a i‖ ≤ 1) ∧ (∀ i, ‖b i‖ ≤ S.r) ∧ y ∈ S.Van ∧
    ‖Q y‖ ≤ S.r ∧ x = ∑ i, a i • S.v i + ∑ i, b i • S.v' i + y}

/-- **Adapted to the weight basis `(b, wt)`** (the condition of W1 §7.2 relative to a flag Levi
subgroup): every `v_{±i}` lies in a single weight space `wtSpan b wt w`, and `V_an` lies in the
weight-`0` space.  Then the split torus of the hyperbolic system preserves the weight spaces. -/
def IsAdapted {ι : Type*} (b : Basis ι F V) (wt : ι → ℤ) : Prop :=
  (∀ i, ∃ w, S.v i ∈ wtSpan b wt w) ∧ (∀ i, ∃ w, S.v' i ∈ wtSpan b wt w) ∧
    S.Van ≤ wtSpan b wt 0

end SpecialLattice

variable [Module.Finite F V]

/-- **The stabilizer of a set `R ⊆ V` in `GSpin(V)`**: the `k` with `P(k) R = R`, i.e. `P(k)` and
`P(k)⁻¹` map `R` into itself. -/
def latticeStab (Q : QuadraticForm F V) (R : Set V) : Subgroup (GSpin Q) where
  carrier := {k | Set.MapsTo (specP Q k) R R ∧ Set.MapsTo (specP Q k⁻¹) R R}
  one_mem' := ⟨fun x hx => by rw [map_one]; exact hx,
    fun x hx => by rw [inv_one, map_one]; exact hx⟩
  mul_mem' := fun {k k'} h h' =>
    ⟨fun x hx => by rw [specP_mul_apply]; exact h.1 (h'.1 hx),
      fun x hx => by rw [mul_inv_rev, specP_mul_apply]; exact h'.2 (h.2 hx)⟩
  inv_mem' := fun {k} h => ⟨h.2, by rw [inv_inv]; exact h.1⟩

omit [Module.Finite F V] in
/-- On a coordinate lattice `Λ_e`, `latticeStab` is the `MapsLattice` condition of `latticeSpin`. -/
theorem mem_latticeStab_coord {κ : Type*} (Q : QuadraticForm F V) (e : Basis κ F V) (k : GSpin Q) :
    k ∈ latticeStab Q {x | ∀ i, ‖e.repr x i‖ ≤ 1} ↔
      MapsLattice e (specP Q k : V →ₗ[F] V) ∧ MapsLattice e (specP Q k⁻¹ : V →ₗ[F] V) :=
  Iff.rfl

/-- **Off a hyperbolic plane, `H = 0` is `‖detChar‖ = 1`**: `hcMap` is `log ‖detChar‖` and a
trivial second coordinate. -/
theorem hcMap_eq_one_iff_of_not_isHypPlane {Q : QuadraticForm F V} (hQ : ¬ IsHypPlane Q)
    (k : GSpin Q) : hcMap Q k = 1 ↔ ‖((detChar Q k : Fˣ) : F)‖ = 1 := by
  classical
  rw [hcMap_eq_one_iff]
  have h1 : gspinChar₁ Q = detChar Q := by simp [gspinChar₁, hQ]
  have h2 : gspinChar₂ Q = 1 := by simp [gspinChar₂, hQ]
  simp [h1, h2]

/-- **Scalars of norm one have `H = 0`**: their powers stay in the compact set of scalars of
norm `1`. -/
theorem hcMap_scalarGSpin_eq_one (Q : QuadraticForm F V) {u : Fˣ} (hu : ‖(u : F)‖ = 1) :
    hcMap Q (scalarGSpin Q u) = 1 := by
  refine hcMap_eq_one_of_zpow_mem_compact Q
    (isCompact_unitSphere.image (continuous_scalarGSpin Q)) fun k => ⟨u ^ k, ?_, map_zpow _ _ _⟩
  change ‖((u ^ k : Fˣ) : F)‖ = 1
  rw [Units.val_zpow_eq_zpow_val, norm_zpow, hu, one_zpow]

omit [Module.Finite F V] in
/-- A subset of a family stabilizing a weight-split lattice stabilizes it. -/
theorem _root_.GSpinGGP.GGPData.StabilizesSplitLattice.mono {ι : Type*} {Q : QuadraticForm F V}
    {b : Basis ι F V} {wt : ι → ℤ} {S S' : Set (GSpin Q)}
    (h : GGPData.StabilizesSplitLattice Q b wt S) (hS : S' ⊆ S) :
    GGPData.StabilizesSplitLattice Q b wt S' :=
  let ⟨κ, hκ, e, he, hm⟩ := h
  ⟨κ, hκ, e, he, fun g hg => hm g (hS hg)⟩

end SpecialLattice

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

/-- **The stabilizer of a pair of special lattices in `G`**: the `g ∈ G` with `H_G(g) = 0`
(`hcG g = 1`) such that `P(g)` stabilizes `R_W` and `R_V`.  By the identification in the module
docstring (Tits 3.1, 1.2, 2.1; BT II 4.2.15–16, 5.1.20 Rem. 1, 5.1.29; W1 §7.1) it is a special
maximal compact subgroup of `G(F)`. -/
def specialStab (SW : SpecialLattice d.QW) (SV : SpecialLattice d.QV) : Subgroup ↥d.G :=
  d.hcG.ker ⊓ (latticeStab d.QW SW.R).comap d.fst ⊓ (latticeStab d.QV SV.R).comap d.snd

theorem mem_specialStab {SW : SpecialLattice d.QW} {SV : SpecialLattice d.QV} {g : ↥d.G} :
    g ∈ d.specialStab SW SV ↔
      d.hcG g = 1 ∧ d.fst g ∈ latticeStab d.QW SW.R ∧ d.snd g ∈ latticeStab d.QV SV.R := by
  simp [specialStab, and_assoc]

theorem hcG_eq_one_iff (g : ↥d.G) :
    d.hcG g = 1 ↔ hcMap d.QW (d.fst g) = 1 ∧ hcMap d.QV (d.snd g) = 1 := by
  simp [hcG, Prod.ext_iff]

/-- **`specialStab` of coordinate lattices is `latticeK`** when neither `W` nor `V` is a
hyperbolic plane: then `H_G(g) = 0` is `‖detChar‖ = 1` on both factors. -/
theorem specialStab_eq_latticeK {nW nV : ℕ} (eW : Basis (Fin nW) F (Fin d.m → F))
    (eV : Basis (Fin nV) F d.V) (SW : SpecialLattice d.QW) (SV : SpecialLattice d.QV)
    (hRW : SW.R = {x | ∀ i, ‖eW.repr x i‖ ≤ 1}) (hRV : SV.R = {x | ∀ i, ‖eV.repr x i‖ ≤ 1})
    (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) :
    d.specialStab SW SV = d.latticeK eW eV := by
  ext g
  rw [mem_specialStab, hcG_eq_one_iff, hcMap_eq_one_iff_of_not_isHypPlane hW,
    hcMap_eq_one_iff_of_not_isHypPlane hV, hRW, hRV, mem_latticeStab_coord, mem_latticeStab_coord]
  simp only [latticeK, Subgroup.mem_inf, Subgroup.mem_comap, latticeSpin, Subgroup.mem_mk,
    Submonoid.mem_mk, Subsemigroup.mem_mk]
  change _ ↔ (_ ∧ _ ∧ _) ∧ (_ ∧ _ ∧ _)
  tauto

/-- **Every special stabilizer contains the scalars of norm one of `GSpin(W)`**: they act
trivially on `W` and have `H_G = 0`. -/
theorem pair_scalarGSpin_mem_specialStab (SW : SpecialLattice d.QW) (SV : SpecialLattice d.QV)
    {u : Fˣ} (hu : ‖(u : F)‖ = 1) : d.pair (scalarGSpin d.QW u, 1) ∈ d.specialStab SW SV := by
  rw [mem_specialStab, hcG_eq_one_iff, fst_pair, snd_pair]
  refine ⟨⟨hcMap_scalarGSpin_eq_one d.QW hu, map_one _⟩, ⟨?_, ?_⟩, one_mem _⟩
  · intro x hx; rw [specP_scalarGSpin_eq_one]; exact hx
  · intro x hx; rw [← map_inv, specP_scalarGSpin_eq_one]; exact hx

variable {d}

/-- **`K` is special maximal compact, in good position relative to `M`**, in W1's lattice form
(Waldspurger 2010, §7.1–7.2, arXiv pp. 34–35): `K` *equals* the stabilizer `specialStab S_W S_V`
of special lattices `R_W`, `R_V` of `W` and `V` adapted to the weight bases of `L`
(`SpecialLattice.IsAdapted`), i.e.
`K = {g : H_G(g) = 0, P(g) R_W = R_W, P(g) R_V = R_V}`.

Sources and identification steps (written out in the module docstring):
* special subgroups are stabilizers of special points of the extended building, and are maximal
  compact (Tits, Corvallis, 3.1, 1.2, 3.2);
* product: special in `G` is special in each factor (Tits 2.1, 1.9, 1.12);
* `GSpin(U)` versus `SO(U)`: same reduced building and special points, `G(F)¹ = ker H_G`
  (Bruhat–Tits II, 4.2.15–16, 5.1.20 Remarque 1 for non-quasi-split `U`, 5.1.29; Tits 1.12): an
  identification through general Bruhat–Tits theory;
* the stabilizer in `SO(U)(F)` of a special lattice is special (W1 §7.1, **stated without proof**
  there; any residue characteristic);
* for adapted lattices it is in good position relative to `A·SO(U_an)`, hence relative to `M ⊇ A`
  (W1 §7.2, **stated without proof** there; W1 §1.1 for the definition).

Only "lattice form ⇒ special in good position" is used; the converse is neither printed nor
needed.  Checks: `gl2GoodK` is special, and a smaller `GoodK` is not
(`Sanity/GL2SpecialK.lean`). -/
def GoodK.IsSpecial {L : d.FlagLeviDatum} (K : d.GoodK L) : Prop :=
  ∃ (SW : SpecialLattice d.QW) (SV : SpecialLattice d.QV),
    SW.IsAdapted L.bW L.wtW ∧ SV.IsAdapted L.bV L.wtV ∧ K.K = d.specialStab SW SV

/-- A special `K` lies in `ker H_G`. -/
theorem GoodK.IsSpecial.le_ker_hcG {L : d.FlagLeviDatum} {K : d.GoodK L} (hK : K.IsSpecial) :
    K.K ≤ d.hcG.ker := by
  obtain ⟨SW, SV, -, -, hK⟩ := hK
  rw [hK]
  exact fun g hg => (d.mem_specialStab.1 hg).1

/-- A special `K` contains the scalars of norm one of `GSpin(W)`. -/
theorem GoodK.IsSpecial.pair_scalarGSpin_mem {L : d.FlagLeviDatum} {K : d.GoodK L}
    (hK : K.IsSpecial) {u : Fˣ} (hu : ‖(u : F)‖ = 1) : d.pair (scalarGSpin d.QW u, 1) ∈ K.K := by
  obtain ⟨SW, SV, -, -, hK⟩ := hK
  rw [hK]
  exact d.pair_scalarGSpin_mem_specialStab SW SV hu

/-- **The stabilizer of adapted special lattices is a `GoodK`** (not yet proved).

Sketch, field by field, for `K₀ = specialStab S_W S_V`:
* *compact open*: `R_an = {y ∈ V_an : ‖Q y‖ ≤ r}` is an `𝒪_F`-lattice of `V_an` (W1 §7.1; for an
  anisotropic form over a local field, `y ↦ ‖Q y‖^{1/2}` is an ultrametric norm), so `R` is a
  lattice `Λ_e` for a basis `e` made of the `v_i`, scalar multiples of the `v'_i`, and a basis of
  `R_an`.  The stabilizer of `Λ_e` is open; its image in `SO` is bounded, and `H_G = 0` bounds the
  central part (as for `latticeK`, `isCompact_latticeK`; for a hyperbolic-plane factor use
  `isCompact_splitCentral_inter_ker_hcMap`);
* *good position*: the basis `e` above lies in weight spaces (`IsAdapted`; `R_an ⊆ V_an` is in
  weight `0`);
* *`G = P K₀` for `P ∈ 𝒫(M)`*: Iwasawa decomposition for a special subgroup fixing a special point
  of the apartment of a maximal split torus `A ⊆ M ⊆ P` (Tits, Corvallis, 3.3.2, as in
  `tits_iwasawa`), through the identification of the module docstring. -/
theorem exists_goodK_eq_specialStab (L : d.FlagLeviDatum) (SW : SpecialLattice d.QW)
    (SV : SpecialLattice d.QV) (hW : SW.IsAdapted L.bW L.wtW) (hV : SV.IsAdapted L.bV L.wtV) :
    ∃ K : d.GoodK L, K.K = d.specialStab SW SV := by
  sorry

/-- **Every reduced Levi datum has a special `GoodK`** (not yet proved).

Sketch.  By `exists_goodK_eq_specialStab` it suffices to find special lattices of `W` and `V`
adapted to the weight bases of `L`.  For `U = W` or `V` with splitting `(b, wt)`: for each weight
`w > 0`, the weight spaces `X_w` and `X_{−w}` are in duality under `polar` (the splitting is
isotropic and orthogonal across weights not summing to `0`, `IsFlagSplitting`), so choose dual
bases `v_i ∈ X_w`, `v'_i ∈ X_{−w}`; in the nondegenerate weight-`0` space `X_0` choose a Witt
decomposition `X_0 = Z_0 ⊕ U_an` with a hyperbolic basis of `Z_0` and `U_an` anisotropic.  These
vectors form a hyperbolic system whose orthogonal is `U_an ⊆ X_0`; take `r = ‖Q y‖` for any
nonzero `y ∈ U_an`, or `r = 1` if `U_an = 0`. -/
theorem exists_specialK (L : d.ReducedLeviDatum) :
    ∃ K : d.GoodK L.toFlagLeviDatum, K.IsSpecial := by
  sorry

end GGPData

end GSpinGGP
