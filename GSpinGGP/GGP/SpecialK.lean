/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.SpecialLattice
import GSpinGGP.Literature.SpecialKIwasawa

/-!
# Special maximal compact subgroups in good position, in lattice form

Waldspurger (*Une formule intégrale reliée à la conjecture locale de Gross–Prasad*, Compositio
Math. 146 (2010); "W1", cited with the pagination of arXiv:0902.1875v1) and Beuzart-Plessis
(Astérisque 418, §1.10, §5.2) define `θ_f` with a **special** maximal compact subgroup `K` in good
position relative to a Levi subgroup `M`.  For orthogonal groups W1 describes these subgroups by
lattices (§7.1, arXiv p. 34; §7.2, arXiv pp. 34–35).  This file transcribes that description to
`G = GSpin(W) × GSpin(V)` and a flag Levi datum `L`.

The special lattices of W1 §7.1 (`SpecialLattice`), the condition `SpecialLattice.IsAdapted` and
the stabilizer `GGPData.specialStab` are defined in `GGP/SpecialLattice.lean`, below the
literature axiom `tits_iwasawa_specialStab` (`Literature/SpecialKIwasawa.lean`) that this file
uses.

## The predicate

* `GGPData.GoodK.IsSpecial K`: `K` **equals** `specialStab S_W S_V` (defined in
  `GGP/SpecialLattice.lean`, with `SpecialLattice.IsAdapted`) for special lattices adapted to `L`.

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
* `GGPData.isOpen_specialStab`, `GGPData.isCompact_specialStab`: for coordinate lattices.
* `GGPData.pair_scalarGSpin_mem_specialStab`: every special stabilizer contains the scalars of
  norm `1` of `GSpin(W)`.
* `GGPData.exists_goodK_eq_specialStab`: the stabilizer of adapted special lattices is a `GoodK`,
  from `SpecialLattice.exists_basis_R_eq` (`sorry`, own work: an adapted special lattice is a
  coordinate lattice of a basis made of vectors of weight spaces) and the literature axiom
  `tits_iwasawa_specialStab` (the Iwasawa decomposition `G = P K` for `P ∈ 𝒫(M)`: Tits,
  Corvallis, 3.3.2 and Waldspurger 2003, p. 240, applied through W1 §7.1–7.2 and the
  identification above).
* `GGPData.exists_specialK` (`sorry`): every reduced Levi datum has a special `GoodK`.  It is on
  the path of `local_ggp` (through `thetaF`, `TraceFormula/ThetaFGlobal.lean`), which relies on
  the existence of special presentations.

The checks at `gl2Data` are in `Sanity/GL2SpecialK.lean`: `gl2GoodK` is special; a `GoodK` of
finite index in it is not; the lattice `⟨z₋₁, z₀, ϖ · ½ z₁⟩` (for `ϖ` a uniformizer, that of an
edge midpoint of the tree) is not a special lattice; and the lattice `⟨z₋₁, ϖ z₀, ϖ · ½ z₁⟩`
(stabilizer the normalizer of an Iwahori subgroup: standard for `PGL₂`, not formalized here)
satisfies every condition except `attained` and is excluded by `attained`
(`not_exists_specialLattice_R_eq_iwahori`).
-/

noncomputable section

open Module

namespace GSpinGGP

section SpecialLattice

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
  {V : Type*} [AddCommGroup V] [Module F V]

/-- **A special lattice adapted to `(b, wt)` is a coordinate lattice `Λ_e` for a basis `e` made of
vectors of weight spaces** (not yet proved; own work).

This is W1 §7.1's "C'est un `𝒪_F`-réseau de `V_an`" (stated there without proof) together with the
splitting `V = Z ⊕ V_an`.  Sketch: `polar` is nondegenerate on `Z = span(v_i, v'_i)` (the Gram
matrix is `[[0, 1], [1, 0]]` blockwise), so `V = Z ⊕ V_an`.  For `Q` anisotropic on `V_an` over a
non-archimedean local field, `R_an = {y ∈ V_an : ‖Q y‖ ≤ r}` is a bounded open `𝒪_F`-submodule
(O'Meara, *Introduction to quadratic forms*, 91:1: the norms of an anisotropic space form a
lattice; closure under addition is the ultrametric inequality for `y ↦ ‖Q y‖^{1/2}`), hence free
with a basis `f_j ∈ V_an ⊆ wtSpan 0`.  Take `e = (v_i, a • v'_i, f_j)` with `‖a‖ = r`; the
`v_i`, `v'_i` lie in weight spaces by `IsAdapted`. -/
theorem SpecialLattice.exists_basis_R_eq [Module.Finite F V] {Q : QuadraticForm F V}
    (S : SpecialLattice Q) {ι : Type*} {b : Basis ι F V} {wt : ι → ℤ} (hS : S.IsAdapted b wt) :
    ∃ (k : ℕ) (e : Basis (Fin k) F V), (∀ i, ∃ w, e i ∈ wtSpan b wt w) ∧
      S.R = {x | ∀ i, ‖e.repr x i‖ ≤ 1} := by
  sorry

/-- **The stabilizer of `Λ_e` with `H = 0` is compact**, given that `latticeSpin Q e` is: off a
hyperbolic plane the two groups are equal (`H = 0` is `‖detChar‖ = 1`); on a hyperbolic plane
`GSpin` is its own split centre and `ker H` is compact
(`isCompact_splitCentral_inter_ker_hcMap`). -/
theorem isCompact_latticeStab_inf_ker_hcMap [Module.Finite F V] {κ : Type*} [Finite κ]
    [TopologicalSpace V] [IsModuleTopology F V] (Q : QuadraticForm F V) (e : Basis κ F V)
    (hK : IsCompact (latticeSpin Q e : Set (GSpin Q))) :
    IsCompact ((latticeStab Q {x | ∀ i, ‖e.repr x i‖ ≤ 1} ⊓ (hcMap Q).ker : Subgroup (GSpin Q)) :
      Set (GSpin Q)) := by
  classical
  by_cases hQ : IsHypPlane Q
  · have hopen : IsOpen ((latticeStab Q {x | ∀ i, ‖e.repr x i‖ ≤ 1} ⊓ (hcMap Q).ker :
        Subgroup (GSpin Q)) : Set (GSpin Q)) := by
      refine Subgroup.isOpen_mono (H₁ := latticeSpin Q e ⊓ (hcMap Q).ker) ?_ ?_
      · exact fun k hk => ⟨(mem_latticeSpin_iff_mem_latticeStab.1 hk.1).1, hk.2⟩
      · exact (isClopen_latticeSpin Q e).isOpen.inter ((isLocallyConstant_hcMap Q).isOpen_fiber 1)
    refine (isCompact_splitCentral_inter_ker_hcMap Q).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ hopen) fun k hk => ⟨by simp [splitCentralGSpin, hQ], hk.2⟩
  · convert hK using 2
    ext k
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, mem_latticeSpin_iff_mem_latticeStab,
      hcMap_eq_one_iff_of_not_isHypPlane hQ]

end SpecialLattice

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

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

/-- **`latticeSpin` of `W` is compact**: it is the image of `latticeK` under `g ↦ g_W`. -/
theorem isCompact_latticeSpin_W {nW : ℕ} (eW : Basis (Fin nW) F (Fin d.m → F)) :
    IsCompact (latticeSpin d.QW eW : Set (GSpin d.QW)) := by
  have h := (d.isCompact_latticeK eW (Module.finBasis F d.V)).image d.continuous_fst
  convert h using 1
  ext k
  refine ⟨fun hk => ⟨d.pair (k, 1),
    ⟨show d.fst (d.pair (k, 1)) ∈ latticeSpin _ _ by rw [d.fst_pair]; exact hk,
      show d.snd (d.pair (k, 1)) ∈ latticeSpin _ _ by rw [d.snd_pair]; exact one_mem _⟩,
    d.fst_pair _⟩, ?_⟩
  rintro ⟨g, hg, rfl⟩
  exact hg.1

/-- **`latticeSpin` of `V` is compact**: it is the image of `latticeK` under `g ↦ g_V`. -/
theorem isCompact_latticeSpin_V {nV : ℕ} (eV : Basis (Fin nV) F d.V) :
    IsCompact (latticeSpin d.QV eV : Set (GSpin d.QV)) := by
  have h := (d.isCompact_latticeK (Module.finBasis F (Fin d.m → F)) eV).image d.continuous_snd
  convert h using 1
  ext k
  refine ⟨fun hk => ⟨d.inr k, d.inr_mem_latticeK _ _ hk, d.snd_inr _⟩, ?_⟩
  rintro ⟨g, hg, rfl⟩
  exact hg.2

/-- **`specialStab` of coordinate lattices is open**: it contains the open subgroup
`latticeK ∩ ker H_G`. -/
theorem isOpen_specialStab {nW nV : ℕ} (eW : Basis (Fin nW) F (Fin d.m → F))
    (eV : Basis (Fin nV) F d.V) (SW : SpecialLattice d.QW) (SV : SpecialLattice d.QV)
    (hRW : SW.R = {x | ∀ i, ‖eW.repr x i‖ ≤ 1}) (hRV : SV.R = {x | ∀ i, ‖eV.repr x i‖ ≤ 1}) :
    IsOpen (d.specialStab SW SV : Set ↥d.G) := by
  refine Subgroup.isOpen_mono (H₁ := d.latticeK eW eV ⊓ d.hcG.ker) (fun g hg => ?_)
    ((d.isOpen_latticeK eW eV).inter (d.isLocallyConstant_hcG.isOpen_fiber 1))
  rw [mem_specialStab, hRW, hRV]
  exact ⟨hg.2, (mem_latticeSpin_iff_mem_latticeStab.1 hg.1.1).1,
    (mem_latticeSpin_iff_mem_latticeStab.1 hg.1.2).1⟩

/-- **`specialStab` of coordinate lattices is compact**: it lies in the image under `pair` of the
product of the compact factor sets `latticeStab ∩ ker H` (`isCompact_latticeStab_inf_ker_hcMap`),
and it is closed (open subgroup). -/
theorem isCompact_specialStab {nW nV : ℕ} (eW : Basis (Fin nW) F (Fin d.m → F))
    (eV : Basis (Fin nV) F d.V) (SW : SpecialLattice d.QW) (SV : SpecialLattice d.QV)
    (hRW : SW.R = {x | ∀ i, ‖eW.repr x i‖ ≤ 1}) (hRV : SV.R = {x | ∀ i, ‖eV.repr x i‖ ≤ 1}) :
    IsCompact (d.specialStab SW SV : Set ↥d.G) := by
  have hc := ((isCompact_latticeStab_inf_ker_hcMap d.QW eW (d.isCompact_latticeSpin_W eW)).prod
    (isCompact_latticeStab_inf_ker_hcMap d.QV eV (d.isCompact_latticeSpin_V eV))).image
      d.continuous_pair
  refine hc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _
    (d.isOpen_specialStab eW eV SW SV hRW hRV)) fun g hg => ?_
  rw [SetLike.mem_coe, mem_specialStab, hcG_eq_one_iff, hRW, hRV] at hg
  exact ⟨(d.fst g, d.snd g), ⟨⟨hg.2.1, hg.1.1⟩, ⟨hg.2.2, hg.1.2⟩⟩, d.pair_fst_snd g⟩

/-- **The stabilizer of adapted special lattices is a `GoodK`.**  `R_W`, `R_V` are coordinate
lattices of bases made of vectors of weight spaces (`SpecialLattice.exists_basis_R_eq`); hence
`specialStab` is open and compact (`isOpen_specialStab`, `isCompact_specialStab`) and in good
position; `G = P K` is the literature axiom `tits_iwasawa_specialStab`. -/
theorem exists_goodK_eq_specialStab (L : d.FlagLeviDatum) (SW : SpecialLattice d.QW)
    (SV : SpecialLattice d.QV) (hW : SW.IsAdapted L.bW L.wtW) (hV : SV.IsAdapted L.bV L.wtV) :
    ∃ K : d.GoodK L, K.K = d.specialStab SW SV := by
  obtain ⟨nW, eW, heW, hRW⟩ := SW.exists_basis_R_eq hW
  obtain ⟨nV, eV, heV, hRV⟩ := SV.exists_basis_R_eq hV
  refine ⟨{ K := d.specialStab SW SV
            isOpen := d.isOpen_specialStab eW eV SW SV hRW hRV
            isCompact := d.isCompact_specialStab eW eV SW SV hRW hRV
            mul_eq := tits_iwasawa_specialStab d L SW SV hW hV
            goodPositionW := ⟨Fin nW, inferInstance, eW, heW, ?_⟩
            goodPositionV := ⟨Fin nV, inferInstance, eV, heV, ?_⟩ }, rfl⟩
  · rintro _ ⟨g, hg, rfl⟩
    have h := (d.mem_specialStab.1 hg).2.1
    rw [hRW, mem_latticeStab_coord] at h
    exact h.1
  · rintro _ ⟨g, hg, rfl⟩
    have h := (d.mem_specialStab.1 hg).2.2
    rw [hRV, mem_latticeStab_coord] at h
    exact h.1

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
