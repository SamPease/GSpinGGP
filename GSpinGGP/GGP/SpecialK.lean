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

* `hypOrth_eq_orthogonal`: `V_an` is the `bform`-orthogonal of the span of the system.
* `SpecialLattice.norm_quadForm_le`: `‖q(x)‖ ≤ |ϖ^c|` on a special lattice.
* `GGPData.specialStab_eq_latticeK`: if `R_W`, `R_V` are the coordinate lattices `Λ_{e_W}`,
  `Λ_{e_V}` and neither `W` nor `V` is a hyperbolic plane, `specialStab = latticeK e_W e_V`.
* `GGPData.isOpen_specialStab`, `GGPData.isCompact_specialStab`: for coordinate lattices.
* `GGPData.pair_scalarGSpin_mem_specialStab`: every special stabilizer contains the scalars of
  norm `1` of `GSpin(W)`.
* `GGPData.exists_goodK_eq_specialStab`: the stabilizer of adapted special lattices is a `GoodK`,
  from two statements not proved here:
  - `SpecialLattice.exists_basis_R_eq` (`sorry`, own work): an adapted special lattice is a
    coordinate lattice of a basis made of vectors of weight spaces;
  - `GGPData.specialStab_mul_eq` (`sorry`): the Iwasawa decomposition `G = P K` for `P ∈ 𝒫(M)`,
    a composite of printed results (W1 §7.1–7.2, Tits 3.3.2, Bruhat–Tits) that cannot be proved
    from the repository's own material and is to become a literature axiom.
* `GGPData.exists_specialK` (`sorry`): every reduced Levi datum has a special `GoodK`.

The checks at `gl2Data` are in `Sanity/GL2SpecialK.lean`: `gl2GoodK` is special; a `GoodK` of
finite index in it is not; and the lattice `⟨z₋₁, z₀, ϖ · ½ z₁⟩` (for `ϖ` a uniformizer, that of an
edge midpoint of the tree) is not a special lattice.  No check yet exercises the condition
`attained`.
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
    x ∈ hypOrth Q v v' ↔
      ∀ i, QuadraticMap.polar Q (v i) x = 0 ∧ QuadraticMap.polar Q (v' i) x = 0 := by
  simp [hypOrth, Submodule.mem_iInf, QuadraticMap.polarBilin_apply_apply]

omit [PAdicField F] in
/-- **`hypOrth` is the `bform`-orthogonal of the span of the system** (`polar = 2 bform`). -/
theorem hypOrth_eq_orthogonal [Invertible (2 : F)] (Q : QuadraticForm F V) {n : ℕ}
    (v v' : Fin n → V) :
    hypOrth Q v v' = (bform Q).orthogonal (Submodule.span F (Set.range v ∪ Set.range v')) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero' F
  ext x
  rw [mem_hypOrth, LinearMap.BilinForm.mem_orthogonal_iff]
  simp only [polar_eq_two_mul_bform, mul_eq_zero, h2, false_or]
  constructor
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact (h i).1
      · exact (h i).2
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul a y _ hy => simp [hy]
  · exact fun h i => ⟨h _ (Submodule.subset_span (Or.inl ⟨i, rfl⟩)),
      h _ (Submodule.subset_span (Or.inr ⟨i, rfl⟩))⟩

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

omit [PAdicField F] in
/-- `Q` vanishes on a combination of pairwise `polar`-orthogonal isotropic vectors. -/
theorem _root_.GSpinGGP.quadForm_sum_smul_eq_zero {ι : Type*} {Q : QuadraticForm F V}
    {f : ι → V} (hf : ∀ i, Q (f i) = 0) (ho : ∀ i j, QuadraticMap.polar Q (f i) (f j) = 0)
    (c : ι → F) (s : Finset ι) : Q (∑ i ∈ s, c i • f i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, QuadraticMap.map_add (⇑Q), ih, QuadraticMap.map_smul, hf,
      QuadraticMap.polar_smul_left, ← QuadraticMap.polarBilin_apply_apply, map_sum]
    simp [QuadraticMap.polarBilin_apply_apply, ho]

/-- The vectors of a hyperbolic system are isotropic. -/
theorem quadForm_v (i : Fin S.n) : Q (S.v i) = 0 := by
  have h := S.polar_v_v i i
  rw [QuadraticMap.polar_self, two_nsmul, ← two_mul, mul_eq_zero] at h
  exact h.resolve_left two_ne_zero

theorem quadForm_v' (i : Fin S.n) : Q (S.v' i) = 0 := by
  have h := S.polar_v'_v' i i
  rw [QuadraticMap.polar_self, two_nsmul, ← two_mul, mul_eq_zero] at h
  exact h.resolve_left two_ne_zero

omit [PAdicField F] in
theorem r_nonneg : 0 ≤ S.r := by
  obtain ⟨a, -, ha⟩ := S.exists_norm_eq; rw [← ha]; exact norm_nonneg a

/-- **`val_F(q) ≥ c` on a special lattice**: `‖Q x‖ ≤ r` for `x ∈ R` (W1 §7.1:
`q(Σ a_i v_i + Σ b_i ϖ^c v_{-i} + y) = Σ a_i b_i ϖ^c + q(y)`). -/
theorem norm_quadForm_le {x : V} (hx : x ∈ S.R) : ‖Q x‖ ≤ S.r := by
  obtain ⟨a, b, y, ha, hb, hy, hQy, rfl⟩ := hx
  have hA : Q (∑ i, a i • S.v i) = 0 :=
    quadForm_sum_smul_eq_zero S.quadForm_v S.polar_v_v a _
  have hB : Q (∑ i, b i • S.v' i) = 0 :=
    quadForm_sum_smul_eq_zero S.quadForm_v' S.polar_v'_v' b _
  have hAB : QuadraticMap.polar Q (∑ i, a i • S.v i) (∑ i, b i • S.v' i) = ∑ i, a i * b i := by
    rw [show QuadraticMap.polar Q (∑ i, a i • S.v i) (∑ i, b i • S.v' i) =
      QuadraticMap.polarBilin Q (∑ i, a i • S.v i) (∑ i, b i • S.v' i) from rfl]
    simp [map_sum, LinearMap.sum_apply, QuadraticMap.polarBilin_apply_apply, S.polar_v_v',
      mul_comm]
  have hy' : ∀ z ∈ Submodule.span F (Set.range S.v ∪ Set.range S.v'),
      QuadraticMap.polar Q z y = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rw [mem_hypOrth] at hy
      rcases hz with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact (hy i).1
      · exact (hy i).2
    | zero => simp
    | add z w _ _ hz hw => rw [QuadraticMap.polar_add_left, hz, hw, add_zero]
    | smul c z _ hz => rw [QuadraticMap.polar_smul_left, hz, smul_zero]
  have hmem : ∑ i, a i • S.v i + ∑ i, b i • S.v' i ∈
      Submodule.span F (Set.range S.v ∪ Set.range S.v') :=
    add_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨i, rfl⟩)))
      (sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨i, rfl⟩)))
  rw [QuadraticMap.map_add (⇑Q), hy' _ hmem, add_zero, QuadraticMap.map_add (⇑Q), hA, hB, hAB,
    zero_add, zero_add]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hQy)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg S.r_nonneg fun i _ => ?_
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (ha i)).trans (hb i)

end SpecialLattice

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

/-- **Iwasawa decomposition `G = P K₀` for the stabilizer of adapted special lattices** (not
provable in this repository; to become a literature axiom).

`K₀ = specialStab S_W S_V` is special and fixes a special point of the apartment of the split torus
`A ⊆ M` of the hyperbolic systems (W1 §7.1–7.2, stated without proof there, through the
identification of the module docstring: Tits, Corvallis, 3.1, 1.2, 2.1, 1.12; BT II 4.2.15–16,
5.1.20 Rem. 1, 5.1.29).  For every parabolic `P ⊇ A`, `G(F) = P(F) K₀` (Tits, Corvallis, 3.3.2;
compare `tits_iwasawa`).  Each `P ∈ 𝒫(M)` contains `M ⊇ A`.  This is a composite of printed
results with identification steps only; it is to be stated as an axiom of `Literature/` (with
those steps in its docstring) before `exists_specialK` comes onto the path of `local_ggp`. -/
theorem specialStab_mul_eq (L : d.FlagLeviDatum) (SW : SpecialLattice d.QW)
    (SV : SpecialLattice d.QV) (hW : SW.IsAdapted L.bW L.wtW) (hV : SV.IsAdapted L.bV L.wtV) :
    ∀ P ∈ d.parabolics L.M, ∀ g : ↥d.G, ∃ p ∈ P, ∃ k ∈ d.specialStab SW SV, g = p * k := by
  sorry

/-- **The stabilizer of adapted special lattices is a `GoodK`.**  `R_W`, `R_V` are coordinate
lattices of bases made of vectors of weight spaces (`SpecialLattice.exists_basis_R_eq`); hence
`specialStab` is open and compact (`isOpen_specialStab`, `isCompact_specialStab`) and in good
position; `G = P K` is `specialStab_mul_eq`. -/
theorem exists_goodK_eq_specialStab (L : d.FlagLeviDatum) (SW : SpecialLattice d.QW)
    (SV : SpecialLattice d.QV) (hW : SW.IsAdapted L.bW L.wtW) (hV : SV.IsAdapted L.bV L.wtV) :
    ∃ K : d.GoodK L, K.K = d.specialStab SW SV := by
  obtain ⟨nW, eW, heW, hRW⟩ := SW.exists_basis_R_eq hW
  obtain ⟨nV, eV, heV, hRV⟩ := SV.exists_basis_R_eq hV
  refine ⟨{ K := d.specialStab SW SV
            isOpen := d.isOpen_specialStab eW eV SW SV hRW hRV
            isCompact := d.isCompact_specialStab eW eV SW SV hRW hRV
            mul_eq := d.specialStab_mul_eq L SW SV hW hV
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
