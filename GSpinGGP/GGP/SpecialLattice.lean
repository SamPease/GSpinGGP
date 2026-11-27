/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.LatticeK

/-!
# Special lattices (Waldspurger 2010, §7.1) and their stabilizer in `G`

The definitions behind `GGP/SpecialK.lean`, kept in a file of their own so that the
literature axiom `tits_iwasawa_specialStab` (`Literature/SpecialKIwasawa.lean`) can be stated
about them and imported by `GGP/SpecialK.lean`.

## W1's special lattices (§7.1)

Waldspurger (*Une formule intégrale reliée à la conjecture locale de Gross–Prasad*, Compositio
Math. 146 (2010); "W1", cited with the pagination of arXiv:0902.1875v1), §7.1, arXiv p. 34.
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
lattices; inside one definition the convention is used consistently.  One direction is proved in
`TraceFormula/SpecialLatticeBridge.lean` (`SpecialLattice.isSpecialLattice`: `S.R` satisfies
`IsSpecialLattice Q ϖ` for every uniformizer `ϖ`).

## Main definitions

* `SpecialLattice Q`, `SpecialLattice.R`: the data of W1 §7.1 and the lattice `R`.
* `SpecialLattice.IsAdapted b wt`: each `v_{±i}` lies in one weight space of `(b, wt)` and
  `V_an` lies in the weight-`0` space.  Then the split torus `A` of the hyperbolic system
  (acting by `t_i` on `v_i`, `t_i⁻¹` on `v_{-i}`, trivially on `V_an`) preserves every weight space,
  so `A ⊆ M` (`M` is the stabilizer of the weight spaces, `mem_flagLevi_iff`).
* `GGPData.specialStab S_W S_V`: the `g ∈ G` with `H_G(g) = 0` (`hcG g = 1`) such that `P(g)`
  stabilizes `R_W` and `R_V` (`latticeStab`).

## Main results

* `hypOrth_eq_orthogonal`: `V_an` is the `bform`-orthogonal of the span of the system.
* `SpecialLattice.norm_quadForm_le`: `‖q(x)‖ ≤ |ϖ^c|` on a special lattice.
* `SpecialLattice.sub_sum_mem_Van`: `V = Z ⊕ V_an`.
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

omit [PAdicField F] in
theorem polar_v'_v (i j : Fin S.n) :
    QuadraticMap.polar Q (S.v' i) (S.v j) = if j = i then 1 else 0 := by
  rw [QuadraticMap.polar_comm, S.polar_v_v']

omit [PAdicField F] in
/-- **`V = Z ⊕ V_an`**: `x − Σ polar(x, v'_k) v_k − Σ polar(x, v_k) v'_k ∈ V_an`. -/
theorem sub_sum_mem_Van (x : V) :
    x - (∑ k, QuadraticMap.polar Q x (S.v' k) • S.v k +
      ∑ k, QuadraticMap.polar Q x (S.v k) • S.v' k) ∈ S.Van := by
  rw [mem_hypOrth]
  intro j
  simp only [← QuadraticMap.polarBilin_apply_apply, map_sub, map_add, map_sum, map_smul,
    smul_eq_mul]
  simp only [QuadraticMap.polarBilin_apply_apply, S.polar_v_v, S.polar_v_v', S.polar_v'_v,
    S.polar_v'_v', mul_zero, Finset.sum_const_zero, mul_ite, mul_one, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, zero_add, add_zero]
  constructor <;> rw [QuadraticMap.polar_comm] <;> ring

end SpecialLattice

end SpecialLattice

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

/-- **The stabilizer of a pair of special lattices in `G`**: the `g ∈ G` with `H_G(g) = 0`
(`hcG g = 1`) such that `P(g)` stabilizes `R_W` and `R_V`.  By the identification written out
in steps 1–4 of `tits_iwasawa_specialStab` (`Literature/SpecialKIwasawa.lean`; Tits 3.1, 1.2, 2.1;
BT II 4.2.15–16, 5.1.20 Rem. 1, 5.1.29; W1 §7.1) it is the fixer of a special point of the
extended building, a special maximal compact subgroup of `G(F)`. -/
def specialStab (SW : SpecialLattice d.QW) (SV : SpecialLattice d.QV) : Subgroup ↥d.G :=
  d.hcG.ker ⊓ (latticeStab d.QW SW.R).comap d.fst ⊓ (latticeStab d.QV SV.R).comap d.snd

theorem mem_specialStab {SW : SpecialLattice d.QW} {SV : SpecialLattice d.QV} {g : ↥d.G} :
    g ∈ d.specialStab SW SV ↔
      d.hcG g = 1 ∧ d.fst g ∈ latticeStab d.QW SW.R ∧ d.snd g ∈ latticeStab d.QV SV.R := by
  simp [specialStab, and_assoc]

theorem hcG_eq_one_iff (g : ↥d.G) :
    d.hcG g = 1 ↔ hcMap d.QW (d.fst g) = 1 ∧ hcMap d.QV (d.snd g) = 1 := by
  simp [hcG, Prod.ext_iff]

end GGPData

end GSpinGGP
