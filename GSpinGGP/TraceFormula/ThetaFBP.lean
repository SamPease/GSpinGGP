/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.RegularCentralizer
import GSpinGGP.TraceFormula.RegularSetAG
import GSpinGGP.GGP.LatticeK

/-!
# Beuzart-Plessis' `θ_f` by its formula

For a strongly cuspidal `f` and `x ∈ G_reg(F)`, Beuzart-Plessis (Astérisque 418, §5.2, p. 109;
Waldspurger, Compos. Math. 146 (2010), §5.3) sets
`θ_f(x) = (−1)^{a_G − a_{M(x)}} ν(G_x)⁻¹ D^G(x)^{−1/2} J_{M(x)}(x, f)`,
where `M(x)` is the centralizer of `A_{G_x}`, the maximal split central torus of the torus `G_x`
(the minimal Levi subgroup containing `x`), and `ν(G_x)` is defined by `d_c t = ν(G_x) dt`
(Beuzart-Plessis §1.6, p. 30).  This file defines that function, `thetaFBP`, for a given Levi datum
`L` with `L.M = M(x)` and a good compact subgroup `K`; `thetaF` (`TraceFormula/ThetaFGlobal.lean`)
evaluates it at every regular `x` for a chosen special presentation of `M(x)`.  At the toy datum
see `toyD_thetaF_eq_thetaFBP` (`Sanity/ToyThetaF.lean`).

**`M(x)` and `A_{G_x}`.**  The Levi subgroup is an input: `IsMx L x` says that `x ∈ G_reg(F)`,
`x ∈ M(F)`, and `G_x(F)` is compact modulo `A_M(F)`, i.e. `x` is elliptic in `M`.  For a Levi
subgroup `M ∋ x` one has `G_x ⊆ M` (`centG_le_M`) and `A_M ⊆ A_{G_x}`, and `M = M(x)` iff
`A_M = A_{G_x}` iff `G_x / A_M` is anisotropic iff `G_x(F)/A_M(F)` is compact; so `IsMx L x` says
`L.M = M(x)`, and then `A_{G_x}(F) = A_M(F)` (`AGx`).

**The measure `d_c t`** (Beuzart-Plessis §1.6): `d_c a` is the Haar measure on `A_{G_x}(F)` giving
its maximal compact subgroup measure `1`, and `d_c t` the Haar measure on `G_x(F)` for which the
quotient measure `d_c t / d_c a` gives `G_x(F)/A_{G_x}(F)` measure `1` (`IsDcMeasure`, `dcMeasure`).
The maximal compact subgroup of the split torus `A_M(F)` is taken as `A_M(F) ∩ ker H_M` (`AGxOne`):
`H_M` restricted to `A_M(F)` has image a lattice of full rank in `a_M` (`span_HMAMF_eq_top`,
`exists_HM_mem_zmultiples`), so its kernel is `A_M(O)`, the maximal compact subgroup.
Since `J_M(x, f)` scales by `c⁻¹` when the measure on `G_x(F)` is multiplied by `c`
(`weightedOrbitalIntegral_smul_measure`), `ν(G_x)⁻¹ J_M(x, f; dt) = J_M(x, f; d_c t)`: `thetaFBP`
uses `d_c t` and has no separate factor `ν`.

**Normalizations that differ from the source.**
* `dg` on `G(F)` is `Measure.haar`, not Beuzart-Plessis' measure (defined through the exponential
  map and an autodual measure on `𝔤(F)`).  If `Measure.haar = c_G · dg_BP` (`c_G > 0`), then
  `thetaFBP = c_G · θ_f` (`θ_f` is linear in `dg` through the quotient measure); statements
  comparing with the sources must carry `c_G`.  `d_c t` itself is canonical and needs no
  comparison.
* `K` is a `GoodK` (compact open, `G = P K` for `P ∈ 𝒫(M)`, good position), where Beuzart-Plessis
  takes a special maximal compact subgroup.  `thetaFBP` depends on `K` through `v_M`, and on the
  presentation `L` of `M` through the coordinates of `a_M`.  The dependence on the presentation
  is only apparent: for the same `K`, `thetaFBP` is the same for any two presentations with the
  same weight spaces up to relabelling, for every `f` (`thetaFBP_eq_of_sameWtSpaces`,
  `TraceFormula/ThetaFBPPresentation.lean`), and for any two presentations of the same `M`
  modulo the `sorry` `sameWtSpaces_of_M_eq` (`thetaFBP_eq_of_M_eq`, off the path).  For strongly
  cuspidal `f` and `K` special (`GoodK.IsSpecial`) the independence of `K` is not proved here; it
  and the independence of the presentation used by `thetaF` are assumed through
  `waldspurger2010_lemme_5_3` (Waldspurger 2010, Lemmes 5.2, 5.3; Beuzart-Plessis Lemma
  5.2.1(ii)).  `thetaF` (`TraceFormula/ThetaFGlobal.lean`) uses
  special `K` only; independence for a general `GoodK` is not used.
* When `d_c t` does not exist (no `IsDcMeasure`), `dcMeasure` is `0` and `thetaFBP` is `0`.  It
  exists for `IsMx L x` (`exists_isDcMeasure`, `IsMx.exists_isDcMeasure`): `A_M(F) ∩ ker H_M` is
  compact and open in `A_M(F)` (`isCompact_AGxOne`, `isOpen_AGxOne`).

## Main definitions

* `ReducedLeviDatum.AGx L x`: `A_{G_x}(F) = A_M(F)` as a subgroup of `G_x(F)`; `AGxOne`: its
  maximal compact subgroup `A_M(F) ∩ ker H_M`.
* `ReducedLeviDatum.IsMx L x`: `L.M = M(x)`.
* `ReducedLeviDatum.IsDcMeasure L x μ`, `dcMeasure L x`: Beuzart-Plessis' `d_c t` on `G_x(F)`.
* `ReducedLeviDatum.thetaFBP L K f x`:
  `(−1)^{dim a_M^G} D^G(x)^{−1/2} J_M(x, f; d_c t)`.

## Main results

* `IsMx.centG_le`: `G_x(F) ⊆ M(F)` (and `x ∈ M(F)` by definition).
* `exists_isMx`: every `x ∈ G_reg(F)` has an `L` with `IsMx L x` (`sorry`, with a proof sketch;
  on the path of the main theorem through `thetaF`).
* `isCompact_AGxOne`, `isOpen_AGxOne`: `A_M(F) ∩ ker H_M` is compact and open in `A_M(F)`.
* `IsDcMeasure.unique`, `dcMeasure_eq`: `d_c t` is unique; `exists_isDcMeasure`,
  `IsMx.exists_isDcMeasure`: it exists when `G_x(F)/A_M(F)` is compact, e.g. for `IsMx L x`.
* `dcMeasure_conj`: `d_c t` is transported by conjugation by `M(F)`.
* `thetaFBP_eq_integral`: `thetaFBP = (−1)^{dim a_M^G} ∫_{G_x\G} f(g⁻¹ x g) v_M(g) dg/d_c t`.
* `thetaFBP_conj`: `thetaFBP(m x m⁻¹) = thetaFBP(x)` for `m ∈ M(F)`.
* `thetaFBP_conj_K`: invariance of `thetaFBP(x)` under conjugating `f` by `K`.
* `thetaFBP_of_aG_eq_top`: for `a_M = a_G` (e.g. `M = G`, `x` elliptic) the sign is `1`, `v_M = 1`,
  and `thetaFBP = D^G(x)^{−1/2} J_G(x, f; d_c t)`.
-/

noncomputable section

open MeasureTheory Topology Module
open scoped ENNReal NNReal

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable {d : GGPData F}

namespace ReducedLeviDatum

variable (L : d.ReducedLeviDatum)

/-! ## 1. `A_{G_x}(F)` and `M(x)` -/

/-! ### The objects attached to a subgroup `T` (`T = G_x(F)` below)

`A_{G_x}(F)`, its maximal compact subgroup and `d_c t` depend on `x` only through `G_x(F)`; they
are defined for a subgroup `T` and specialized to `T = G_x(F)`, so that two points with the same
centralizer have literally the same objects (`integral_orbQuotMeasure_dcMeasure_congr`). -/

/-- `A_M(F) ∩ T`, as a subgroup of `T`. -/
def AGxOn (T : Subgroup ↥d.G) : Subgroup ↥T := L.AMF.subgroupOf T

/-- The inclusion `A_M(F) ∩ T → M(F)`. -/
def AGxToMOn (T : Subgroup ↥d.G) : ↥(L.AGxOn T) →* ↥L.M :=
  (T.subtype.comp (L.AGxOn T).subtype).codRestrict L.M
    fun a => L.AMF_le_M (Subgroup.mem_subgroupOf.1 a.2)

/-- `A_M(F) ∩ T ∩ ker H_M`. -/
def AGxOneOn (T : Subgroup ↥d.G) : Subgroup ↥(L.AGxOn T) := (L.HMHom.comp (L.AGxToMOn T)).ker

/-- **`A_{G_x}(F)`, for `L.M = M(x)`** (Beuzart-Plessis §1.6, §5.2): `A_M(F)` as a subgroup of
`G_x(F)`.  When `L.M = M(x)` (`IsMx`) the maximal split central torus `A_{G_x}` of the torus `G_x`
is `A_M`.  Defined as `A_M(F) ∩ G_x(F)`, which is all of `A_M(F)` for `x ∈ M(F)` (`A_M` is central
in `M`; not needed here and not proved). -/
abbrev AGx (x : ↥d.G) : Subgroup ↥(d.centG x) := L.AGxOn (d.centG x)

variable {L} in
theorem mem_AGx {x : ↥d.G} {a : ↥(d.centG x)} : a ∈ L.AGx x ↔ (a : ↥d.G) ∈ L.AMF :=
  Subgroup.mem_subgroupOf

/-- The inclusion `A_{G_x}(F) → M(F)`. -/
abbrev AGxToM (x : ↥d.G) : ↥(L.AGx x) →* ↥L.M := L.AGxToMOn (d.centG x)

/-- **The maximal compact subgroup `A_{G_x}(F)^1 = A_M(F) ∩ ker H_M`** (the subgroup of measure `1`
for `d_c a`, Beuzart-Plessis §1.6).  For the split torus `A_M`, `H_M(A_M(F))` is a lattice of full
rank in `a_M` (`span_HMAMF_eq_top`, `exists_HM_mem_zmultiples`), so `ker H_M ∩ A_M(F) = A_M(O)` is
the maximal compact subgroup.  It is compact and open (`isCompact_AGxOne`, `isOpen_AGxOne`): on
`A_M(F)`, `ker H_M` is the lattice stabilizer `latticeK` of the splitting bases
(`HM_eq_zero_iff_mem_latticeK`). -/
abbrev AGxOne (x : ↥d.G) : Subgroup ↥(L.AGx x) := L.AGxOneOn (d.centG x)

theorem mem_AGxOne {x : ↥d.G} {a : ↥(L.AGx x)} :
    a ∈ L.AGxOne x ↔ L.HM (L.AGxToM x a) = 0 := by
  rw [AGxOne, AGxOneOn, MonoidHom.mem_ker]; rfl

/-- `A_{G_x}(F)^1` is the preimage of the lattice stabilizer `latticeK` of the splitting bases
(`HM_eq_zero_iff_mem_latticeK`). -/
theorem AGxOne_eq_preimage (x : ↥d.G) : (L.AGxOne x : Set ↥(L.AGx x)) =
    (fun a : ↥(L.AGx x) => ((a : ↥(d.centG x)) : ↥d.G)) ⁻¹' d.latticeK L.bWFin L.bVFin := by
  ext a
  rw [SetLike.mem_coe, mem_AGxOne]
  exact L.HM_eq_zero_iff_mem_latticeK (m := L.AGxToM x a) (mem_AGx.1 a.2)

/-- **`A_{G_x}(F)^1` is open** in `A_{G_x}(F)` (`latticeK` is open). -/
theorem isOpen_AGxOne (x : ↥d.G) : IsOpen (L.AGxOne x : Set ↥(L.AGx x)) := by
  rw [AGxOne_eq_preimage]
  exact (d.isOpen_latticeK _ _).preimage (continuous_subtypeVal.comp continuous_subtypeVal)

theorem isClosed_AGx (x : ↥d.G) : IsClosed (L.AGx x : Set ↥(d.centG x)) :=
  L.isClosed_AMF.preimage continuous_subtypeVal

instance locallyCompactSpace_AGx (x : ↥d.G) : LocallyCompactSpace ↥(L.AGx x) :=
  (L.isClosed_AGx x).locallyCompactSpace

instance secondCountableTopology_AGx (x : ↥d.G) : SecondCountableTopology ↥(L.AGx x) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

theorem isClosedEmbedding_AGx (x : ↥d.G) : IsClosedEmbedding (L.AGx x).subtype :=
  (L.isClosed_AGx x).isClosedEmbedding_subtypeVal

instance isClosed_range_AGx (x : ↥d.G) :
    IsClosed ((L.AGx x).subtype.range : Set ↥(d.centG x)) := by
  rw [Subgroup.range_subtype]; exact L.isClosed_AGx x

/-- **`A_{G_x}(F)^1` is compact** (`latticeK` is compact, and `A_{G_x}(F) → G(F)` is a closed
embedding). -/
theorem isCompact_AGxOne (x : ↥d.G) : IsCompact (L.AGxOne x : Set ↥(L.AGx x)) := by
  rw [AGxOne_eq_preimage]
  exact ((d.isClosedEmbedding_centG x).comp (L.isClosedEmbedding_AGx x)).isCompact_preimage
    (d.isCompact_latticeK _ _)

/-- **`L.M = M(x)`** (Beuzart-Plessis §5.2: `M(x)` is the centralizer of `A_{G_x}`, the minimal
Levi subgroup containing `x`): `x` is regular semisimple, lies in `M(F)`, and is elliptic in `M`,
i.e. `G_x(F)` is compact modulo `A_M(F)`.  For a Levi `M ∋ x` one has `A_M ⊆ A_{G_x}` and
`M(x) = M` iff `A_{G_x} = A_M` iff the torus `G_x / A_M` is anisotropic iff `G_x(F)/A_M(F)` is
compact (`A_M` split, so `(G_x/A_M)(F) = G_x(F)/A_M(F)`). -/
structure IsMx (x : ↥d.G) : Prop where
  regular : x ∈ regularSet d.G d.lie
  mem : x ∈ L.M
  compact : CompactSpace (CosetSpace (L.AGx x).subtype)

variable {L}

/-- **`G_x(F) ⊆ M(x)(F)`** (Waldspurger 2010, §2.3), from `centG_le_M`. -/
theorem IsMx.centG_le {x : ↥d.G} (h : L.IsMx x) : d.centG x ≤ L.M :=
  centG_le_M L.toFlagLeviDatum h.regular h.mem

variable (L) in
/-- If `G_x(F) ⊆ A_M(F)`, the space `A_M(F)\G_x(F)` is a point. -/
theorem subsingleton_cosetSpace_AGx {x : ↥d.G} (h : d.centG x ≤ L.AMF) :
    Subsingleton (CosetSpace (L.AGx x).subtype) := by
  refine ⟨fun a b => ?_⟩
  induction a using CosetSpace.ind with | h g => ?_
  induction b using CosetSpace.ind with | h k => ?_
  rw [CosetSpace.mk_eq_mk_iff, CosetSpace.rel_iff]
  exact ⟨⟨k * g⁻¹, mem_AGx.2 (h (k * g⁻¹).2)⟩, by simp⟩

/-- **Existence of `M(x)`** (Beuzart-Plessis §5.2; Waldspurger 2010, §2.3): every `x ∈ G_reg(F)`
has a reduced Levi datum `L` with `L.M = M(x)`.  Not proved here.

Proof sketch.  `T = G_x` is a maximal torus (`commute_of_mem_centG`); `M(x)` is the centralizer of
its maximal split subtorus `A_T`.  On `W` (and likewise `V`), `s = P(x_W) ∈ SO(W)` is semisimple;
`W = ⊕_p W_p`, `W_p = ker p(s)` over the monic irreducible factors `p` of its characteristic
polynomial, and `b` pairs `W_p` with `W_{p*}` (`p*` the reciprocal polynomial), so `W_p` is
totally isotropic for `p ≠ p*` and nondegenerate for `p = p*`.  The eigenspaces `W_{t∓1}` have
dimension `≤ 2`, since `x` is regular (`𝔤_x` abelian, while `𝔰𝔬` of a space of dimension `≥ 3`
is not), and every other eigenvalue (over `F̄`) has multiplicity `1`, so `dim W_p = deg p` and
`W_p` is a field `F[t]/(p)` on which `s` acts by multiplication by `t`; this is what makes the
centralizer on each piece the tori named below.  The split part of `T` acts on
`W_p ⊕ W_{p*}` (`p ≠ p*`) by `τ` on `W_p` and `τ⁻¹` on `W_{p*}`; on a `W_p` with `p = p*` of
degree `≥ 2` it acts trivially (the centralizer there is a norm-one torus, anisotropic); on an
eigenspace `W_{t∓1}` that is a hyperbolic plane it acts by `τ^{±1}` on its two isotropic lines,
and trivially if that eigenspace is anisotropic.  Number these split pieces `1, …, n` and give the
`k`-th piece weights `±k` (a basis adapted to the pieces); this is an `IsWtGrading` whose weight
spaces are `P(x)`-stable, so `x ∈ (ofGrading …).M` (`mem_flagLevi_iff`).  The weight-`0` space is
the sum of the anisotropic pieces; it is not a hyperbolic plane (an anisotropic `W_p`, `p = p*`,
is not one: a `W_p` with anisotropic centralizer torus is not a hyperbolic plane, whose `SO` is a
split torus; and `dim W_{t+1}` is even because `det P(x) = 1`, so `W_{t−1} ⊕ W_{t+1}` cannot be
two lines), so the datum is
reduced.  Then `A_M = A_T` (`AMF` is the lift of the scalars on the weight spaces), and
`T(F)/A_T(F)` embeds in `(T/A_T)(F)` as a closed subgroup (Hilbert 90 for the split `A_T`), which
is compact since `T/A_T` is anisotropic: `CompactSpace (CosetSpace (L.AGx x).subtype)`. -/
theorem exists_isMx {x : ↥d.G} (hx : x ∈ regularSet d.G d.lie) :
    ∃ L : d.ReducedLeviDatum, L.IsMx x := by
  sorry

/-! ## 2. The measure `d_c t` -/

variable (L)

/-- **Beuzart-Plessis' measure `d_c t`** (§1.6, p. 30), on a subgroup `T` (`T = G_x(F)` below):
`μ` is a Haar measure on `G_x(F)` and there are a Haar measure `d_c a` on `A_{G_x}(F)` giving the
maximal compact subgroup
`AGxOne` measure `1` and a quotient measure (`IsWeilMeasure`, `μ = (quotient) ∘ d_c a`) giving
`A_{G_x}(F)\G_x(F)` measure `1`.  (`G_x(F)` is commutative for regular `x`, so right cosets are
left cosets.) -/
def IsDcMeasureOn (T : Subgroup ↥d.G) (μ : Measure ↥T) : Prop :=
  μ.IsHaarMeasure ∧ ∃ (μA : Measure ↥(L.AGxOn T)) (m : Measure (CosetSpace (L.AGxOn T).subtype)),
    μA.IsHaarMeasure ∧ μA (L.AGxOneOn T : Set ↥(L.AGxOn T)) = 1 ∧
      IsWeilMeasure (L.AGxOn T).subtype μ μA m ∧ m Set.univ = 1

/-- `IsDcMeasureOn` at `T = G_x(F)`. -/
abbrev IsDcMeasure (x : ↥d.G) (μ : Measure ↥(d.centG x)) : Prop := L.IsDcMeasureOn (d.centG x) μ

open scoped Classical in
/-- `d_c t` on a subgroup `T`, chosen by the epsilon pattern; `0` if there is none. -/
def dcMeasureOn (T : Subgroup ↥d.G) : Measure ↥T :=
  if h : ∃ μ, L.IsDcMeasureOn T μ then h.choose else 0

/-- **`d_c t` on `G_x(F)`** (Beuzart-Plessis §1.6), chosen by the epsilon pattern; `0` if there is
none.  It is unique for regular `x` (`dcMeasure_eq`) and exists under `exists_isDcMeasure`.
Beuzart-Plessis writes `d_c t = ν(G_x) dt`; using `d_c t` in `J_M` absorbs `ν(G_x)⁻¹`. -/
abbrev dcMeasure (x : ↥d.G) : Measure ↥(d.centG x) := L.dcMeasureOn (d.centG x)

theorem AGx_eq_AGxOn (x : ↥d.G) : L.AGx x = L.AGxOn (d.centG x) := rfl

theorem dcMeasure_eq_dcMeasureOn (x : ↥d.G) : L.dcMeasure x = L.dcMeasureOn (d.centG x) := rfl

variable {L}

/-- **`d_c t` is unique** for regular `x`: Haar measures are proportional, and the two
normalizations fix the constants. -/
theorem IsDcMeasure.unique {x : ↥d.G} (hx : x ∈ regularSet d.G d.lie) {μ μ' : Measure ↥(d.centG x)}
    (h : L.IsDcMeasure x μ) (h' : L.IsDcMeasure x μ') : μ = μ' := by
  obtain ⟨hμ, μA, m, hA, hA1, hW, hm1⟩ := h
  obtain ⟨hμ', μA', m', hA', hA1', hW', hm1'⟩ := h'
  have := isMulRightInvariant_of_le_centG hx (L.AGx x) μA
  have := isMulRightInvariant_of_le_centG hx (L.AGx x) μA'
  have hTμ : μ.IsMulRightInvariant := isMulRightInvariant_of_mem_regularSet hx μ
  have hTμ' : μ'.IsMulRightInvariant := isMulRightInvariant_of_mem_regularSet hx μ'
  have hs : ∀ {α : Type _} [MeasurableSpace α] (c : ℝ≥0) (ν : Measure α),
      c • ν = (c : ℝ≥0∞) • ν := fun c ν => ENNReal.smul_def c ν
  -- `d_c a` is unique
  have eA : μA' = μA := by
    have e := Measure.isMulLeftInvariant_eq_smul μA' μA
    rw [hs] at e
    have h1 := congrArg (fun ν : Measure ↥(L.AGx x) => ν (L.AGxOne x : Set ↥(L.AGx x))) e
    simp only [smul_apply, hA1, hA1', smul_eq_mul, mul_one] at h1
    rw [e, ← h1, one_smul]
  subst eA
  -- the scalar relating `μ'` to `μ` is `1`
  have e := Measure.isMulLeftInvariant_eq_smul μ' μ
  rw [hs] at e
  set c : ℝ≥0∞ := (Measure.haarScalarFactor μ' μ : ℝ≥0∞)
  have hW2 : IsWeilMeasure (L.AGx x).subtype μ' μA' (c • m) := by
    rw [e]; exact hW.smul_left c
  have hmm := IsWeilMeasure.unique continuous_subtypeVal (L.isClosedEmbedding_AGx x) hW' hW2
  have h1 := congrArg (fun ν : Measure (CosetSpace (L.AGx x).subtype) => ν Set.univ) hmm
  simp only [smul_apply, hm1, hm1', smul_eq_mul, mul_one] at h1
  rw [e, ← h1, one_smul]

theorem isDcMeasure_dcMeasure {x : ↥d.G} (h : ∃ μ, L.IsDcMeasure x μ) :
    L.IsDcMeasure x (L.dcMeasure x) := by
  classical
  unfold dcMeasure dcMeasureOn
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

theorem dcMeasure_eq {x : ↥d.G} (hx : x ∈ regularSet d.G d.lie) {μ : Measure ↥(d.centG x)}
    (h : L.IsDcMeasure x μ) : L.dcMeasure x = μ :=
  (isDcMeasure_dcMeasure ⟨μ, h⟩).unique hx h

theorem dcMeasure_of_not_exists {x : ↥d.G} (h : ¬ ∃ μ, L.IsDcMeasure x μ) :
    L.dcMeasure x = 0 := by
  classical
  unfold dcMeasure dcMeasureOn
  rw [dite_eq_right_of_eq_false (eq_false h)]

/-- **Existence of `d_c t`**, when `G_x(F)/A_M(F)` is compact (`IsMx`): normalize a Haar measure
of `A_M(F)` on the compact open subgroup `AGxOne` (`isCompact_AGxOne`, `isOpen_AGxOne`), and a
Haar measure of `G_x(F)` by the (finite, nonzero) total mass of the quotient. -/
theorem exists_isDcMeasure {x : ↥d.G} (hx : x ∈ regularSet d.G d.lie)
    [hc : CompactSpace (CosetSpace (L.AGx x).subtype)] :
    ∃ μ, L.IsDcMeasure x μ := by
  have ho := L.isOpen_AGxOne x
  have hk := L.isCompact_AGxOne x
  set A1 : Set ↥(L.AGx x) := (L.AGxOne x : Set ↥(L.AGx x))
  set ι := (L.AGx x).subtype
  -- `d_c a`: the Haar measure normalized on the compact open subgroup `A¹`
  let A1c : TopologicalSpace.PositiveCompacts ↥(L.AGx x) :=
    ⟨⟨A1, hk⟩, ⟨1, ho.mem_nhds (L.AGxOne x).one_mem |> mem_interior_iff_mem_nhds.2⟩⟩
  set μA : Measure ↥(L.AGx x) := Measure.haarMeasure A1c
  have hA : μA.IsHaarMeasure := inferInstance
  have hA1 : μA A1 = 1 := Measure.haarMeasure_self
  have := isMulRightInvariant_of_le_centG hx (L.AGx x) μA
  -- the quotient of a Haar measure of `G_x(F)`
  set ν0 : Measure ↥(d.centG x) := Measure.haar
  have := isMulRightInvariant_of_mem_regularSet hx ν0
  obtain ⟨m0, hW0, -⟩ := weil_quotient ι continuous_subtypeVal (L.isClosedEmbedding_AGx x) ν0 μA
  have := hW0.isFiniteMeasureOnCompacts continuous_subtypeVal (L.isClosedEmbedding_AGx x)
  have hfin : m0 Set.univ ≠ ⊤ := isCompact_univ.measure_lt_top.ne
  have hpos : m0 Set.univ ≠ 0 := fun h00 => hW0.ne_zero (Measure.measure_univ_eq_zero.1 h00)
  refine ⟨(m0 Set.univ)⁻¹ • ν0, Measure.IsHaarMeasure.smul ν0 (ENNReal.inv_ne_zero.2 hfin)
    (ENNReal.inv_ne_top.2 hpos), μA, (m0 Set.univ)⁻¹ • m0, hA, hA1, hW0.smul_left _, ?_⟩
  simp only [smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]

/-- **`d_c t` exists for `L.M = M(x)`.** -/
theorem IsMx.exists_isDcMeasure {x : ↥d.G} (h : L.IsMx x) : ∃ μ, L.IsDcMeasure x μ := by
  have := h.compact
  exact ReducedLeviDatum.exists_isDcMeasure h.regular

/-! ### Transport by conjugation in `M(F)` -/

/-- Conjugation by `m ∈ M(F)` maps `A_{G_x}(F)` onto `A_{G_{m x m⁻¹}}(F)` (`conj_mem_AMF`). -/
def AGxConj (x m : ↥d.G) (hm : m ∈ L.M) : ↥(L.AGx x) ≃ₜ* ↥(L.AGx (m * x * m⁻¹)) where
  toFun a := ⟨d.centConj x m (a : ↥(d.centG x)), mem_AGx.2 (L.conj_mem_AMF hm (mem_AGx.1 a.2))⟩
  invFun a := ⟨(d.centConj x m).symm (a : ↥(d.centG (m * x * m⁻¹))), mem_AGx.2 (by
    have := L.conj_mem_AMF (L.M.inv_mem hm) (mem_AGx.1 a.2)
    rwa [inv_inv] at this)⟩
  left_inv a := Subtype.ext ((d.centConj x m).left_inv (a : ↥(d.centG x)))
  right_inv a := Subtype.ext ((d.centConj x m).right_inv (a : ↥(d.centG (m * x * m⁻¹))))
  map_mul' a b := Subtype.ext (map_mul (d.centConj x m) (a : ↥(d.centG x)) b)
  continuous_toFun := Continuous.subtype_mk
    ((d.centConj x m).continuous.comp continuous_subtypeVal) _
  continuous_invFun := Continuous.subtype_mk
    ((d.centConj x m).symm.continuous.comp continuous_subtypeVal) _

@[simp] theorem coe_AGxConj (x m : ↥d.G) (hm : m ∈ L.M) (a : ↥(L.AGx x)) :
    ((L.AGxConj x m hm a : ↥(L.AGx (m * x * m⁻¹))) : ↥(d.centG (m * x * m⁻¹))) =
      d.centConj x m (a : ↥(d.centG x)) := rfl

/-- `AGxConj` preserves the maximal compact subgroup (`HM_conj`). -/
theorem preimage_AGxConj_AGxOne (x m : ↥d.G) (hm : m ∈ L.M) :
    L.AGxConj x m hm ⁻¹' (L.AGxOne (m * x * m⁻¹) : Set ↥(L.AGx (m * x * m⁻¹))) =
      (L.AGxOne x : Set ↥(L.AGx x)) := by
  ext a
  simp only [Set.mem_preimage, SetLike.mem_coe, mem_AGxOne]
  have e : L.AGxToM (m * x * m⁻¹) (L.AGxConj x m hm a) =
      ⟨m, hm⟩ * L.AGxToM x a * ⟨m, hm⟩⁻¹ := rfl
  rw [e, HM_conj]

/-- **`d_c t` is transported by conjugation in `M(F)`.** -/
theorem IsDcMeasure.map {x m : ↥d.G} (hx : x ∈ regularSet d.G d.lie) (hm : m ∈ L.M)
    {μ : Measure ↥(d.centG x)} (h : L.IsDcMeasure x μ) :
    L.IsDcMeasure (m * x * m⁻¹) (μ.map (d.centConj x m)) := by
  obtain ⟨hμ, μA, mW, hA, hA1, hW, hm1⟩ := h
  have := isMulRightInvariant_of_le_centG hx (L.AGx x) μA
  set eA := L.AGxConj x m hm
  have hι : ∀ a, (L.AGx (m * x * m⁻¹)).subtype (eA a) = d.centConj x m ((L.AGx x).subtype a) :=
    fun _ => rfl
  set ē := CosetSpace.mapHomeomorph (L.AGx x).subtype (L.AGx (m * x * m⁻¹)).subtype
    eA.toMulEquiv (d.centConj x m) hι
  refine ⟨inferInstance, μA.map eA, mW.map ē, inferInstance, ?_, hW.map eA (d.centConj x m) hι, ?_⟩
  · rw [show (μA.map eA) = μA.map eA.toHomeomorph.toMeasurableEquiv from rfl,
      MeasurableEquiv.map_apply]
    exact (congrArg μA (L.preimage_AGxConj_AGxOne x m hm)).trans hA1
  · rw [show (mW.map ē) = mW.map ē.toMeasurableEquiv from rfl, MeasurableEquiv.map_apply,
      Set.preimage_univ, hm1]

/-- **`d_c t` on `G_{m x m⁻¹}(F)` is the transport of `d_c t` on `G_x(F)`**, for `m ∈ M(F)` and
`x` regular (both sides are `0` if `d_c t` does not exist). -/
theorem dcMeasure_conj {x m : ↥d.G} (hx : x ∈ regularSet d.G d.lie) (hm : m ∈ L.M) :
    L.dcMeasure (m * x * m⁻¹) = (L.dcMeasure x).map (d.centConj x m) := by
  have hx' : m * x * m⁻¹ ∈ regularSet d.G d.lie := conj_mem_regularSet d m x hx
  by_cases h : ∃ μ, L.IsDcMeasure x μ
  · exact dcMeasure_eq hx' ((isDcMeasure_dcMeasure h).map hx hm)
  · have h' : ¬ ∃ μ, L.IsDcMeasure (m * x * m⁻¹) μ := by
      rintro ⟨μ, hμ⟩
      have h2 := hμ.map hx' (L.M.inv_mem hm)
      have e : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
      have h3 : ∃ μ, L.IsDcMeasure (m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹) μ := ⟨_, h2⟩
      rw [e] at h3
      exact h h3
    rw [dcMeasure_of_not_exists h, dcMeasure_of_not_exists h', Measure.map_zero]

variable (L)

/-! ## 3. `θ_f` -/

/-- **Beuzart-Plessis' `θ_f(x)`** (Astérisque 418, §5.2, p. 109; Waldspurger 2010, §5.3), for a
Levi datum `L` with `L.M = M(x)` (`IsMx L x`):
`θ_f(x) = (−1)^{a_G − a_{M(x)}} ν(G_x)⁻¹ D^G(x)^{−1/2} J_{M(x)}(x, f)
        = (−1)^{dim a_M^G} D^G(x)^{−1/2} J_M(x, f; d_c t)`,
with `J_M` Arthur's weighted orbital integral (`weightedOrbitalIntegral`), `a_G − a_M = dim a_M^G`,
and the measure `d_c t = ν(G_x) dt` on `G_x(F)` (`dcMeasure`), so that `ν(G_x)` does not appear
(`weightedOrbitalIntegral_smul_measure`).  The normalization is Beuzart-Plessis' §5.2, not the
introductory formula `(−1)^{a_{M(x)}} J_{M(x)}(x, f)` quoted in Thesis Ch. 1.
* It is Beuzart-Plessis' function only at `x` with `IsMx L x`; elsewhere it has no meaning.
* `dg` on `G(F)` is `Measure.haar`, which differs from Beuzart-Plessis' measure by a positive
  constant (module docstring); `θ_f` is linear in `dg`.
* It depends on `K` through `v_M` (on the presentation `L` only through its weight spaces,
  `thetaFBP_eq_of_sameWtSpaces`); Beuzart-Plessis Lemma 5.2.1(ii)
  (Waldspurger 2010, Lemme 5.2) says it does not for strongly cuspidal `f` and special `K`.  This
  is not proved here (`f` is arbitrary); `thetaF` takes it from `waldspurger2010_lemme_5_3`.
* It is `0` if `d_c t` does not exist (`dcMeasure`). -/
def thetaFBP (K : d.GoodK L.toFlagLeviDatum) (f : ↥d.G → ℂ) (x : ↥d.G) : ℂ :=
  (-1) ^ finrank ℝ L.aMG * ((Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) : ℂ))⁻¹ *
    d.weightedOrbitalIntegral L K x (L.dcMeasure x) f

variable {L}

/-- **`θ_f(x) = (−1)^{dim a_M^G} ∫_{G_x(F)\G(F)} f(g⁻¹ x g) v_M(g) dg/d_c t`**: the factors
`D^G(x)^{±1/2}` cancel (`D^G(x) > 0`). -/
theorem thetaFBP_eq_integral (K : d.GoodK L.toFlagLeviDatum) (f : ↥d.G → ℂ) (x : ↥d.G) :
    L.thetaFBP K f x = (-1) ^ finrank ℝ L.aMG *
      ∫ q, d.weightedIntegrand L K x f (CosetSpace.out _ q)
        ∂d.orbQuotMeasure x (L.dcMeasure x) := by
  have hD : ((Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (weylDisc_pos d x)).ne'
  unfold thetaFBP weightedOrbitalIntegral
  rw [mul_assoc, ← mul_assoc _ (Real.sqrt _ : ℂ), inv_mul_cancel₀ hD, one_mul]

/-- **`θ_f` is invariant under conjugation by `M(F)`**: `θ_f(m x m⁻¹) = θ_f(x)` for `m ∈ M(F)`
and `x ∈ M(F) ∩ G_reg(F)` (Beuzart-Plessis §5.2, from Lemma 5.2.1(iv) with `y ∈ M(F)`; here from
`weightedOrbitalIntegral_conj`, `weylDisc_conj` and the transport of `d_c t`, `dcMeasure_conj`).
`IsMx L x` implies `IsMx L (m x m⁻¹)` for such `m`, which is not needed here. -/
theorem thetaFBP_conj (K : d.GoodK L.toFlagLeviDatum) (f : ↥d.G → ℂ) {x m : ↥d.G}
    (hx : x ∈ regularSet d.G d.lie) (hxM : x ∈ L.M) (hm : m ∈ L.M) :
    L.thetaFBP K f (m * x * m⁻¹) = L.thetaFBP K f x := by
  have hx' : m * x * m⁻¹ ∈ regularSet d.G d.lie := conj_mem_regularSet d m x hx
  unfold thetaFBP
  rw [weylDisc_conj]
  congr 1
  by_cases h : ∃ μ, L.IsDcMeasure x μ
  · have hdc := isDcMeasure_dcMeasure h
    have := hdc.1
    have := isMulRightInvariant_of_mem_regularSet hx (L.dcMeasure x)
    have hdc' := (isDcMeasure_dcMeasure ⟨_, hdc.map hx hm⟩ :
      L.IsDcMeasure (m * x * m⁻¹) (L.dcMeasure (m * x * m⁻¹)))
    have := hdc'.1
    have := isMulRightInvariant_of_mem_regularSet hx' (L.dcMeasure (m * x * m⁻¹))
    exact weightedOrbitalIntegral_conj (centG_le_M L.toFlagLeviDatum hx hxM) hm _ _
      (dcMeasure_conj hx hm).symm f
  · rw [dcMeasure_conj hx hm, dcMeasure_of_not_exists h, Measure.map_zero,
      weightedOrbitalIntegral_zero_measure, weightedOrbitalIntegral_zero_measure]

/-- **`θ_f(x)` is unchanged by conjugating `f` by `k ∈ K`**, for `x ∈ M(F) ∩ G_reg(F)`
(`weightedOrbitalIntegral_conj_K_of_mem_regularSet`). -/
theorem thetaFBP_conj_K (K : d.GoodK L.toFlagLeviDatum) (f : ↥d.G → ℂ) {x : ↥d.G}
    (hx : x ∈ regularSet d.G d.lie) (hxM : x ∈ L.M) {k : ↥d.G} (hk : k ∈ K.K) :
    L.thetaFBP K (fun g => f (k * g * k⁻¹)) x = L.thetaFBP K f x := by
  unfold thetaFBP
  congr 1
  by_cases h : ∃ μ, L.IsDcMeasure x μ
  · have := (isDcMeasure_dcMeasure h).1
    exact weightedOrbitalIntegral_conj_K_of_mem_regularSet hx hxM _ hk f
  · rw [dcMeasure_of_not_exists h, weightedOrbitalIntegral_zero_measure,
      weightedOrbitalIntegral_zero_measure]

/-- **The case `a_M = a_G`** (e.g. `M = G`, i.e. `x` elliptic in `G`): the sign is `1` and
`v_M = 1`, so `θ_f(x) = D^G(x)^{−1/2} J_G(x, f; d_c t) = ∫_{G_x(F)\G(F)} f(g⁻¹ x g) dg/d_c t`. -/
theorem thetaFBP_of_aG_eq_top (hG : L.aG = ⊤) (K : d.GoodK L.toFlagLeviDatum)
    (f : ↥d.G → ℂ) (x : ↥d.G) :
    L.thetaFBP K f x =
      ((Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) : ℂ))⁻¹ *
        d.orbitalIntegral x (L.dcMeasure x) f := by
  have : Subsingleton L.aMG := Submodule.Quotient.subsingleton_iff.2 hG
  unfold thetaFBP
  rw [finrank_zero_of_subsingleton, pow_zero, one_mul,
    weightedOrbitalIntegral_eq_orbitalIntegral_of_aG_eq_top hG]

/-- The case `a_M = a_G` as an integral: `θ_f(x) = ∫_{G_x(F)\G(F)} f(g⁻¹ x g) dg/d_c t`. -/
theorem thetaFBP_of_aG_eq_top_eq_integral (hG : L.aG = ⊤) (K : d.GoodK L.toFlagLeviDatum)
    (f : ↥d.G → ℂ) (x : ↥d.G) :
    L.thetaFBP K f x = ∫ q, f ((CosetSpace.out _ q)⁻¹ * x * CosetSpace.out _ q)
      ∂d.orbQuotMeasure x (L.dcMeasure x) := by
  have hD : ((Real.sqrt (weylDisc d.lie (x : d.ambientˣ)) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (weylDisc_pos d x)).ne'
  rw [thetaFBP_of_aG_eq_top hG, orbitalIntegral_eq, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]

/-! ## 4. Dependence on `x` only through `G_x(F)`; linearity -/

variable (L) in
/-- **Integrals over `G_x(F)\G(F)` for `dg / d_c t` depend on `x` only through `G_x(F)`.** -/
theorem integral_orbQuotMeasure_dcMeasure_congr {x y : ↥d.G} (h : d.centG x = d.centG y)
    (Φ : ↥d.G → ℂ) :
    ∫ q, Φ (CosetSpace.out _ q) ∂d.orbQuotMeasure x (L.dcMeasure x) =
      ∫ q, Φ (CosetSpace.out _ q) ∂d.orbQuotMeasure y (L.dcMeasure y) := by
  have key : ∀ T T' : Subgroup ↥d.G, T = T' →
      ∫ q, Φ (CosetSpace.out T.subtype q) ∂d.quotMeasureOn T (L.dcMeasureOn T) =
        ∫ q, Φ (CosetSpace.out T'.subtype q) ∂d.quotMeasureOn T' (L.dcMeasureOn T') := by
    rintro T _ rfl; rfl
  exact key _ _ h


/-- **`IsMx` depends on `x` only through `G_x(F)`** (for regular `x`): `x ∈ G_x(F) ⊆ M(F)`, and
`A_{G_x}(F)` is defined from `G_x(F)`. -/
theorem IsMx.of_centG_eq {x y : ↥d.G} (h : L.IsMx x) (hy : y ∈ regularSet d.G d.lie)
    (hc : d.centG y = d.centG x) : L.IsMx y := by
  refine ⟨hy, h.centG_le (hc ▸ Subgroup.mem_centralizer_singleton_iff.2 rfl), ?_⟩
  have key : ∀ T T' : Subgroup ↥d.G, T = T' →
      CompactSpace (CosetSpace (L.AGxOn T).subtype) →
        CompactSpace (CosetSpace (L.AGxOn T').subtype) := by
    rintro T _ rfl h; exact h
  exact key _ _ hc.symm h.compact

/-- **`θ_f(a x) = χ(a)⁻¹ θ_f(x)` for one presentation**, `f` `χ`-equivariant and `a ∈ A_G(F)`:
`G_{a x}(F) = G_x(F)`, and `f(g⁻¹ a x g) = f(a g⁻¹ x g) = χ(a)⁻¹ f(g⁻¹ x g)` (`a` central). -/
theorem thetaFBP_mul_AG (K : d.GoodK L.toFlagLeviDatum) (χ : CentralCharOn d) {f : ↥d.G → ℂ}
    (hf : IsChiEquivariant d χ f) (a : ↥d.AG) (x : ↥d.G) :
    L.thetaFBP K f ((a : ↥d.G) * x) = (((χ.toHom a)⁻¹ : Circle) : ℂ) * L.thetaFBP K f x := by
  rw [thetaFBP_eq_integral, thetaFBP_eq_integral,
    L.integral_orbQuotMeasure_dcMeasure_congr (d.centG_mul_AG x a.2)]
  unfold weightedIntegrand
  have hc : ∀ g : ↥d.G, g⁻¹ * ((a : ↥d.G) * x) * g = (a : ↥d.G) * (g⁻¹ * x * g) := fun g => by
    have hb := Subgroup.mem_center_iff.mp (d.AG_le_center a.2) g⁻¹
    rw [← mul_assoc, hb, mul_assoc, mul_assoc, mul_assoc]
  simp_rw [hc, hf a, mul_assoc, integral_const_mul]
  ring

/-- **`θ_{κ f} = κ θ_f` for one presentation**, for `κ` invariant under conjugation. -/
theorem thetaFBP_mul_invariant (K : d.GoodK L.toFlagLeviDatum) {κ : ↥d.G → ℂ}
    (hκ : ∀ g y : ↥d.G, κ (g⁻¹ * y * g) = κ y) (f : ↥d.G → ℂ) (x : ↥d.G) :
    L.thetaFBP K (κ * f) x = κ x * L.thetaFBP K f x := by
  rw [thetaFBP_eq_integral, thetaFBP_eq_integral]
  unfold weightedIntegrand
  simp_rw [Pi.mul_apply, hκ, mul_assoc, integral_const_mul]
  ring

/-- `θ_0 = 0` for one presentation. -/
theorem thetaFBP_zero_fun (K : d.GoodK L.toFlagLeviDatum) (x : ↥d.G) :
    L.thetaFBP K 0 x = 0 := by
  rw [thetaFBP_eq_integral]
  unfold weightedIntegrand
  simp

end ReducedLeviDatum

end GGPData

end GSpinGGP
