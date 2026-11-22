/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.LeviSubgroup
import GSpinGGP.HarmonicAnalysis.HullVolume

/-!
# Arthur's weight `v_M(g)`

For a Levi subgroup `M` of `G = GSpin(W) × GSpin(V)` and a compact open subgroup `K` with
`G = P K` for every `P ∈ 𝒫(M)`, the points `H_P(g)`, `P ∈ 𝒫(M)`, of `a_M` define the weight
`v_M(g)`: the volume in `a_M^G = a_M / a_G` of their convex hull (Thesis §2.6; Beuzart-Plessis,
Astérisque 418, §1.10, p. 36; Waldspurger, Compos. Math. 146 (2010), §2.3).  The Haar measure on
`a_M^G` is the one of Waldspurger 2010, §1.2: the quotient of `a_M^G` by the projection of
`H_M(A_M(F))` has volume `1`.

The weight is defined directly as a volume; the (G,M)-family formalism, of which `v_M(g)` is the
number `c_M` attached to the family of the points `H_P(g)`, is not built here.  The sources
identify `c_M` with the volume of the hull when the family `(H_P(g))_P` is *positive*
`(G,M)`-orthogonal (Beuzart-Plessis §1.9, p. 36), and state that it is so for `K` special
(Beuzart-Plessis §1.10; Waldspurger 2010, §2.3: `K` special in good position relative to `M`).
`GoodK` carries `G = P K` and good position; positivity is not yet proved from it, and the
definition below is the sources' `v_M` when it holds.

## Main definitions

* `GGPData.GoodK L`: a compact open subgroup `K` with `G = P K` for every `P ∈ 𝒫(M)`, in good
  position relative to `M` (it stabilizes weight-split lattices of `W` and `V`).
* `GGPData.ReducedLeviDatum.hPar`: `H_P : G → a_M` for each `P ∈ 𝒫(M)` (any flags defining `P`
  give the same map, `hPar_eq`).
* `GGPData.ReducedLeviDatum.AMF`: `A_M(F)`, the split component of the centre of `M`.
* `GGPData.ReducedLeviDatum.aG`: `a_G ⊆ a_M`, spanned by `H_M(A_G(F))`.
* `GGPData.ReducedLeviDatum.latticeMG`: `proj_M^G(H_M(A_M(F)))` in `a_M / a_G`.
* `GGPData.ReducedLeviDatum.vM`: the weight `v_M(g)`.

## Main results

* `vM_mul_left`: `v_M(m g) = v_M(g)` for `m ∈ M`.
* `vM_mul_right`: `v_M(g k) = v_M(g)` for `k ∈ K`.
* `vM_eq_hullVolume_neg`: the hull of the `−H_P(g)` has the same volume.
* `vM_eq_one_of_aG_eq_top`: `v_M = 1` when `a_M = a_G` (e.g. `M = G`).
-/

noncomputable section

open MeasureTheory Module Pointwise

namespace GSpinGGP

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {d : GGPData F}

/-! ## 2. Good compact subgroups -/

section SplitLattice

variable {V : Type*} [AddCommGroup V] [Module F V] {ι : Type*}

/-- **`S` stabilizes an `𝒪_F`-lattice of `V` split by the weight spaces of `(b, wt)`**: there is a
basis `e` of `V`, each vector of which lies in one weight space `wtSpan b wt w`, such that every
`P(g)`, `g ∈ S`, maps the lattice `Λ_e = {v : ‖e^*_i(v)‖ ≤ 1 ∀ i}` into itself.  (Every
`𝒪_F`-lattice
that is the direct sum of its intersections with the weight spaces is such a `Λ_e`.) -/
def StabilizesSplitLattice (Q : QuadraticForm F V) (b : Basis ι F V) (wt : ι → ℤ)
    (S : Set (GSpin Q)) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (e : Basis κ F V), (∀ i, ∃ w, e i ∈ wtSpan b wt w) ∧
    ∀ g ∈ S, ∀ v : V, (∀ i, ‖e.repr v i‖ ≤ 1) → ∀ i, ‖e.repr (specP Q g v) i‖ ≤ 1

end SplitLattice

variable (d) in
/-- **A good compact subgroup for the Levi datum `L`**, carried as data: a compact open subgroup
`K` of `G` with
* the Iwasawa decomposition `G = P K` for every `P ∈ 𝒫(M)` (hence `G = Q K` for every parabolic
  `Q ⊇ M`, which contains some `P ∈ 𝒫(M)`);
* **good position relative to `M`** in lattice form: `K` stabilizes `𝒪_F`-lattices of `W` and `V`
  that are split by the weight spaces of `L`, i.e. by the eigenspaces of `A_M`.
Waldspurger 2010, §1.1 and §2.3, takes `K` special maximal compact in good position relative to
`M` (`K` fixes a special point of the apartment of a maximal split torus `A ⊆ M`).  Through
`P : GSpin → SO`, a point of that apartment gives norms on `W` and `V` split by the
`A`-eigenspaces, whose unit balls are lattices split by the weight spaces (sums of
`A`-eigenspaces); `goodPositionW/V` keep only this consequence (not proved here from the building).
Beuzart-Plessis (§1.10) takes `K` special.  These sources state that `(H_P(g))_{P ∈ 𝒫(M)}` is
then a *positive* `(G,M)`-orthogonal family.  Positivity is expected from `goodPositionW/V` alone
(not proved here; no roots of `A_M` are formalized yet): `H_P` does not change when `K` is
enlarged to the stabilizer of the split lattices, and for adjacent `P, P'` the difference
`H_P(g) - H_{P'}(g)` is a nonpositive multiple of the coroot, by submultiplicativity of the lattice
norms on exterior powers (the dual lattice on the isotropic part).  Specialness is not imposed
beyond the Iwasawa decompositions. -/
structure GoodK (L : d.FlagLeviDatum) where
  /-- the compact open subgroup -/
  K : Subgroup ↥d.G
  isOpen : IsOpen (K : Set ↥d.G)
  isCompact : IsCompact (K : Set ↥d.G)
  /-- `G = P K` for every `P ∈ 𝒫(M)` -/
  mul_eq : ∀ P ∈ d.parabolics L.M, ∀ g : ↥d.G, ∃ p ∈ P, ∃ k ∈ K, g = p * k
  /-- good position: `K` stabilizes weight-split lattices of `W` and `V` -/
  goodPositionW : StabilizesSplitLattice d.QW L.bW L.wtW (d.fst '' (K : Set ↥d.G))
  goodPositionV : StabilizesSplitLattice d.QV L.bV L.wtV (d.snd '' (K : Set ↥d.G))

/-- The Iwasawa pair `(P, K)` of a good `K` and `P ∈ 𝒫(M)`. -/
def GoodK.toIwasawaPair {L : d.FlagLeviDatum} (K : d.GoodK L) {P : Subgroup ↥d.G}
    (hP : P ∈ d.parabolics L.M) : IwasawaPair ↥d.G where
  P := P
  K := K.K
  isClosed_P := by obtain ⟨FW, FV, rfl, -⟩ := hP; exact d.isClosed_whittB FW FV
  isOpen_K := K.isOpen
  isCompact_K := K.isCompact
  mul_eq := K.mul_eq P hP

/-- **For `M = G`** (`𝒫(G) = {G}`) a compact open subgroup in good position is good. -/
def GoodK.ofEqTop {L : d.FlagLeviDatum} (hM : L.M = ⊤) (K : Subgroup ↥d.G)
    (hKo : IsOpen (K : Set ↥d.G)) (hKc : IsCompact (K : Set ↥d.G))
    (hW : StabilizesSplitLattice d.QW L.bW L.wtW (d.fst '' (K : Set ↥d.G)))
    (hV : StabilizesSplitLattice d.QV L.bV L.wtV (d.snd '' (K : Set ↥d.G))) : d.GoodK L where
  K := K
  isOpen := hKo
  isCompact := hKc
  mul_eq P hP g := by
    obtain ⟨FW, FV, rfl, hL⟩ := hP
    exact ⟨g, hL.le (hM ▸ Subgroup.mem_top g), 1, K.one_mem, (mul_one g).symm⟩
  goodPositionW := hW
  goodPositionV := hV

namespace ReducedLeviDatum

variable (L : d.ReducedLeviDatum)

/-! ## 3. `H_P` for every `P ∈ 𝒫(M)` -/

/-- **`H_P : G → a_M` for `P ∈ 𝒫(M)`** (Thesis §2.1; Beuzart-Plessis §1.1): `H_P(p k) = H_M(m)`
for `p = m u ∈ P`, `k ∈ K`.  Defined through flags `F_W`, `F_V` with `P = P_{F_W} × P_{F_V}`
chosen from `P ∈ 𝒫(M)`; any other choice gives the same map (`hPar_eq`). -/
def hPar (K : d.GoodK L.toFlagLeviDatum) (P : ↥(d.parabolics L.M)) : ↥d.G → L.aM :=
  L.hP P.2.choose_spec.choose_spec.2 K.K K.isOpen K.isCompact
    (P.2.choose_spec.choose_spec.1 ▸ K.mul_eq P P.2)

/-- `hPar` is `hP` for any flags defining `P`. -/
theorem hPar_eq (K : d.GoodK L.toFlagLeviDatum) (P : ↥(d.parabolics L.M)) {FW : IsotropicFlag d.QW}
    {FV : IsotropicFlag d.QV} (hP : (P : Subgroup ↥d.G) = d.whittB FW FV)
    (hL : d.IsLevi FW FV L.M) :
    L.hPar K P = L.hP hL K.K K.isOpen K.isCompact (hP ▸ K.mul_eq P P.2) :=
  L.hP_congr _ hL (P.2.choose_spec.choose_spec.1.symm.trans hP) _ _ _ _

/-- `H_P(g k) = H_P(g)` for `k ∈ K`. -/
theorem hPar_mul_right (K : d.GoodK L.toFlagLeviDatum) (P : ↥(d.parabolics L.M)) (g : ↥d.G)
    {k : ↥d.G}
    (hk : k ∈ K.K) : L.hPar K P (g * k) = L.hPar K P g :=
  L.hP_mul_right _ _ _ _ g hk

/-- `H_P(m g) = H_M(m) + H_P(g)` for `m ∈ M`. -/
theorem hPar_mul_left (K : d.GoodK L.toFlagLeviDatum) (P : ↥(d.parabolics L.M)) (m : ↥L.M)
    (g : ↥d.G) :
    L.hPar K P ((m : ↥d.G) * g) = L.HM m + L.hPar K P g :=
  L.hP_mul_left_of_mem _ _ _ _ m g

/-! ## 4. `a_G`, `A_M(F)` and the measure on `a_M^G` -/

/-- **`a_G ⊆ a_M`** (Beuzart-Plessis §1.1: `a_M = a_M^G ⊕ a_G`): the span of `H_M(A_G(F) ∩ M)`,
with `A_G(F)` the split centre of `G` (`GGPData.AG`; being central, it lies in every Levi
subgroup, so the intersection is all of `A_G(F)`, which is not needed here).  The inclusion
`a_G → a_M` is dual to the restriction `X^*(M) → X^*(A_G)` (with `X^*(G) ⊗ ℚ = X^*(A_G) ⊗ ℚ`),
and `H_G(A_G(F))` spans `a_G`. -/
def aG : Submodule ℝ L.aM :=
  Submodule.span ℝ (Set.range fun m : {m : ↥L.M // (m : ↥d.G) ∈ d.AG} => L.HM m)

instance isClosed_aG : IsClosed (L.aG : Set L.aM) := Submodule.isClosed_of_finiteDimensional _

/-- `a_M^G = a_M / a_G`, the space of the weight. -/
abbrev aMG : Type := L.aM ⧸ L.aG

instance : BorelSpace L.aMG := ⟨L.aG.continuous_mkQ.map_eq_borel L.aG.mkQ_surjective⟩

/-- **`A_M(F)`, the split component of the centre of `M`** (Thesis §2.1; Beuzart-Plessis §1.1:
`ã_{M,F} = H_M(A_M(F))`): the pairs in the split centres `wtScalar` of the two flag Levi
subgroups.  That this is the split centre uses that the datum is reduced (the weight-`0` spaces
are not hyperbolic planes). -/
def AMF : Subgroup ↥d.G :=
  ((wtScalar d.QW L.bW L.wtW).prod (wtScalar d.QV L.bV L.wtV)).map d.pair

/-- **The lattice `proj_M^G(H_M(A_M(F)))` in `a_M^G`** (Waldspurger 2010, §1.2): the subgroup of
`a_M / a_G` generated by the image of `ã_{M,F} = H_M(A_M(F) ∩ M)` (Beuzart-Plessis §1.1). -/
def latticeMG : AddSubgroup L.aMG :=
  AddSubgroup.closure (Set.range fun m : {m : ↥L.M // (m : ↥d.G) ∈ L.AMF} =>
    L.aG.mkQ (L.HM m))

/-- **`proj_M^G(H_M(A_M(F)))` is a lattice in `a_M^G`**: discrete and spanning.  Sketch: `H_M` of
an element of `A_M(F)` has `GL`-coordinates `(n_w log ‖t_w‖)_w` (`n_w` the dimension of the
weight-`w` space), and `log ‖F^×‖` is discrete in `ℝ`; the elements with one `t_w = ϖ` and the
others `1` exist by the surjectivity of `GSpin → SO` (`gspin_specP_surjective_SO`) and span the
`GL`-coordinates; `a_G` is spanned by `H_M(A_G(F)) ⊆ H_M(A_M(F))`, so the image is a lattice.
Stated for `toIntSubmodule`, so that the two parts are Mathlib's `DiscreteTopology` and
`IsZLattice ℝ` (whose only field is the span), which give the fundamental domains of finite positive
volume that `MeasureTheory.Measure.latticeHaar_fundamentalDomain` needs. -/
theorem latticeMG_isLattice :
    DiscreteTopology L.latticeMG.toIntSubmodule ∧
      Submodule.span ℝ (L.latticeMG.toIntSubmodule : Set L.aMG) = ⊤ := by
  sorry

/-! ## 5. The weight `v_M(g)` -/

/-- **Arthur's weight `v_M(g)`** (Thesis §2.6; Beuzart-Plessis §1.10, p. 36; Waldspurger 2010,
§2.3): the volume in `a_M^G` of the convex hull of the projections of the points `H_P(g)`,
`P ∈ 𝒫(M)`, for the Haar measure of Waldspurger 2010, §1.2 (`a_M^G / proj_M^G(H_M(A_M(F)))` has
volume `1`, `latticeMG`; see `MeasureTheory.Measure.latticeHaar_fundamentalDomain`).
The Thesis (§2.4) and Beuzart-Plessis (§1.6) normalize the measures on `a_M` and `a_G` instead
(`a_M / ã_{M,F}` and `a_G / ã_{G,F}` of volume `1`); the quotient measure they induce on `a_M^G` is
this one, because `ã_{M,F} ∩ a_G = ã_{G,F}`: `X_*(A_G)` is saturated in `X_*(A_M)` (the cokernel
`X_*(A_M/A_G)` is torsion-free).
Beuzart-Plessis (§1.9, §1.10) and the Thesis take the hull of the `H_P(g)`; Waldspurger 2010,
§2.1, attaches `c_P(λ) = e^{−λ(Y_P)}` to the points `Y_P`; the hull of the `−H_P(g)` has the same
volume
(`vM_eq_hullVolume_neg`).  Rescaling `H_M` (here `‖·‖` is `|·|_F^s`, so `HM` is `s` times the
thesis' `H_M`) rescales the lattice too, so `v_M` does not depend on it.  The definition uses no
finiteness of `𝒫(M)`; it is the real volume of the hull when the hull has finite measure, e.g.
when `𝒫(M)` is finite (`FlagLeviDatum.finite_parabolics`), and `0` otherwise.  The normalization
is meaningful once `latticeMG` is a lattice (`latticeMG_isLattice`, not yet proved): without a
fundamental domain `latticeHaar` is the junk measure `⊤ • addHaar`.  The weight is the sources'
`v_M` when `(H_P(g))_P` is positive (see `GoodK`). -/
def vM (K : d.GoodK L.toFlagLeviDatum) (g : ↥d.G) : ℝ :=
  Measure.hullVolume L.latticeMG
    (Set.range fun P : ↥(d.parabolics L.M) => L.aG.mkQ (L.hPar K P g))

/-- **`v_M` is left `M`-invariant** (Beuzart-Plessis §1.10): every `H_P(m g)` is
`H_M(m) + H_P(g)`, so the hull is translated. -/
theorem vM_mul_left (K : d.GoodK L.toFlagLeviDatum) (m : ↥L.M) (g : ↥d.G) :
    L.vM K ((m : ↥d.G) * g) = L.vM K g := by
  have : (Set.range fun P : ↥(d.parabolics L.M) => L.aG.mkQ (L.hPar K P ((m : ↥d.G) * g))) =
      L.aG.mkQ (L.HM m) +ᵥ Set.range fun P : ↥(d.parabolics L.M) => L.aG.mkQ (L.hPar K P g) := by
    rw [Set.vadd_set_range]
    congr 1
    funext P
    simp [hPar_mul_left, vadd_eq_add]
  rw [vM, this, Measure.hullVolume_vadd]
  rfl

/-- **`v_M` is right `K`-invariant** (Beuzart-Plessis §1.10). -/
theorem vM_mul_right (K : d.GoodK L.toFlagLeviDatum) (g : ↥d.G) {k : ↥d.G} (hk : k ∈ K.K) :
    L.vM K (g * k) = L.vM K g := by
  simp only [vM, L.hPar_mul_right K _ g hk]

/-- **Sign conventions**: the hull of the `−H_P(g)` (the points of Waldspurger 2010, §2.1,
`c_P(λ) = e^{−λ(Y_P)}`) has the same volume as the hull of the `H_P(g)` (Beuzart-Plessis §1.9,
p. 36). -/
theorem vM_eq_hullVolume_neg (K : d.GoodK L.toFlagLeviDatum) (g : ↥d.G) :
    L.vM K g = Measure.hullVolume L.latticeMG
      (Set.range fun P : ↥(d.parabolics L.M) => -L.aG.mkQ (L.hPar K P g)) := by
  rw [vM, ← Measure.hullVolume_neg, Set.neg_range]

/-! ## 6. `M = G` -/

/-- For empty flags all weights are `0`. -/
theorem wtW_eq_zero (hW : L.FW.len = 0) (j : L.ιW) : L.wtW j = 0 := by
  have h1 := L.hsW.wt_le j
  have h2 := L.hsW.neg_len_le j
  rw [hW] at h1 h2
  omega

theorem wtV_eq_zero (hV : L.FV.len = 0) (j : L.ιV) : L.wtV j = 0 := by
  have h1 := L.hsV.wt_le j
  have h2 := L.hsV.neg_len_le j
  rw [hV] at h1 h2
  omega

/-- **For empty flags `M = G`.** -/
theorem M_eq_top_of_len_eq_zero (hW : L.FW.len = 0) (hV : L.FV.len = 0) : L.M = ⊤ := by
  refine eq_top_iff.2 fun g _ => ⟨mem_flagLevi_iff.2 fun j i hi => ?_,
    mem_flagLevi_iff.2 fun j i hi => ?_⟩
  · exact absurd (by rw [L.wtW_eq_zero hW i, L.wtW_eq_zero hW j]) hi
  · exact absurd (by rw [L.wtV_eq_zero hV i, L.wtV_eq_zero hV j]) hi

/-- The `GL`-coordinates of `H_M(m)` vanish when the components of `m` are scalars (scalars act
trivially on `W` and `V`). -/
theorem HM_inl_inl_eq_zero (m : ↥L.M) {c : Fˣ} (h : d.fst m = scalarGSpin d.QW c)
    (i : Fin L.FW.len) : L.HM m (Sum.inl (Sum.inl i)) = 0 := by
  have e : L.char (Sum.inl (Sum.inl i)) m =
      wtDet (Q := d.QW) L.bW L.wtW ((i : ℤ) + 1) ⟨d.fst m, m.2.1⟩ := rfl
  have : ((L.char (Sum.inl (Sum.inl i)) m : Fˣ) : F) = 1 := by
    rw [e, wtDet_apply]
    simp only [h, specP_scalarGSpin_eq_one]
    exact (congrArg LinearMap.det (wtBlock_id _)).trans LinearMap.det_id
  simp [HM, this]

theorem HM_inr_inl_eq_zero (m : ↥L.M) {c : Fˣ} (h : d.snd m = scalarGSpin d.QV c)
    (i : Fin L.FV.len) : L.HM m (Sum.inr (Sum.inl i)) = 0 := by
  have e : L.char (Sum.inr (Sum.inl i)) m =
      wtDet (Q := d.QV) L.bV L.wtV ((i : ℤ) + 1) ⟨d.snd m, m.2.2⟩ := rfl
  have : ((L.char (Sum.inr (Sum.inl i)) m : Fˣ) : F) = 1 := by
    rw [e, wtDet_apply]
    simp only [h, specP_scalarGSpin_eq_one]
    exact (congrArg LinearMap.det (wtBlock_id _)).trans LinearMap.det_id
  simp [HM, this]

/-- **The two `GSpin`-coordinate vectors lie in `a_G`**: `H_M` of the central scalars `(c, 1)`,
`(1, c)` of `A_G(F)` is `2^{dim} log ‖c‖` times them (`detChar` is `c ↦ c^{2^{dim}}` on scalars,
and the scalars act trivially on `V`, so their `GL`-coordinates vanish). -/
theorem single_gspin_mem_aG : Pi.single (Sum.inl (Sum.inr ())) (1 : ℝ) ∈ L.aG ∧
    Pi.single (Sum.inr (Sum.inr ())) (1 : ℝ) ∈ L.aG := by
  classical
  obtain ⟨τ, hτ0, hτ1⟩ := NormedField.exists_norm_lt_one F
  have hτ : τ ≠ 0 := norm_pos_iff.1 hτ0
  set c : Fˣ := Units.mk0 τ hτ
  have hlog : Real.log ‖τ‖ ≠ 0 := (Real.log_neg hτ0 hτ1).ne
  have hNW : (finrank F (CliffordAlgebra d.QW) : ℝ) ≠ 0 := by
    rw [finrank_cliffordAlgebra]; positivity
  have hNV : (finrank F (CliffordAlgebra d.QV) : ℝ) ≠ 0 := by
    rw [finrank_cliffordAlgebra]; positivity
  let mW : {m : ↥L.M // (m : ↥d.G) ∈ d.AG} :=
    ⟨⟨d.pair (scalarGSpin d.QW c, 1), scalarGSpin_mem_flagLevi (Q := d.QW) L.bW L.wtW c,
      (flagLevi (Q := d.QV) L.bV L.wtV).one_mem⟩,
      ⟨_, ⟨scalarGSpin_mem_splitCentralGSpin _ c, Subgroup.one_mem _⟩, rfl⟩⟩
  let mV : {m : ↥L.M // (m : ↥d.G) ∈ d.AG} :=
    ⟨⟨d.pair (1, scalarGSpin d.QV c), (flagLevi (Q := d.QW) L.bW L.wtW).one_mem,
      scalarGSpin_mem_flagLevi (Q := d.QV) L.bV L.wtV c⟩,
      ⟨_, ⟨Subgroup.one_mem _, scalarGSpin_mem_splitCentralGSpin _ c⟩, rfl⟩⟩
  have hmW : L.HM mW = ((finrank F (CliffordAlgebra d.QW) : ℝ) * Real.log ‖τ‖) •
      Pi.single (Sum.inl (Sum.inr ())) 1 := by
    funext x
    rcases x with (i | _) | (i | _)
    · simpa using L.HM_inl_inl_eq_zero mW.1 (c := c) rfl i
    · simp [mW, HM, char, fst_pair, detChar_scalarGSpin, c, norm_pow, Real.log_pow]
    · simpa using L.HM_inr_inl_eq_zero mW.1 (c := 1) (by simp [mW, snd_pair]) i
    · simp [mW, HM, char, snd_pair]
  have hmV : L.HM mV = ((finrank F (CliffordAlgebra d.QV) : ℝ) * Real.log ‖τ‖) •
      Pi.single (Sum.inr (Sum.inr ())) 1 := by
    funext x
    rcases x with (i | _) | (i | _)
    · simpa using L.HM_inl_inl_eq_zero mV.1 (c := 1) (by simp [mV, fst_pair]) i
    · simp [mV, HM, char, fst_pair]
    · simpa using L.HM_inr_inl_eq_zero mV.1 (c := c) rfl i
    · simp [mV, HM, char, snd_pair, detChar_scalarGSpin, c, norm_pow, Real.log_pow]
  constructor
  · have h := L.aG.smul_mem ((finrank F (CliffordAlgebra d.QW) : ℝ) * Real.log ‖τ‖)⁻¹
      (Submodule.subset_span ⟨mW, rfl⟩ : L.HM mW ∈ L.aG)
    rwa [hmW, smul_smul, inv_mul_cancel₀ (mul_ne_zero hNW hlog), one_smul] at h
  · have h := L.aG.smul_mem ((finrank F (CliffordAlgebra d.QV) : ℝ) * Real.log ‖τ‖)⁻¹
      (Submodule.subset_span ⟨mV, rfl⟩ : L.HM mV ∈ L.aG)
    rwa [hmV, smul_smul, inv_mul_cancel₀ (mul_ne_zero hNV hlog), one_smul] at h

/-- `a_G = a_M` as soon as every coordinate vector lies in `a_G`. -/
theorem aG_eq_top_of_single_mem (h : ∀ x : L.Coord, Pi.single x (1 : ℝ) ∈ L.aG) : L.aG = ⊤ := by
  classical
  rw [eq_top_iff, ← (Pi.basisFun ℝ L.Coord).span_eq, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  simpa using h x

/-- **For empty flags `a_M = a_G`**: `a_M` has only the two `GSpin`-coordinates
(`single_gspin_mem_aG`). -/
theorem aG_eq_top_of_len_eq_zero (hW : L.FW.len = 0) (hV : L.FV.len = 0) : L.aG = ⊤ :=
  L.aG_eq_top_of_single_mem fun x => by
    rcases x with (i | _) | (i | _)
    · exact absurd (i.isLt.trans_eq hW) (Nat.not_lt_zero _)
    · exact L.single_gspin_mem_aG.1
    · exact absurd (i.isLt.trans_eq hV) (Nat.not_lt_zero _)
    · exact L.single_gspin_mem_aG.2

/-- **`v_M = 1` when `a_M = a_G`** (e.g. `M = G`, Beuzart-Plessis §1.10 with `𝒫(G) = {G}`): the
hull of a nonempty set in the zero space has volume `1`. -/
theorem vM_eq_one_of_aG_eq_top (hG : L.aG = ⊤) (K : d.GoodK L.toFlagLeviDatum) (g : ↥d.G) :
    L.vM K g = 1 := by
  have : Subsingleton L.aMG := Submodule.Quotient.subsingleton_iff.2 hG
  exact Measure.hullVolume_of_subsingleton _
    ⟨_, ⟨⟨_, L.toFlagLeviDatum.mem_parabolics⟩, rfl⟩⟩

/-- **`v_G = 1`**: for empty flags (`M = G`, `M_eq_top_of_len_eq_zero`) the weight is `1`. -/
theorem vM_eq_one_of_len_eq_zero (hW : L.FW.len = 0) (hV : L.FV.len = 0)
    (K : d.GoodK L.toFlagLeviDatum)
    (g : ↥d.G) : L.vM K g = 1 :=
  L.vM_eq_one_of_aG_eq_top (L.aG_eq_top_of_len_eq_zero hW hV) K g

end ReducedLeviDatum

end GGPData

end GSpinGGP
