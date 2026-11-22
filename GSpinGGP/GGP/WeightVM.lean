/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.LeviLattice
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
  position relative to `M` (it stabilizes weight-split lattices of `W` and `V`).  Examples:
  `GoodK.ofEqTop` for `M = G`; a lattice stabilizer (`GGP/LatticeK.lean`) for a maximal torus of
  `GL₁ × GSpin₃` (`Sanity/GL2GoodK.lean`).
* `GGPData.ReducedLeviDatum.hPar`: `H_P : G → a_M` for each `P ∈ 𝒫(M)` (any flags defining `P`
  give the same map, `hPar_eq`).
* `GGPData.ReducedLeviDatum.aG`: `a_G ⊆ a_M`, spanned by `H_M(A_G(F))`; `IsCentralCoord`: the
  coordinates of `a_M` that lie in `a_G` (`mem_aG_iff`).
* `GGPData.ReducedLeviDatum.latticeMG`: `proj_M^G(H_M(A_M(F)))` in `a_M / a_G`.
* `GGPData.ReducedLeviDatum.vM`: the weight `v_M(g)`.

## Main results

* `latticeMG_isLattice`: `proj_M^G(H_M(A_M(F)))` is a lattice in `a_M^G`, so `latticeHaar` gives
  its fundamental domains volume `1` (`exists_isAddFundamentalDomain_latticeHaar_eq_one`).
* `vM_mul_left`: `v_M(m g) = v_M(g)` for `m ∈ M`.
* `vM_mul_right`: `v_M(g k) = v_M(g)` for `k ∈ K`.
* `continuous_vM`: `v_M` is locally constant.
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

/-- **The lattice `proj_M^G(H_M(A_M(F)))` in `a_M^G`** (Waldspurger 2010, §1.2): the subgroup of
`a_M / a_G` generated by the image of `ã_{M,F} = H_M(A_M(F) ∩ M)` (Beuzart-Plessis §1.1). -/
def latticeMG : AddSubgroup L.aMG :=
  AddSubgroup.closure (Set.range fun m : {m : ↥L.M // (m : ↥d.G) ∈ L.AMF} =>
    L.aG.mkQ (L.HM m))

/-! ### `a_G` is a coordinate subspace -/

/-- **The two `GSpin`-coordinate vectors lie in `a_G`**: `H_M` of the central scalars `(c, 1)`,
`(1, c)` of `A_G(F)` is `2^{dim} log ‖c‖` times them (`HM_scalarW`, `HM_scalarV`). -/
theorem single_gspin_mem_aG : Pi.single (Sum.inl (Sum.inr ())) (1 : ℝ) ∈ L.aG ∧
    Pi.single (Sum.inr (Sum.inr ())) (1 : ℝ) ∈ L.aG :=
  L.single_gspin_mem
    (fun c => Submodule.subset_span ⟨⟨L.scalarW c,
      ⟨_, ⟨scalarGSpin_mem_splitCentralGSpin _ c, Subgroup.one_mem _⟩, rfl⟩⟩, rfl⟩)
    (fun c => Submodule.subset_span ⟨⟨L.scalarV c,
      ⟨_, ⟨Subgroup.one_mem _, scalarGSpin_mem_splitCentralGSpin _ c⟩, rfl⟩⟩, rfl⟩)

/-- **The coordinates of `a_M` that lie in `a_G`**: the two `GSpin`-coordinates, and all the
coordinates of a factor `GSpin(W)` or `GSpin(V)` that is a hyperbolic plane (then that factor is a
split torus, `splitCentralGSpin = ⊤`, and `A_G(F)` contains the whole of its part of `A_M(F)`). -/
def IsCentralCoord : L.Coord → Prop
  | Sum.inl (Sum.inl _) => IsHypPlane d.QW
  | Sum.inl (Sum.inr _) => True
  | Sum.inr (Sum.inl _) => IsHypPlane d.QV
  | Sum.inr (Sum.inr _) => True

/-- The coordinate vectors of the central coordinates lie in `a_G`. -/
theorem single_mem_aG {c : L.Coord} (hc : L.IsCentralCoord c) : Pi.single c (1 : ℝ) ∈ L.aG := by
  classical
  rcases c with (i | _) | (i | _)
  · obtain ⟨T, m, hmT, -, a, ha, he⟩ := L.exists_HM_torusW i
    have hAG : (m : ↥d.G) ∈ d.AG := hmT ▸ ⟨(T, 1), ⟨by
      rw [splitCentralGSpin, ite_eq_left_of_eq_true _ _ (eq_true (show IsHypPlane d.QW from hc))]; trivial,
      Subgroup.one_mem _⟩, rfl⟩
    have hm0 : L.HM m ∈ L.aG := Submodule.subset_span ⟨⟨m, hAG⟩, rfl⟩
    generalize L.HM m (Sum.inl (Sum.inr ())) = x at he
    rw [he] at hm0
    have h := L.aG.sub_mem hm0 (L.aG.smul_mem x L.single_gspin_mem_aG.1)
    rw [add_sub_cancel_right] at h
    exact L.single_mem_of_smul_mem ha h
  · exact L.single_gspin_mem_aG.1
  · obtain ⟨T, m, hmT, -, a, ha, he⟩ := L.exists_HM_torusV i
    have hAG : (m : ↥d.G) ∈ d.AG := hmT ▸ ⟨(1, T), ⟨Subgroup.one_mem _, by
      rw [splitCentralGSpin, ite_eq_left_of_eq_true _ _ (eq_true (show IsHypPlane d.QV from hc))]; trivial⟩, rfl⟩
    have hm0 : L.HM m ∈ L.aG := Submodule.subset_span ⟨⟨m, hAG⟩, rfl⟩
    generalize L.HM m (Sum.inr (Sum.inr ())) = x at he
    rw [he] at hm0
    have h := L.aG.sub_mem hm0 (L.aG.smul_mem x L.single_gspin_mem_aG.2)
    rw [add_sub_cancel_right] at h
    exact L.single_mem_of_smul_mem ha h
  · exact L.single_gspin_mem_aG.2

/-- On `A_G(F)`, the coordinates of `H_M` that are not central vanish: the factor of `A_G(F)` in a
`GSpin` that is not a hyperbolic plane is the scalars, which act trivially. -/
theorem HM_apply_eq_zero_of_mem_AG {m : ↥L.M} (hm : (m : ↥d.G) ∈ d.AG) {c : L.Coord}
    (hc : ¬ L.IsCentralCoord c) : L.HM m c = 0 := by
  obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩ := hm
  rcases c with (i | _) | (i | _)
  · have hW : ¬ IsHypPlane d.QW := hc
    rw [splitCentralGSpin, ite_eq_right_of_eq_false _ _ (eq_false hW)] at hx
    obtain ⟨c, rfl⟩ := hx
    exact L.HM_inl_inl_eq_zero m (c := c) (by rw [← hxy, fst_pair]) i
  · exact absurd trivial hc
  · have hV : ¬ IsHypPlane d.QV := hc
    rw [splitCentralGSpin, ite_eq_right_of_eq_false _ _ (eq_false hV)] at hy
    obtain ⟨c, rfl⟩ := hy
    exact L.HM_inr_inl_eq_zero m (c := c) (by rw [← hxy, snd_pair]) i
  · exact absurd trivial hc

/-- **`a_G` is the span of the central coordinate vectors**: `H ∈ a_G` iff the coordinates of `H`
that are not central vanish. -/
theorem mem_aG_iff {H : L.aM} : H ∈ L.aG ↔ ∀ c, ¬ L.IsCentralCoord c → H c = 0 := by
  classical
  constructor
  · intro hH
    let S : Submodule ℝ L.aM :=
      { carrier := {H | ∀ c, ¬ L.IsCentralCoord c → H c = 0}
        add_mem' := fun ha hb c hc => by simp [ha c hc, hb c hc]
        zero_mem' := fun _ _ => rfl
        smul_mem' := fun a H hH c hc => by simp [hH c hc] }
    have : L.aG ≤ S := Submodule.span_le.2 (by
      rintro _ ⟨m, rfl⟩
      exact fun c hc => L.HM_apply_eq_zero_of_mem_AG m.2 hc)
    exact this hH
  · intro hH
    rw [← (Pi.basisFun ℝ L.Coord).sum_repr H]
    refine Submodule.sum_mem _ fun c _ => ?_
    simp only [Pi.basisFun_repr, Pi.basisFun_apply]
    by_cases hc : L.IsCentralCoord c
    · exact L.aG.smul_mem _ (L.single_mem_aG hc)
    · rw [hH c hc, zero_smul]; exact L.aG.zero_mem

/-- **`a_M^G ≠ 0`** as soon as some coordinate is not central (a `GL`-coordinate of a factor that is
not a hyperbolic plane, i.e. a nonempty flag in it). -/
theorem nontrivial_aMG {c : L.Coord} (hc : ¬ L.IsCentralCoord c) : Nontrivial L.aMG := by
  classical
  refine ⟨⟨L.aG.mkQ (Pi.single c 1), 0, fun h => ?_⟩⟩
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, L.mem_aG_iff] at h
  simpa using h c hc

/-- **`proj_M^G(H_M(A_M(F)))` is a lattice in `a_M^G`**: discrete and spanning.  Spanning:
`H_M(A_M(F))` spans `a_M` (`span_HMAMF_eq_top`).  Discreteness: `a_G` is the span of the central
coordinate vectors (`mem_aG_iff`), so the projection to the other coordinates identifies `a_M^G`
with a coordinate space, in which the image of `H_M(M(F))` lies in `(ℤ ℓ)^{coordinates}`
(`exists_HM_mem_zmultiples`; the value group of `F` is cyclic).
Stated for `toIntSubmodule`, so that the two parts are Mathlib's `DiscreteTopology` and
`IsZLattice ℝ` (whose only field is the span), which give the fundamental domains of finite positive
volume that `MeasureTheory.Measure.latticeHaar_fundamentalDomain` needs
(`exists_isAddFundamentalDomain_latticeHaar_eq_one`). -/
theorem latticeMG_isLattice :
    DiscreteTopology L.latticeMG.toIntSubmodule ∧
      Submodule.span ℝ (L.latticeMG.toIntSubmodule : Set L.aMG) = ⊤ := by
  classical
  obtain ⟨ℓ, -, hZ⟩ := L.exists_HM_mem_zmultiples
  let π : L.aM →ₗ[ℝ] ({c : L.Coord // ¬ L.IsCentralCoord c} → ℝ) :=
    LinearMap.pi fun c => LinearMap.proj c.1
  have hle : L.aG ≤ LinearMap.ker π := fun H hH => by
    rw [LinearMap.mem_ker]
    funext c
    exact L.mem_aG_iff.1 hH c.1 c.2
  let ψ := L.aG.liftQ π hle
  have hψ : ∀ H, ψ (L.aG.mkQ H) = π H := fun H => rfl
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot]
    refine Submodule.ker_liftQ_eq_bot _ _ _ fun H hH => L.mem_aG_iff.2 fun c hc => ?_
    exact congrFun (LinearMap.mem_ker.1 hH) ⟨c, hc⟩
  have hψc : Continuous ψ := by
    rw [L.aG.isQuotientMap_mkQ.continuous_iff]
    exact π.continuous_of_finiteDimensional
  have hmem : ∀ x ∈ L.latticeMG, ∀ c, ψ x c ∈ AddSubgroup.zmultiples ℓ := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      exact fun c => by rw [hψ]; exact hZ m c.1
    | zero => exact fun c => by simp
    | add x y _ _ hx hy => exact fun c => by rw [map_add]; exact add_mem (hx c) (hy c)
    | neg x _ hx => exact fun c => by rw [map_neg]; exact neg_mem (hx c)
  refine ⟨?_, ?_⟩
  · let f : L.latticeMG.toIntSubmodule → ({c : L.Coord // ¬ L.IsCentralCoord c} →
        AddSubgroup.zmultiples ℓ) := fun x c => ⟨ψ x c, hmem x x.2 c⟩
    have hf : Continuous f := continuous_pi fun c =>
      ((continuous_apply c).comp (hψc.comp continuous_subtypeVal)).subtype_mk _
    have hfi : Function.Injective f := fun x y h =>
      Subtype.ext (hψinj (funext fun c => congrArg Subtype.val (congrFun h c)))
    exact DiscreteTopology.of_continuous_injective hf hfi
  · rw [eq_top_iff, ← L.aG.range_mkQ, LinearMap.range_eq_map, ← L.span_HMAMF_eq_top,
      Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    exact AddSubgroup.subset_closure ⟨m, rfl⟩

/-- **The normalization of `v_M` is a genuine Haar measure**: `a_M^G` has a fundamental domain for
`proj_M^G(H_M(A_M(F)))` (`latticeMG_isLattice`), of volume `1` for `latticeHaar`; so
`latticeHaar latticeMG` is the Haar measure of Waldspurger 2010, §1.2, not the junk value
`⊤ • addHaar`. -/
theorem exists_isAddFundamentalDomain_latticeHaar_eq_one :
    ∃ D : Set L.aMG, IsAddFundamentalDomain L.latticeMG.toIntSubmodule D Measure.addHaar ∧
      Measure.latticeHaar L.latticeMG D = 1 := by
  obtain ⟨h1, h2⟩ := L.latticeMG_isLattice
  have : IsZLattice ℝ L.latticeMG.toIntSubmodule := ⟨h2⟩
  have : Module.Free ℤ L.latticeMG.toIntSubmodule := ZLattice.module_free ℝ _
  have : Module.Finite ℤ L.latticeMG.toIntSubmodule := ZLattice.module_finite ℝ _
  have hD := ZSpan.isAddFundamentalDomain
    ((Module.Free.chooseBasis ℤ L.latticeMG.toIntSubmodule).ofZLatticeBasis ℝ
      L.latticeMG.toIntSubmodule)
    (Measure.addHaar : Measure L.aMG)
  rw [Module.Basis.ofZLatticeBasis_span] at hD
  refine ⟨_, hD, ?_⟩
  have h := Measure.latticeHaar_fundamentalDomain_of_isZLattice _ hD
  rwa [AddSubgroup.toIntSubmodule_toAddSubgroup] at h

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
is meaningful because `latticeMG` is a lattice (`latticeMG_isLattice`): `latticeHaar` gives its
fundamental domains volume `1` (`exists_isAddFundamentalDomain_latticeHaar_eq_one`).  The weight is the sources'
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

/-- **`v_M` is locally constant**, hence continuous: it is right `K`-invariant (`vM_mul_right`) and
`K` is open. -/
theorem continuous_vM (K : d.GoodK L.toFlagLeviDatum) : Continuous (L.vM K) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hn : (g * ·) '' (K.K : Set ↥d.G) ∈ nhds g := by
    have := (Homeomorph.mulLeft g).isOpenMap _ K.isOpen
    refine this.mem_nhds ⟨1, K.K.one_mem, mul_one g⟩
  refine (continuousAt_const (y := L.vM K g)).congr (Filter.mem_of_superset hn ?_)
  rintro _ ⟨k, hk, rfl⟩
  exact (L.vM_mul_right K g hk).symm

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
