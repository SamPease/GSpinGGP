import GSpinGGP.Foundations.LocalGroups
import GSpinGGP.Foundations.Representations
import GSpinGGP.Foundations.GSpin

/-!
# GGP-specific assembly: multiplicities, packets, `Γ(G,H)`, `m_geom`, the multiplicity formula

Layer 2.  Everything specific to a GGP triple `(G, H, ξ)` of general spin groups that the main
theorem and the trace-formula programme need to *state* their results:

* `mult ψ d π = m(π)` (Thesis §5.5) and `charG d π = θ_π` (Thesis Ch. 1);
* the Kottwitz sign `kottwitzSign`;
* `InnerFormSystem d`: the inner forms `(G_α, H_α, ξ_α)` of the triple (Thesis §6.2);
* `IsStableFn`, `IsTransfer`, `TemperedPacketFamily` (STAB, TRANS, WHITT; Thesis §6.3);
* `Γ(G,H)`: `torusOf`, `IsGammaElt`, `GammaClass`, `weylCard`, `deltaGGP` (Thesis §6.5,
  (6.5.9));
* the orbit choice `orbitChoice` (after Luo §7.1);
* `mGeom` (Thesis §7.2, Prop. 12.1.1) and the statement
  `MultiplicityFormula` of Thesis Thm. 7.2.2 (= Thm. 1.0.2), and its body `MultAt` at one datum;
* virtual tempered representations (Thesis §3.4, §7.4): `IsTempCC`, `TempClass`,
  `VirtualTemp = R_temp(G,η) ⊗ ℂ`, and the linear maps `vChar`, `vMult`, `vMGeom`, `defect`.

Only own (citation-free) lemmas are stated here; literature results are in `Literature/`.

Conventions: `F` is a `p`-adic field (`PAdicField`), `ψ : NontrivialAddChar F`.
`W = F^m`, `V = W ⊕ Z` as in `GGPData` (`Foundations/GSpin.lean`).
-/

noncomputable section

open MeasureTheory Filter Topology Module
open scoped Classical

/- The commutator Lie structure on associative algebras is only a local instance in Mathlib. -/
attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-! ## 0. Topological instances on `G(F)` -/

namespace GGPData

/-- `G(F)` is Hausdorff (bridging instance: `subgroup_t2Space` in `LocalGroups` is a theorem,
since its conclusion does not mention `F`; here `d` mentions `F`, so an instance is fine). -/
instance instT2SpaceG (d : GGPData F) : T2Space ↥d.G :=
  subgroup_t2Space F d.ambient d.G

/-- `G(F)` is locally compact (it is closed in `(C(W) × C(V))^×`, `GGPData.isClosed_G`). -/
instance instLocallyCompactSpaceG (d : GGPData F) : LocallyCompactSpace ↥d.G :=
  subgroup_locallyCompactSpace_of_isClosed F d.ambient d.G d.isClosed_G

/- Instance search does not find the two instances above for the inner forms `d.twist τ`
(`twist` is an `abbrev` whose structure-literal unfolding changes the discrimination-tree key),
so we restate them for `d.twist τ`. -/
instance instT2SpaceTwistG (d : GGPData F) (τ : InnerTwist d.QW) : T2Space ↥(d.twist τ).G :=
  instT2SpaceG (d.twist τ)

instance instLocallyCompactSpaceTwistG (d : GGPData F) (τ : InnerTwist d.QW) :
    LocallyCompactSpace ↥(d.twist τ).G :=
  instLocallyCompactSpaceG (d.twist τ)

end GGPData

/-! ## 1. The multiplicity and characters -/

/-- The multiplicity `m(π) = dim Hom_{H(F)}(π^∞, ξ)` of the GGP triple attached to `d`
(Thesis §5.5), where `ξ(h) = ψ(λ(h))`. -/
def mult (ψ : NontrivialAddChar F) (d : GGPData F) (π : UnitaryRep ↥d.G) : ℕ∞ :=
  multiplicity π d.H (d.xi ψ.toAddChar)

/-- The Harish-Chandra character `θ_π` of `π`, normalized to be locally constant on the regular
semisimple set `G_reg(F)` (Thesis Ch. 1). -/
def charG (d : GGPData F) (π : UnitaryRep ↥d.G) : ↥d.G → ℂ :=
  characterOn π (regularSet d.G d.lie)

/-- The Kottwitz sign `e(G_α)` of the inner form attached to the twist `τ`, by its `p`-adic
formula `e(G_α) = (-1)^{rk_F G - rk_F G_α} = (-1)^{w(W)+w(W_α)+w(V)+w(V_α)}`
(`w` = Witt index).  That this equals Kottwitz's
cohomological sign is Kottwitz 1983 (not formalized). -/
def kottwitzSign (d : GGPData F) (τ : InnerTwist d.QW) : ℤ :=
  (-1) ^ (wittIndex d.QW + wittIndex (d.twist τ).QW + wittIndex d.QV + wittIndex (d.twist τ).QV)

/-- The trivial twist has Kottwitz sign `1`. -/
theorem kottwitzSign_refl (d : GGPData F) : kottwitzSign d d.reflTwist = 1 := by
  unfold kottwitzSign
  have : wittIndex d.QW + wittIndex (d.twist d.reflTwist).QW + wittIndex d.QV +
      wittIndex (d.twist d.reflTwist).QV = 2 * (wittIndex d.QW + wittIndex d.QV) := by
    show wittIndex d.QW + wittIndex d.QW + wittIndex d.QV + wittIndex d.QV = _
    ring
  rw [this, pow_mul]
  norm_num

/-- The Kottwitz sign is a sign. -/
theorem kottwitzSign_eq_one_or (d : GGPData F) (τ : InnerTwist d.QW) :
    kottwitzSign d τ = 1 ∨ kottwitzSign d τ = -1 := by
  unfold kottwitzSign
  exact neg_one_pow_eq_or ℤ _

/-- The trivial inner form of `d` is `d` itself (definitionally). -/
theorem GGPData.twist_reflTwist (d : GGPData F) : d.twist d.reflTwist = d := rfl

/-! ## 2. Inner forms (Thesis §6.2) -/

/-- A system of representatives of the inner forms of the GGP triple attached to `d`:
an index set `Idx` with, for each `α`, an inner twist
`(W_α, φ_α)` of `W`, the base point `α = 1` being the trivial twist, such that every
nondegenerate quadratic form on `F^m` with the same discriminant as `W` is isometric to exactly
one `W_α`.  (So `Idx ≃ H^1(F, SO(W)) = H^1(F, H/Z_{G,H})`.)  This differs from Thesis §6.2:
the inner forms are indexed by `H¹(F, SO(W))`, not `H¹(F, PGSpin(W))`. -/
structure InnerFormSystem (d : GGPData F) where
  /-- the index set, `≃ H^1(F, SO(W))` -/
  Idx : Type
  /-- the twist `(W_α, φ_α)` -/
  twist : Idx → InnerTwist d.QW
  /-- the base point `α = 1` -/
  base : Idx
  twist_base : twist base = d.reflTwist
  /-- every form of the same dimension and discriminant is isometric to exactly one `W_α` -/
  classify : ∀ Q' : QuadraticForm F (Fin d.m → F), IsNondeg Q' → SameDisc d.QW Q' →
    ∃! α : Idx, Nonempty (Q'.IsometryEquiv (twist α).Q')

namespace InnerFormSystem

variable {d : GGPData F} (IF : InnerFormSystem d)

/-- The GGP datum `(W_α, V_α = W_α ⊕ Z)` of the inner form `α`. -/
abbrev data (α : IF.Idx) : GGPData F := d.twist (IF.twist α)

/-- The base inner form is `d` itself. -/
theorem data_base : IF.data IF.base = d := by
  rw [data, IF.twist_base]
  rfl

/-- Transport `G(F) → G_{base}(F)` along `data_base` (a cast; it is the identity once
`twist_base` is substituted). -/
def toBase (x : ↥d.G) : ↥(IF.data IF.base).G :=
  cast (congrArg (fun e : GGPData F => (↥e.G : Type _)) IF.data_base.symm) x

end InnerFormSystem

/-! ## 3. Stability, transfer, tempered packets (Thesis §6.1, §6.3) -/

/-- **(STAB)** `θ` is stable: constant on stable conjugacy classes of regular semisimple
elements (Thesis §6.1). -/
def IsStableFn (d : GGPData F) (θ : ↥d.G → ℂ) : Prop :=
  ∀ x y : ↥d.G, x ∈ regularSet d.G d.lie → y ∈ regularSet d.G d.lie →
    d.StablyConj x y → θ x = θ y

/-- **(TRANS)** `θ'` on `G_α(F)` is a transfer of `θ` on `G(F)`: `θ'(y) = θ(x)` whenever
`x ∈ G_reg(F)` and `y ∈ G_{α,reg}(F)` are stably conjugate through `ψ_α`
(Thesis §6.1). -/
def IsTransfer (d : GGPData F) (τ : InnerTwist d.QW) (θ : ↥d.G → ℂ)
    (θ' : ↥(d.twist τ).G → ℂ) : Prop :=
  ∀ (x : ↥d.G) (y : ↥(d.twist τ).G), x ∈ regularSet d.G d.lie →
    y ∈ regularSet (d.twist τ).G (d.twist τ).lie → d.StablyConjG τ x y → θ' y = θ x

/-- A family of tempered `L`-packets `Π_α ⊂ Temp(G_α)` for all inner forms, satisfying the
hypotheses of the main theorem (Thesis §6.3 and Thm. 6.4.1):
finite families of pairwise inequivalent irreducible tempered representations
with central character trivial on `Z_{G,H}(F) = A_{G,H}(F)`, with
* **(STAB)** `θ_α = Σ_{π ∈ Π_α} θ_π` stable;
* **(TRANS)** `θ_α(y) = e(G_α) θ_1(x)` for stably conjugate regular `x ∈ G(F)`, `y ∈ G_α(F)`;
* **(WHITT)** for every Whittaker datum of `G` exactly one member of `Π_1` has a model.
The Langlands parameter itself is not modelled. -/
structure TemperedPacketFamily (d : GGPData F) (IF : InnerFormSystem d) where
  /-- the index set of the packet `Π_α` -/
  ι : IF.Idx → Type
  [fintype : ∀ α, Fintype (ι α)]
  /-- the members of `Π_α` -/
  rep : ∀ α, ι α → UnitaryRep ↥(IF.data α).G
  tempered : ∀ α i, IsTempered (rep α i)
  inequiv : ∀ α (i j : ι α), i ≠ j → ¬ (rep α i).IsEquivalent (rep α j)
  central_trivial : ∀ α i, IsTrivialOn (rep α i) ((IF.data α).AGH : Set ↥(IF.data α).G)
  /-- **(STAB)** -/
  stab : ∀ α, IsStableFn (IF.data α) (fun y => ∑ i, charG (IF.data α) (rep α i) y)
  /-- **(TRANS)** -/
  trans : ∀ α (x : ↥d.G) (y : ↥(IF.data α).G), x ∈ regularSet d.G d.lie →
    y ∈ regularSet (IF.data α).G (IF.data α).lie → d.StablyConjG (IF.twist α) x y →
    ∑ i, charG (IF.data α) (rep α i) y =
      (kottwitzSign d (IF.twist α) : ℂ) *
        ∑ i, charG (IF.data IF.base) (rep IF.base i) (IF.toBase x)
  /-- **(WHITT)** -/
  whitt : ∀ w : WhittakerDatum (IF.data IF.base),
    ∃! i : ι IF.base, HasModel (rep IF.base i) w.U w.χ

attribute [instance] TemperedPacketFamily.fintype

/-- The stable character `θ_α = Σ_{π ∈ Π_α} θ_π` of the packet `Π_α` (Thesis §6.3). -/
def TemperedPacketFamily.packetChar {d : GGPData F} {IF : InnerFormSystem d}
    (P : TemperedPacketFamily d IF) (α : IF.Idx) : ↥(IF.data α).G → ℂ :=
  fun y => ∑ i, charG (IF.data α) (P.rep α i) y

/-! ## 4. `Γ(G,H)` (Thesis §6.5) -/

section Gamma

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- The pointwise stabilizer `{g ∈ GSpin(V) | P(g)|_U = id}` of a subspace `U`. -/
def fixerOf (Q : QuadraticForm F V) (U : Submodule F V) : Subgroup ↥(GSpin Q) where
  carrier := {g | ∀ w ∈ U, specP Q g w = w}
  one_mem' := fun w _ => by simp
  mul_mem' := fun {g h} hg hh w hw => by
    rw [map_mul, LinearEquiv.mul_apply, hh w hw, hg w hw]
  inv_mem' := fun {g} hg w hw => by
    have h1 : specP Q g⁻¹ (specP Q g w) = w := by
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [hg w hw] at h1
    exact h1

/-- The common fixed space `⋂_{t ∈ T} ker(P(t) − 1)` of a subgroup `T ⊆ GSpin(V)`
(for `T = T_x` this is `W'_x`). -/
def commonFixed {Q : QuadraticForm F V} (T : Subgroup ↥(GSpin Q)) : Submodule F V :=
  ⨅ t : ↥T, fixedSub (t : ↥(GSpin Q))

omit [PAdicField F] in
/-- The central scalars commute with everything in `GSpin(V)`. -/
theorem scalarGSpin_commute (Q : QuadraticForm F V) (c : Fˣ) (g : ↥(GSpin Q)) :
    Commute (scalarGSpin Q c) g := by
  apply Subtype.ext
  apply Units.ext
  show (algebraMap F (CliffordAlgebra Q) (c : F)) * _ = _ * algebraMap F (CliffordAlgebra Q) (c : F)
  exact Algebra.commutes _ _

end Gamma

namespace GGPData

variable (d : GGPData F)

/-- The torus `T_x := GSpin(W''_x)_x = P^{-1}(Z_{SO(W''_x)}(x̄)^0)` attached to
`x ∈ GSpin(W)(F)`: the elements commuting with `x` and acting trivially on
`W'_x = ker(P(x) − 1)`.  (Commuting with `x` already forces
`P(g) ∈ Z(x̄)^0`.) It contains the central scalars `A_{G,H}`. -/
def torusOf (x : ↥(GSpin d.QW)) : Subgroup ↥(GSpin d.QW) :=
  Subgroup.centralizer {x} ⊓ fixerOf d.QW (fixedSub x)

/-- The scalars `A_{G,H}(F) = F^×` inside a subgroup `T` of `GSpin(W)(F)`. -/
def scalarsIn (T : Subgroup ↥(GSpin d.QW)) : Subgroup ↥T :=
  (scalarGSpin d.QW).range.subgroupOf T

instance scalarsIn_normal (T : Subgroup ↥(GSpin d.QW)) : (d.scalarsIn T).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf).mp hn
  refine Subgroup.mem_subgroupOf.mpr ⟨c, ?_⟩
  have hcomm : Commute (scalarGSpin d.QW c) (g : ↥(GSpin d.QW)) :=
    scalarGSpin_commute d.QW c g
  rw [hc] at hcomm
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc]
  rw [← hcomm.eq, mul_inv_cancel_right]

/-- The quotient `T(F)/A_{G,H}(F)`. -/
abbrev TorusQuot (T : Subgroup ↥(GSpin d.QW)) : Type _ := ↥T ⧸ d.scalarsIn T

/-- `x ∈ GSpin(W)(F)` defines an element of `Γ(G,H)`: `x` is semisimple,
`T_x` is a torus (its `F`-points commute; `T_x` is
connected by Steinberg, and `F`-points of a connected reductive group are Zariski dense), and
`T_x/A_{G,H}` is anisotropic, i.e. `T_x(F)/A_{G,H}(F)` is compact (Hilbert 90 identifies it with
`S_x(F)`).  This differs from Thesis §6.5, which requires `T_x` itself to be anisotropic. -/
def IsGammaElt (x : ↥(GSpin d.QW)) : Prop :=
  IsSS F (((x : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW) ∧
    (∀ a ∈ d.torusOf x, ∀ b ∈ d.torusOf x, Commute a b) ∧
    CompactSpace (d.TorusQuot (d.torusOf x))

/-- The tori `T_x` of elements `x` of `Γ(G,H)` (the set `𝒯`). -/
def GammaTorus : Type _ :=
  {T : Subgroup ↥(GSpin d.QW) // ∃ x, d.IsGammaElt x ∧ d.torusOf x = T}

/-- `GSpin(W)(F)`-conjugacy of subgroups. -/
def TorusConj (T T' : d.GammaTorus) : Prop :=
  ∃ g : ↥(GSpin d.QW), T'.1 = T.1.map (MulAut.conj g).toMonoidHom

end GGPData

/-- The index set of `Γ(G,H)`: `GSpin(W)(F)`-conjugacy classes of the tori `T_x`,
`x ∈ Γ(G,H)`. (Finite for `p`-adic `F`.) -/
def GammaClass (d : GGPData F) : Type _ := Quot d.TorusConj

/-- `|W(T)|` for `T = T_x`: the group `W(T) = N_{H(F)}(T)/Z_H(T)(F) = N_{GSpin(W)(F)}(T)/Z_{GSpin(W)(F)}(T)`
acting on the fibres of `A\T_♮(F) → Γ(G,H)` (Waldspurger 2010
§7.3, `W(H,T)`).  Normalizer and centralizer are taken in all of `GSpin(W)(F)`; the unipotent radical
of `H` does not contribute.  Via `P` this is `N_{O(W'')(F)}(S)/S(F)` if `W' ≠ 0` and
`W(GSpin(W''),T) = N_{SO(W'')(F)}(S)/S(F)` if `W' = 0`.
This differs from Thesis (6.5.3), which uses `N_{GSpin(W'')(F)}(T)/T(F)`;
that is smaller by a factor 2 on some components with `W' ≠ 0`, since
an element of determinant `−1` on `W''`, compensated by a reflection of `W'`, also conjugates
points of `T_♮`. -/
def weylCardOf (d : GGPData F) (T : Subgroup ↥(GSpin d.QW)) : ℕ :=
  Nat.card (↥(Subgroup.normalizer (T : Set ↥(GSpin d.QW))) ⧸
    (Subgroup.centralizer (T : Set ↥(GSpin d.QW))).subgroupOf
      (Subgroup.normalizer (T : Set ↥(GSpin d.QW))))

/-- `|W(T)|` for a class in `Γ(G,H)` (computed on a representative). -/
def weylCard (d : GGPData F) (c : GammaClass d) : ℕ :=
  weylCardOf d (Quot.out c).1

/-- `Δ(x) = |det((P(x) − 1)|_{W''_x})|_F` (Thesis (6.5.9):
`Δ = D^G (D^H)^{-2} = |det(1 − x)|_{W''_x}|`; the sign `(-1)^{dim W''}` is invisible). -/
def deltaGGP (d : GGPData F) (x : ↥(GSpin d.QW)) : ℝ :=
  absF (LinearMap.det (((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) -
      LinearMap.id).restrict (p := movedSub x) (q := movedSub x)
        (fun v _ => LinearMap.mem_range_self _ v)))

/-! ## 5. Regular nilpotent orbits and the choice `O_x` -/

section Orbits

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- The action `v ↦ [X, v]` on `V ⊂ C(V)` of an element `X ∈ gspin(V)` (the image of `X` in
`so(V)`). -/
def adV (Q : QuadraticForm F V) (X : CliffordAlgebra Q) : V →ₗ[F] V :=
  ιInv Q ∘ₗ (LinearMap.mulLeft F X - LinearMap.mulRight F X) ∘ₗ CliffordAlgebra.ι Q

/-- `N ∈ so(U)` lies in the regular nilpotent orbit `O_ν` of the even-dimensional quadratic space
`U ⊆ V` (after Waldspurger 2010 §7.1 / Luo §2.1): `U = D ⊕^⊥ U₁` with `D = F d₀` an
anisotropic line and `U₁ ≅ H^k ⊕ ⟨ν⟩` split odd-dimensional whose anisotropic line has form
`νx²`; `N` kills `D`, preserves `U₁`, and is regular nilpotent in `so(U₁)` (one Jordan block:
`N^{dim U₁ − 1} ≠ 0` on `U₁`). -/
def IsInOrbitNu (Q : QuadraticForm F V) (U : Submodule F V) (ν : F) (N : V →ₗ[F] V) : Prop :=
  ∃ (d₀ : V) (U₁ : Submodule F V),
    d₀ ∈ U ∧ Q d₀ ≠ 0 ∧ U₁ ≤ U ∧ (∀ u ∈ U₁, bform Q d₀ u = 0) ∧
    Submodule.span F {d₀} ⊔ U₁ = U ∧
    N d₀ = 0 ∧ (∀ u ∈ U₁, N u ∈ U₁) ∧
    (∃ u ∈ U₁, (N ^ (finrank F U₁ - 1)) u ≠ 0) ∧
    ∃ e ∈ U₁, Q e = ν ∧
      IsSplitQF (Q.comp (U₁ ⊓ (bform Q).orthogonal (Submodule.span F {e})).subtype)

end Orbits

/-- Luo's recipe (Luo §7.1) applied to the GGP triple `(G'_x, H'_x)` of the
admissible pair `(W'_x, V'_x = W'_x ⊕ Z)`, with `ν = q(z₀)`, as a condition on an element
`X = (X_W, X_V) ∈ 𝔤_x`:
* if `dim V'_x ≥ 4` is even: `X_V ∈ O_ν` on `V'_x` (`O_reg × O_ν`);
* else if `dim W'_x ≥ 4` is even: `X_W ∈ O_{−ν}` on `W'_x` (`O_{−ν} × O_reg`);
* otherwise no condition (the regular orbit is unique). -/
def OrbitSpec (d : GGPData F) (x : ↥(GSpin d.QW)) (X : d.ambient) : Prop :=
  if Even (finrank F ↥((fixedSub x).prod (⊤ : Submodule F d.Z))) ∧
      4 ≤ finrank F ↥((fixedSub x).prod (⊤ : Submodule F d.Z)) then
    IsInOrbitNu d.QV ((fixedSub x).prod ⊤) (d.ν : F) (adV d.QV X.2)
  else if Even (finrank F ↥(fixedSub x)) ∧ 4 ≤ finrank F ↥(fixedSub x) then
    IsInOrbitNu d.QW (fixedSub x) (-(d.ν : F)) (adV d.QW X.1)
  else True

/-- The orbit `O_x ∈ Nil_reg(𝔤_x)` (Luo §7.1): the regular nilpotent
orbit of `𝔤_x` selected by `OrbitSpec`.  This differs from the choice in Thesis §5.4: it is
Luo's recipe applied to `(G'_x, H'_x)`.  When no such orbit exists (e.g. `G_x` not quasi-split,
where `Nil_reg(𝔤_x) = ∅`), a junk value (the zero orbit); this is harmless since germs vanish off
`Nil_reg` (`germ_of_not_mem`). -/
def orbitChoice (d : GGPData F) (x : ↥(GSpin d.QW)) :
    NilOrbit (grpCentralizer d.G (d.diag x : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag x : d.ambientˣ)) : d.ambient)) :=
  if h : ∃ O ∈ NilReg (grpCentralizer d.G (d.diag x : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag x : d.ambientˣ)) : d.ambient)),
      ∃ X ∈ nilOrbitSet O, OrbitSpec d x (X : d.ambient) then h.choose
  else Quotient.mk (nilSetoid _ _) ⟨0, LieSubalgebra.zero_mem _, IsNilpotent.zero⟩

/-! ## 6. The geometric multiplicity (Thesis §7.2, Prop. 12.1.1) -/

/-- The probability Haar measure on a compact group (`0` if the group is not compact). -/
def probHaar (Q : Type*) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [MeasurableSpace Q] [BorelSpace Q] : Measure Q :=
  if _h : CompactSpace Q then
    Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  else 0

/-- The integrand `D^G(t)^{1/2} c_{θ,O_t}(t) Δ(t)^{s−1/2}` on `T(F)`, set to `0` off
`T_♮ = {t ∈ T | t ∈ Γ(G,H), T_t = T}` (= regular in `GSpin(W'')` without eigenvalue `1` on
`W''`). -/
def gammaIntegrand (ψ : NontrivialAddChar F) (d : GGPData F) (θ : ↥d.G → ℂ)
    (T : Subgroup ↥(GSpin d.QW)) (s : ℝ) (t : ↥(GSpin d.QW)) : ℂ :=
  if d.IsGammaElt t ∧ d.torusOf t = T then
    (Real.sqrt (weylDisc d.lie (d.diag t : d.ambientˣ)) : ℂ) *
      germ d.G d.lie d.bilin ψ θ (d.diag t) (orbitChoice d t) *
      ((deltaGGP d t ^ (s - 1 / 2) : ℝ) : ℂ)
  else 0

/-- `∫_{T(F)/A(F)} D^G(t)^{1/2} c_{θ,O_t}(t) Δ(t)^{s−1/2} dt` for the probability Haar measure
(this is `ν(T) dt` of Thesis §6.5).  The integrand is evaluated on a
representative of each coset; it is `A_{G,H}(F)`-invariant for `θ` with central character
trivial on `A_{G,H}(F)`. -/
def torusIntegral (ψ : NontrivialAddChar F) (d : GGPData F) (θ : ↥d.G → ℂ)
    (T : Subgroup ↥(GSpin d.QW)) (s : ℝ) : ℂ :=
  letI : MeasurableSpace (d.TorusQuot T) := borel _
  haveI : BorelSpace (d.TorusQuot T) := ⟨rfl⟩
  ∫ q, gammaIntegrand ψ d θ T s ((Quotient.out q : ↥T) : ↥(GSpin d.QW))
    ∂(probHaar (d.TorusQuot T))

/-- `m_{geom,s}(θ) = ∫_{Γ(G,H)} D^G(x)^{1/2} c_{θ,O_x}(x) Δ(x)^{s−1/2} dx
= Σ_{[T]} |W(T)|⁻¹ ∫_{T(F)/A(F)} …` (Thesis Prop. 12.1.1). -/
def mGeomS (ψ : NontrivialAddChar F) (d : GGPData F) (θ : ↥d.G → ℂ) (s : ℝ) : ℂ :=
  ∑' c : GammaClass d, ((weylCard d c : ℂ))⁻¹ * torusIntegral ψ d θ (Quot.out c).1 s

/-- `m_geom(θ) = lim_{s → 0⁺} m_{geom,s}(θ)` (Thesis §7.2 and Prop. 12.1.1). -/
def mGeom (ψ : NontrivialAddChar F) (d : GGPData F) (θ : ↥d.G → ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (mGeomS ψ d θ)

/-- **The multiplicity formula** (Thesis Thm. 7.2.2 (= Thm. 1.0.2)): for every GGP
triple and every irreducible tempered `π` with central character trivial on `A_{G,H}(F)`,
`m(π)` is finite and `m(π) = m_geom(θ_π)`.  A `Prop`-valued definition:
`Main` assumes it as `multiplicity_formula`, `TraceFormula` aims to derive it. -/
def MultiplicityFormula (F : Type*) [NontriviallyNormedField F] [PAdicField F]
    (ψ : NontrivialAddChar F) : Prop :=
  ∀ d : GGPData F, ∀ π : UnitaryRep ↥d.G, IsTempered π →
    IsTrivialOn π (d.AGH : Set ↥d.G) →
    mult ψ d π ≠ ⊤ ∧ ((mult ψ d π).toNat : ℂ) = mGeom ψ d (charG d π)

/-! ## 6a. Virtual tempered representations (Thesis §3.4, §7.2, §7.4)

The space `R_temp(G, η) ⊗ ℂ` of virtual tempered representations with central character `η` on
`A_G(F)`, as the free vector space on unitary-equivalence classes of irreducible tempered
representations with that central character, together with the linear extensions of
`π ↦ θ_π`, `π ↦ m(π)` and `π ↦ m_geom(θ_π)`.  `vMGeom` is the *linear extension*
of `m_geom` on irreducibles: it does not presuppose that `mGeom` is linear in `θ`
(Thesis Prop. 12.1.1, not proved here). -/

section Virtual

variable (d : GGPData F)

/-- `π` is irreducible tempered with central character `η` on `A_G(F)`: `π ∈ Temp(G, η)`
(Thesis §7.1 and §3.4, `Temp(G,χ)`). -/
def IsTempCC (η : CentralCharOn d) (π : UnitaryRep ↥d.G) : Prop :=
  IsTempered π ∧ HasCentralChar π d.AG (fun a => ((η.toHom a : Circle) : ℂ))

/-- The irreducible tempered representations with central character `η` (before passing to
equivalence classes). -/
abbrev TempRepCC (η : CentralCharOn d) : Type _ := {π : UnitaryRep ↥d.G // IsTempCC d η π}

/-- Unitary equivalence on `Temp(G, η)` (induced from `UnitaryRep.equivSetoid`). -/
instance TempRepCC.setoid (η : CentralCharOn d) : Setoid (TempRepCC d η) :=
  Setoid.comap Subtype.val UnitaryRep.equivSetoid

/-- The set `Temp(G, η)` of unitary-equivalence classes of irreducible tempered representations of
`G(F)` with central character `η` on `A_G(F)` (Thesis §3.4, §7.1).  It lives one universe
up, because `UnitaryRep` bundles its Hilbert space. -/
def TempClass (η : CentralCharOn d) : Type _ := Quotient (TempRepCC.setoid d η)

/-- `R_temp(G, η) ⊗ ℂ`: finite formal `ℂ`-linear combinations of classes in `Temp(G, η)`
(Thesis §3.4: "the complex vector space with basis `Temp(G)`"; `R_temp(G,χ)` in §7.4).
Equivalently the complexified Grothendieck group of
tempered representations of finite length with central character `η`, by Harish-Chandra's
linear independence of characters (not needed here). -/
abbrev VirtualTemp (η : CentralCharOn d) : Type _ := TempClass d η →₀ ℂ

variable {d}

/-- The class `[π] ∈ Temp(G, η)` of `π`. -/
def TempClass.mk {η : CentralCharOn d} (π : UnitaryRep ↥d.G) (hπ : IsTempCC d η π) :
    TempClass d η :=
  Quotient.mk (TempRepCC.setoid d η) ⟨π, hπ⟩

/-- A chosen representative of a class in `Temp(G, η)`.  All invariants used below
(`mult`, `charG`) do not depend on the choice (`mult_rep_mk`, `charG_rep_mk`). -/
def TempClass.rep {η : CentralCharOn d} (c : TempClass d η) : UnitaryRep ↥d.G :=
  (Quotient.out c).1

theorem TempClass.isTempCC_rep {η : CentralCharOn d} (c : TempClass d η) :
    IsTempCC d η c.rep :=
  (Quotient.out c).2

/-- The representative of a class is irreducible tempered. -/
theorem TempClass.isTempered_rep {η : CentralCharOn d} (c : TempClass d η) :
    IsTempered c.rep :=
  c.isTempCC_rep.1

/-- The representative of a class has central character `η` on `A_G(F)`. -/
theorem TempClass.hasCentralChar_rep {η : CentralCharOn d} (c : TempClass d η) :
    HasCentralChar c.rep d.AG (fun a => ((η.toHom a : Circle) : ℂ)) :=
  c.isTempCC_rep.2

/-- The representative of `[π]` is unitarily equivalent to `π`. -/
theorem TempClass.rep_equiv {η : CentralCharOn d} (π : UnitaryRep ↥d.G)
    (hπ : IsTempCC d η π) :
    (TempClass.mk π hπ).rep.IsEquivalent π :=
  Quotient.mk_out (s := TempRepCC.setoid d η) ⟨π, hπ⟩

/-- Every class is the class of its representative. -/
theorem TempClass.mk_rep {η : CentralCharOn d} (c : TempClass d η) :
    TempClass.mk c.rep c.isTempCC_rep = c :=
  Quotient.out_eq c

/-- Two representations have the same class iff they are unitarily equivalent. -/
theorem TempClass.mk_eq_mk_iff {η : CentralCharOn d} {π π' : UnitaryRep ↥d.G}
    (hπ : IsTempCC d η π) (hπ' : IsTempCC d η π') :
    TempClass.mk π hπ = TempClass.mk π' hπ' ↔ π.IsEquivalent π' :=
  Quotient.eq (r := TempRepCC.setoid d η)

/-- `m(π)` depends only on the class of `π`. -/
theorem TempClass.mult_rep_mk (ψ : NontrivialAddChar F) {η : CentralCharOn d}
    (π : UnitaryRep ↥d.G) (hπ : IsTempCC d η π) :
    mult ψ d (TempClass.mk π hπ).rep = mult ψ d π :=
  multiplicity_congr (TempClass.rep_equiv π hπ) _ _

/-- `θ_π` depends only on the class of `π`. -/
theorem TempClass.charG_rep_mk {η : CentralCharOn d} (π : UnitaryRep ↥d.G)
    (hπ : IsTempCC d η π) :
    charG d (TempClass.mk π hπ).rep = charG d π :=
  characterOn_congr (TempClass.rep_equiv π hπ) _


/-- The character `θ_Π = Σ_c a_c θ_{π_c}` of a virtual tempered representation
`Π = Σ_c a_c [π_c]` (Thesis §3.4, extension to virtual representations). -/
def vChar (d : GGPData F) {η : CentralCharOn d} : VirtualTemp d η →ₗ[ℂ] (↥d.G → ℂ) :=
  Finsupp.linearCombination ℂ (fun c : TempClass d η => charG d c.rep)

/-- The multiplicity `m(Π) = Σ_c a_c m(π_c)`, linearly extended (Thesis §7.2, §7.4).
Infinite multiplicities are read as `0` (`ℕ∞.toNat`); they do not occur
(`emoryTakeda_mult_le_one`). -/
def vMult (ψ : NontrivialAddChar F) (d : GGPData F) {η : CentralCharOn d} :
    VirtualTemp d η →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun c : TempClass d η => ((mult ψ d c.rep).toNat : ℂ))

/-- `m_geom(Π) := Σ_c a_c m_geom(θ_{π_c})`, the linear extension of `π ↦ m_geom(θ_π)` from
irreducibles (Thesis §7.2, "`m_geom(π) = m_geom(θ_π)` for all `π ∈ R_temp(G,χ)`").
It agrees with `m_geom(θ_Π)` once `m_geom` is
known to be linear (Thesis Prop. 12.1.1), which is not used here. -/
def vMGeom (ψ : NontrivialAddChar F) (d : GGPData F) {η : CentralCharOn d} :
    VirtualTemp d η →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun c : TempClass d η => mGeom ψ d (charG d c.rep))

/-- The defect `m(Π) − m_geom(Π)` of the multiplicity formula on virtual tempered
representations (Thesis Prop. 7.4.1(ii) and §7.4): the multiplicity formula for
`π` is `defect [π] = 0`. -/
def defect (ψ : NontrivialAddChar F) (d : GGPData F) {η : CentralCharOn d} :
    VirtualTemp d η →ₗ[ℂ] ℂ :=
  vMult ψ d - vMGeom ψ d


@[simp] theorem vChar_single {η : CentralCharOn d} (c : TempClass d η) (a : ℂ) :
    vChar d (Finsupp.single c a) = a • charG d c.rep := by
  simp [vChar]

@[simp] theorem vMult_single (ψ : NontrivialAddChar F) {η : CentralCharOn d}
    (c : TempClass d η) (a : ℂ) :
    vMult ψ d (Finsupp.single c a) = a * ((mult ψ d c.rep).toNat : ℂ) := by
  simp [vMult]

@[simp] theorem vMGeom_single (ψ : NontrivialAddChar F) {η : CentralCharOn d}
    (c : TempClass d η) (a : ℂ) :
    vMGeom ψ d (Finsupp.single c a) = a * mGeom ψ d (charG d c.rep) := by
  simp [vMGeom]

/-- The defect of `a [π_c]` is `a (m(π_c) − m_geom(θ_{π_c}))`. -/
theorem defect_single (ψ : NontrivialAddChar F) {η : CentralCharOn d} (c : TempClass d η)
    (a : ℂ) :
    defect ψ d (Finsupp.single c a) =
      a * (((mult ψ d c.rep).toNat : ℂ) - mGeom ψ d (charG d c.rep)) := by
  simp [defect, mul_sub]

/-- `defect [c] = 0` iff the multiplicity formula `m(π_c) = m_geom(θ_{π_c})` holds for the
representative (read with `toNat`). -/
theorem defect_single_one_eq_zero_iff (ψ : NontrivialAddChar F) {η : CentralCharOn d}
    (c : TempClass d η) :
    defect ψ d (Finsupp.single c 1) = 0 ↔
      ((mult ψ d c.rep).toNat : ℂ) = mGeom ψ d (charG d c.rep) := by
  rw [defect_single, one_mul, sub_eq_zero]

end Virtual

/-- The multiplicity formula at one GGP datum `d` (the body of `MultiplicityFormula`;
Thesis Thm. 7.2.2 (= Thm. 1.0.2)). -/
def MultAt (ψ : NontrivialAddChar F) (d : GGPData F) : Prop :=
  ∀ π : UnitaryRep ↥d.G, IsTempered π → IsTrivialOn π (d.AGH : Set ↥d.G) →
    mult ψ d π ≠ ⊤ ∧ ((mult ψ d π).toNat : ℂ) = mGeom ψ d (charG d π)

/-- `MultiplicityFormula` is `MultAt` at every datum (definitionally). -/
theorem multiplicityFormula_iff (ψ : NontrivialAddChar F) :
    MultiplicityFormula F ψ ↔ ∀ d : GGPData F, MultAt ψ d := Iff.rfl

/-! ## 7. Own lemmas (no citations) -/

namespace GGPData

variable (d : GGPData F)

/-- The first component of `diag x = (x, x)` is `x`. -/
theorem fst_diag (x : ↥(GSpin d.QW)) : d.fst (d.diag x) = x := rfl

/-- The second component of `diag x = (x, x)` is `x` embedded in `GSpin(V)`. -/
theorem snd_diag (x : ↥(GSpin d.QW)) : d.snd (d.diag x) = d.incl x := rfl

/-- The unipotent part of a diagonal element is trivial. -/
theorem nPart_diag (x : ↥(GSpin d.QW)) : d.nPart (d.diag x) = 1 := by
  rw [nPart, fst_diag, snd_diag, inv_mul_cancel]

/-- On `Z ⊆ V`, the form of `V = W ⊕ Z` restricts to the form of `Z`. -/
theorem bform_zV (k l : ℤ) :
    bform d.QV (d.zV k) (d.zV l) = bform d.QZ (zvec d.r k) (zvec d.r l) := by
  simp [zV, bform, QuadraticMap.associated_prod]

/-- `A_{G,H} ⊆ H`: `n(c, c) = c⁻¹ c = 1 ∈ N`. -/
theorem AGH_le_H : d.AGH ≤ d.H := by
  rintro _ ⟨c, rfl⟩
  show d.nPart _ ∈ d.N
  rw [MonoidHom.comp_apply, d.nPart_diag]
  exact d.N.one_mem

/-- `ξ` is trivial on `A_{G,H}(F)`: for `h = (c, c)` the unipotent part is `1`, and
`λ(1) = Σ b(z_{−i−1}, z_i) = 0`. -/
theorem xi_eq_one_of_mem_AGH (ψ : AddChar F Circle) (h : ↥d.H) (hh : (h : ↥d.G) ∈ d.AGH) :
    d.xi ψ h = 1 := by
  obtain ⟨c, hc⟩ := hh
  have hn : d.nPart (h : ↥d.G) = 1 := by
    rw [← hc]
    exact d.nPart_diag _
  have hlam : d.lam h = 0 := by
    unfold lam
    rw [hn, map_one]
    refine Finset.sum_eq_zero fun i _ => ?_
    show bform d.QV (d.zV (-(i : ℤ) - 1)) (d.zV (i : ℕ)) = 0
    have hi := i.2
    rw [bform_zV]
    · rw [bform_splitOddForm_zvec]
      · exact ite_eq_right_iff.mpr fun h => absurd h (by omega)
      · rw [abs_le]; constructor <;> omega
      · rw [abs_le]; constructor <;> omega
  unfold xi
  rw [hlam, AddChar.map_zero_eq_one]
  rfl

end GGPData

omit [NontriviallyNormedField F] [PAdicField F] in
/-- Generic form of the vanishing argument for `m(π)`: if some `a ∈ S` with `ξ(a) = 1` acts by
a scalar `c` and not trivially, there is no nonzero `(S, ξ)`-equivariant form. -/
theorem equivariantForms_eq_bot_of_scalar {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (π : UnitaryRep G) (S : Subgroup G) (ξ : ↥S → ℂ) (a : G)
    (haS : a ∈ S) (c : ℂ) (hρ : π.ρ a ≠ 1) (hρa : ∀ v : π.H, π.ρ a v = c • v)
    (hξ : ξ ⟨a, haS⟩ = 1) : equivariantForms π S ξ = ⊥ := by
  have hc : c ≠ 1 := by
    rintro rfl
    apply hρ
    ext v
    rw [hρa, one_smul]
    rfl
  rw [Submodule.eq_bot_iff]
  intro ℓ hℓ
  ext v
  have h1 := hℓ ⟨a, haS⟩ v
  rw [hξ, one_mul] at h1
  have h2 : smoothAction π a v = c • v := by
    apply Subtype.ext
    rw [smoothAction_apply, hρa]
    rfl
  rw [h2, map_smul, smul_eq_mul] at h1
  have h3 : (c - 1) * ℓ v = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd (sub_eq_zero.mp h4) hc
  · simpa using h4

/-- Since `ξ` is trivial on `Z_{G,H}(F)`, `m(π) = 0` unless the central character of
`π` is trivial on `Z_{G,H}(F) = A_{G,H}(F)`.  (Stated for `π` with a central character on
`A_{G,H}`; for irreducible `π` this is Schur's lemma.) -/
theorem mult_eq_zero_of_not_isTrivialOn (ψ : NontrivialAddChar F) (d : GGPData F)
    (π : UnitaryRep ↥d.G) (χ : ↥d.AGH → ℂ) (hχ : HasCentralChar π d.AGH χ)
    (h : ¬ IsTrivialOn π (d.AGH : Set ↥d.G)) : mult ψ d π = 0 := by
  simp only [IsTrivialOn, not_forall] at h
  obtain ⟨a, ha0, hρ⟩ := h
  have ha : a ∈ d.AGH := SetLike.mem_coe.mp ha0
  have hv : ∀ v : π.H, π.ρ a v = χ ⟨a, ha⟩ • v := fun v => by
    have := congrArg (fun T : π.H →L[ℂ] π.H => T v) (hχ ⟨a, ha⟩)
    exact this
  have hbot := equivariantForms_eq_bot_of_scalar π d.H (d.xi ψ.toAddChar) a (d.AGH_le_H ha)
    (χ ⟨a, ha⟩) hρ hv (d.xi_eq_one_of_mem_AGH ψ.toAddChar ⟨a, d.AGH_le_H ha⟩ ha)
  by_contra hne
  exact ((hasModel_iff_multiplicity_ne_zero π d.H (d.xi ψ.toAddChar)).mpr hne) hbot

section DeltaAux

variable {V : Type*} [AddCommGroup V] [Module F V]

omit [NontriviallyNormedField F] [PAdicField F] in
/-- `det(f|_{Im f})` for an endomorphism `f`; `Δ(x)` is `|detIm (P(x) − 1)|_F`. -/
def detIm {K : Type*} [Field K] [Module K V] (f : V →ₗ[K] V) : K :=
  LinearMap.det (f.restrict (p := LinearMap.range f) (q := LinearMap.range f)
    (fun v _ => LinearMap.mem_range_self _ v))

omit [NontriviallyNormedField F] [PAdicField F] in
theorem detIm_zero {K : Type*} [Field K] [Module K V] : detIm (0 : V →ₗ[K] V) = 1 := by
  have : Subsingleton ↥(LinearMap.range (0 : V →ₗ[K] V)) := by
    rw [LinearMap.range_zero]; infer_instance
  exact LinearMap.det_eq_one_of_subsingleton _

omit [NontriviallyNormedField F] [PAdicField F] in
/-- `detIm` is invariant under conjugation by a linear automorphism. -/
theorem detIm_conj {K : Type*} [Field K] [Module K V] (f : V →ₗ[K] V) (e : V ≃ₗ[K] V) :
    detIm ((e : V →ₗ[K] V) ∘ₗ f ∘ₗ (e.symm : V →ₗ[K] V)) = detIm f := by
  have hr : (LinearMap.range f).map (e : V →ₗ[K] V) =
      LinearMap.range ((e : V →ₗ[K] V) ∘ₗ f ∘ₗ (e.symm : V →ₗ[K] V)) := by
    ext u
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply]
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨e w, by simp⟩
    · rintro ⟨w, rfl⟩
      exact ⟨_, ⟨e.symm w, rfl⟩, rfl⟩
  let φ := e.ofSubmodules _ _ hr
  unfold detIm
  rw [← LinearMap.det_conj _ φ]
  congr 1

omit [NontriviallyNormedField F] [PAdicField F] in
/-- If `ker f ∩ Im f = 0` (e.g. `f` semisimple) then `det(f|_{Im f}) ≠ 0`. -/
theorem detIm_ne_zero {K : Type*} [Field K] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V) (hf : Disjoint (LinearMap.ker f) (LinearMap.range f)) : detIm f ≠ 0 := by
  unfold detIm
  set g := f.restrict (p := LinearMap.range f) (q := LinearMap.range f)
    (fun v _ => LinearMap.mem_range_self _ v)
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    have h1 : (u : V) ∈ LinearMap.ker f := by
      have := congrArg Subtype.val (LinearMap.mem_ker.mp hu)
      simpa [g] using this
    exact Subtype.ext (Submodule.disjoint_def.mp hf _ h1 u.2)
  exact (LinearEquiv.ofInjectiveEndo g hinj).isUnit_det'.ne_zero

omit [NontriviallyNormedField F] [PAdicField F] in
/-- A semisimple endomorphism has `ker f ∩ Im f = 0`. -/
theorem disjoint_ker_range_of_isSemisimple {K : Type*} [Field K] [Module K V]
    {f : Module.End K V} (hf : f.IsSemisimple) : Disjoint (LinearMap.ker f) (LinearMap.range f) := by
  obtain ⟨q, hq, hc⟩ := Module.End.isSemisimple_iff.mp hf (LinearMap.ker f)
    ((Module.End.mem_invtSubmodule f).mpr fun v hv => by
      simp only [Submodule.mem_comap, LinearMap.mem_ker] at hv ⊢; simp [hv])
  have hrange : LinearMap.range f ≤ q := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨k, hk, c, hc', rfl⟩ := Submodule.mem_sup.mp (hc.codisjoint.eq_top ▸ Submodule.mem_top :
      v ∈ LinearMap.ker f ⊔ q)
    rw [map_add, LinearMap.mem_ker.mp hk, zero_add]
    exact (Module.End.mem_invtSubmodule f).mp hq hc'
  exact hc.disjoint.mono_right hrange

end DeltaAux

theorem deltaGGP_eq (d : GGPData F) (x : ↥(GSpin d.QW)) :
    deltaGGP d x = absF (detIm ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) -
      LinearMap.id)) := rfl

/-- `P(c) = 1` for central scalars `c`. -/
theorem specP_scalarGSpin (d : GGPData F) (c : Fˣ) : specP d.QW (scalarGSpin d.QW c) = 1 := by
  refine LinearEquiv.ext fun w => ?_
  apply ι_injective d.QW
  rw [ι_specP]
  simp only [scalarGSpin, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_map,
    Units.coe_map_inv, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  rw [← Algebra.commutes, ← mul_assoc, ← map_mul]
  simp

/-- `Δ ≥ 0`. -/
theorem deltaGGP_nonneg (d : GGPData F) (x : ↥(GSpin d.QW)) : 0 ≤ deltaGGP d x :=
  absF_nonneg _

/-- `Δ(1) = 1` (`W''_1 = 0`; the class of `1` is the atom of `Γ(G,H)`). -/
theorem deltaGGP_one (d : GGPData F) : deltaGGP d 1 = 1 := by
  rw [deltaGGP_eq, map_one]
  show absF (detIm (LinearMap.id - LinearMap.id)) = 1
  rw [sub_self, detIm_zero, absF_of_ne_zero one_ne_zero]
  simp

/-- `Δ(cx) = Δ(x)` for central scalars `c ∈ A_{G,H}(F)` (since `P(cx) = P(x)`). -/
theorem deltaGGP_scalar_mul (d : GGPData F) (c : Fˣ) (x : ↥(GSpin d.QW)) :
    deltaGGP d (scalarGSpin d.QW c * x) = deltaGGP d x := by
  rw [deltaGGP_eq, deltaGGP_eq, map_mul, specP_scalarGSpin, one_mul]

/-- `Δ` is invariant under `GSpin(W)(F)`-conjugation. -/
theorem deltaGGP_conj (d : GGPData F) (g x : ↥(GSpin d.QW)) :
    deltaGGP d (g * x * g⁻¹) = deltaGGP d x := by
  rw [deltaGGP_eq, deltaGGP_eq]
  conv_rhs => rw [← detIm_conj _ (specP d.QW g)]
  congr 2
  ext v
  simp [map_mul, map_inv]

/-- `Δ(x) > 0` for semisimple `x` (`P(x) − 1` is invertible on `W''_x`, as
`W = W'_x ⊕ W''_x`). -/
theorem deltaGGP_pos (d : GGPData F) (x : ↥(GSpin d.QW))
    (hx : IsSS F (((x : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW)) : 0 < deltaGGP d x := by
  rw [deltaGGP_eq]
  apply absF_pos
  apply detIm_ne_zero
  set a : CliffordAlgebra d.QW := ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) with ha
  set b : CliffordAlgebra d.QW :=
    (((x : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) with hb
  have hba : b * a = 1 := Units.inv_mul _
  have hab : a * b = 1 := Units.mul_inv _
  -- `R_a` is semisimple: `a` and `R_a` are killed by the same polynomials as `L_a`.
  have hL : ∀ p : Polynomial F, ∀ y, (Polynomial.aeval (LinearMap.mulLeft F a) p) y =
      Polynomial.aeval a p * y := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => intro y; simp [hp, hq, add_mul]
    | monomial n k =>
      intro y
      simp [Polynomial.aeval_monomial, LinearMap.pow_mulLeft, Algebra.smul_def, mul_assoc]
  have hR : ∀ p : Polynomial F, ∀ y, (Polynomial.aeval (LinearMap.mulRight F a) p) y =
      y * Polynomial.aeval a p := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => intro y; simp [hp, hq, mul_add]
    | monomial n k =>
      intro y
      simp [Polynomial.aeval_monomial, LinearMap.pow_mulRight, Algebra.smul_def,
        Algebra.commutes, mul_assoc]
  have hss : Module.End.IsSemisimple (LinearMap.mulLeft F a) := hx
  have hRs : Module.End.IsSemisimple (LinearMap.mulRight F a) := by
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hss.minpoly_squarefree ?_
    have h1 : Polynomial.aeval a (minpoly F (LinearMap.mulLeft F a)) = 0 := by
      have := hL (minpoly F (LinearMap.mulLeft F a)) 1
      rw [minpoly.aeval, mul_one] at this
      exact this.symm
    ext y
    rw [hR, h1, mul_zero]
    rfl
  have hD : Module.End.IsSemisimple (LinearMap.mulLeft F a - LinearMap.mulRight F a) :=
    Module.End.IsSemisimple.sub_of_commute (LinearMap.commute_mulLeft_right a a) hss hRs
  have hdisj := Submodule.disjoint_def.mp (disjoint_ker_range_of_isSemisimple hD)
  rw [Submodule.disjoint_def]
  intro v hv1 hv2
  obtain ⟨w, hw⟩ := hv2
  have hPv : specP d.QW x v = v := by
    have := LinearMap.mem_ker.mp hv1
    simpa [sub_eq_zero] using this
  have hPw : specP d.QW x w - w = v := by simpa using hw
  have hιPv := ι_specP x v
  rw [hPv] at hιPv
  have hιPw := ι_specP x w
  apply ι_injective d.QW
  rw [map_zero]
  apply hdisj
  · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      sub_eq_zero]
    calc a * CliffordAlgebra.ι d.QW v = a * CliffordAlgebra.ι d.QW v * (b * a) := by rw [hba, mul_one]
      _ = (a * CliffordAlgebra.ι d.QW v * b) * a := by simp only [mul_assoc]
      _ = CliffordAlgebra.ι d.QW v * a := by rw [← hιPv]
  · refine ⟨CliffordAlgebra.ι d.QW w * b, ?_⟩
    rw [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, mul_assoc _ b a,
      hba, mul_one, ← mul_assoc, ← hιPw, ← map_sub, hPw]

/-- `T_x` contains the central scalars `A_{G,H}(F)`. -/
theorem GGPData.scalar_mem_torusOf (d : GGPData F) (x : ↥(GSpin d.QW)) (c : Fˣ) :
    scalarGSpin d.QW c ∈ d.torusOf x := by
  refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, ?_⟩
  · rintro y rfl
    exact (scalarGSpin_commute d.QW c y).eq.symm
  · intro w _
    apply ι_injective d.QW
    rw [ι_specP]
    simp only [scalarGSpin, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_map,
      Units.coe_map_inv, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    rw [← Algebra.commutes, ← mul_assoc, ← map_mul]
    simp

end GSpinGGP
