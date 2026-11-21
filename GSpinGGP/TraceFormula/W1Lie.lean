/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.SOLie

/-!
# Waldspurger 2010, §7: the Lie-algebra integral formula for `(SO(V), SO(W))`

The objects of Waldspurger, *Une formule intégrale reliée à la conjecture locale de
Gross–Prasad*, Compositio Math. 146 (2010), arXiv:0902.1875v1 ("W1"), §7.1–§7.3 and §7.9, for the
single group `G = SO(V)` and its subgroup `H = SO(W)`, with the data of a `LuoDatum`
(`V = W ⊕ D ⊕ Z`, `D = F z₀`, `(z_i)_{i = ±1, …, ±r}` a hyperbolic system of `Z`).  W1's bilinear
form `q(·,·)` is `bform`; W1's quadratic form `q(v) = ½ q(v, v)` is `½ Q(v)` (`bform Q v v = Q v`).
These are used by the literature axiom `waldspurger2010_thm_7_9`
(`Literature/WaldspurgerLie.lean`).

* `EndW`, `EndV`: `End W`, `End V` with the module topology; `soW = 𝔥`, `soV = 𝔤` (W1 §7.1);
  `bW`, `bV`: W1's form `⟨X, Y⟩ = ½ trace(XY)` (§7.1; on `𝔥` its restriction, §1.2).
* `SOW = H`, `SOV = G`, `HV` (`H ⊆ G`, acting trivially on `D ⊕ Z`), `UV = U` (the unipotent
  radical of the parabolic `P` stabilizing `F z_r ⊂ ⋯ ⊂ F z_r ⊕ ⋯ ⊕ F z_1`, §7.2), `UHV = UH`.
* `xiU`: W1's `ξ(N) = ψ(Σ_{i=0}^{r-1} ξ_i q(N v_i, v_{-i-1}))` on `𝔲(F)` (§7.2, §7.9).
* `IsSpecialLattice` (§7.1), `kappa` (`κ_N`, §7.2).
* `fXi`, `Ig` (`I(θ, f, g)`), `IN` (`I_N(θ, f)`) (§7.9).
* `W1Torus` (`𝒯`, §7.3), `weylW1` (`|W(H, T)|`), `IsNatW` (`𝔱_♮`), `deltaW` (`Δ`, §7.9), `cThetaW`,
  `cFW` (`c_θ`, `c_f`, §7.3 recipe at `Y ∈ 𝔱_♮(F)`, §7.9), `Igeom` (`I(θ, f)`, §7.9).
* `W1Input`: the remaining data of §7.2 (`ξ_i`, the special lattices and `K`) and the measures of
  §1.2 and §7.2, as hypotheses.
-/

noncomputable section

open MeasureTheory Topology Filter Module

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

namespace LuoDatum

/-! ## The ambient algebras `End W`, `End V` -/

section Ambient

variable {K : Type*} [Field K] [Invertible (2 : K)] (L : LuoDatum K)

/-- `End W` (a type synonym carrying the module topology and the commutator Lie bracket). -/
def EndW : Type _ := Module.End K L.W

/-- `End V` (a type synonym carrying the module topology and the commutator Lie bracket). -/
def EndV : Type _ := Module.End K L.V

instance : Ring L.EndW := inferInstanceAs (Ring (Module.End K L.W))
instance : Algebra K L.EndW := inferInstanceAs (Algebra K (Module.End K L.W))
instance : Module.Finite K L.EndW := inferInstanceAs (Module.Finite K (Module.End K L.W))
instance : Ring L.EndV := inferInstanceAs (Ring (Module.End K L.V))
instance : Algebra K L.EndV := inferInstanceAs (Algebra K (Module.End K L.V))
instance : Module.Finite K L.EndV := inferInstanceAs (Module.Finite K (Module.End K L.V))

/-- An element of `End W` as an endomorphism. -/
def asW (X : L.EndW) : Module.End K L.W := X

/-- An element of `End V` as an endomorphism. -/
def asV (X : L.EndV) : Module.End K L.V := X

/-- An endomorphism of `V` as an element of `End V`. -/
def ofV (X : Module.End K L.V) : L.EndV := X

/-- `𝔥 = so(W)` (W1 §7.1). -/
def soW : LieSubalgebra K L.EndW where
  carrier := {X | X ∈ skewAdjointLieSubalgebra (bform L.QW)}
  add_mem' := fun hX hY => (skewAdjointLieSubalgebra (bform L.QW)).add_mem hX hY
  zero_mem' := (skewAdjointLieSubalgebra (bform L.QW)).zero_mem
  smul_mem' := fun c _ hX => (skewAdjointLieSubalgebra (bform L.QW)).smul_mem c hX
  lie_mem' := fun hX hY => (skewAdjointLieSubalgebra (bform L.QW)).lie_mem hX hY

/-- `𝔤 = so(V)` (W1 §7.1). -/
def soV : LieSubalgebra K L.EndV where
  carrier := {X | X ∈ skewAdjointLieSubalgebra (bform L.QV)}
  add_mem' := fun hX hY => (skewAdjointLieSubalgebra (bform L.QV)).add_mem hX hY
  zero_mem' := (skewAdjointLieSubalgebra (bform L.QV)).zero_mem
  smul_mem' := fun c _ hX => (skewAdjointLieSubalgebra (bform L.QV)).smul_mem c hX
  lie_mem' := fun hX hY => (skewAdjointLieSubalgebra (bform L.QV)).lie_mem hX hY

/-- W1's form `⟨X, Y⟩ = ½ trace(XY)` on `End W` (W1 §7.1; on `𝔥 ⊆ 𝔤` it is the restriction of
the form of `𝔤`, since `trace_V((X ⊕ 0)(Y ⊕ 0)) = trace_W(XY)`). -/
def bW : LinearMap.BilinForm K L.EndW :=
  (⅟(2 : K) • (LinearMap.mul K (Module.End K L.W)).compr₂ (LinearMap.trace K L.W) :
    LinearMap.BilinForm K (Module.End K L.W))

/-- W1's form `⟨X, Y⟩ = ½ trace(XY)` on `End V` (W1 §7.1). -/
def bV : LinearMap.BilinForm K L.EndV :=
  (⅟(2 : K) • (LinearMap.mul K (Module.End K L.V)).compr₂ (LinearMap.trace K L.V) :
    LinearMap.BilinForm K (Module.End K L.V))

/-- `H = SO(W)` (W1 §7.2). -/
def SOW : Subgroup L.EndWˣ := SOu L.QW

/-- `G = SO(V)` (W1 §7.1). -/
def SOV : Subgroup L.EndVˣ := SOu L.QV

/-- `GL(W) → GL(V)`, `g ↦ g ⊕ 1` (W1 §7.1: an element of `SO(W)` acts by the identity on the
orthogonal `D ⊕ Z` of `W`). -/
def extU : L.EndWˣ →* L.EndVˣ := Units.map L.extGrp

/-- `H = SO(W)` as a subgroup of `GL(V)`. -/
def HV : Subgroup L.EndVˣ := L.SOW.map L.extU

/-- `U`, the unipotent radical of the parabolic subgroup `P` of `G` stabilizing the flag
`F z_r ⊂ F z_r ⊕ F z_{r-1} ⊂ ⋯ ⊂ F z_r ⊕ ⋯ ⊕ F z_1` (W1 §7.2).  `Nset` is this group; the closure
is taken only to have a `Subgroup`. -/
def UV : Subgroup L.EndVˣ := Subgroup.closure L.Nset

/-- `U H` (W1 §7.2: `H` normalizes `U`). -/
def UHV : Subgroup L.EndVˣ := Subgroup.closure ((L.HV : Set L.EndVˣ) ∪ L.Nset)

/-- `U` as a subgroup of `G(F)`. -/
def Ubar : Subgroup ↥L.SOV := L.UV.subgroupOf L.SOV

/-- `H` as a subgroup of `G(F)`. -/
def Hbar' : Subgroup ↥L.SOV := L.HV.subgroupOf L.SOV

/-- `U H` as a subgroup of `G(F)`. -/
def UHbar : Subgroup ↥L.SOV := L.UHV.subgroupOf L.SOV

theorem Ubar_le_UHbar : L.Ubar ≤ L.UHbar := fun _ hx =>
  Subgroup.closure_mono Set.subset_union_right hx

theorem Hbar'_le_UHbar : L.Hbar' ≤ L.UHbar := fun _ hx =>
  Subgroup.subset_closure (Or.inl hx)

/-- `V₀ = W ⊕ D` (W1 §7.2). -/
def V0sub : Submodule K L.V := (⊤ : Submodule K L.W).prod (Submodule.span K {L.z 0})

/-- `Z` (W1 §7.2), the span of the `z_i`, `1 ≤ |i| ≤ r`. -/
def Zsub : Submodule K L.V :=
  (⊥ : Submodule K L.W).prod (Submodule.span K (L.z '' {i : ℤ | 1 ≤ |i| ∧ |i| ≤ L.r}))

/-- W1's character `ξ` of `𝔲(F)` (§7.2, §7.9): `ξ(N) = ψ(Σ_{i=0}^{r-1} ξ_i q(N v_i, v_{-i-1}))`,
with `v_i = z_i` (so `v₀ = z₀` spans `D`). -/
def xiArg (ξc : Fin L.r → K) (N : Module.End K L.V) : K :=
  ∑ i : Fin L.r, ξc i * bform L.QV (N (L.zV (i : ℕ))) (L.zV (-(i : ℤ) - 1))

end Ambient

/-! ## Topology, measurable structures, and the anisotropic kernel -/

section Topology

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (L : LuoDatum F)

instance instTopologicalSpaceEndW : TopologicalSpace L.EndW := moduleTopology F L.EndW
instance instIsModuleTopologyEndW : IsModuleTopology F L.EndW := ⟨rfl⟩
instance instIsTopologicalRingEndW : IsTopologicalRing L.EndW :=
  isTopologicalRing_of_moduleTopology F L.EndW
instance instTopologicalSpaceEndV : TopologicalSpace L.EndV := moduleTopology F L.EndV
instance instIsModuleTopologyEndV : IsModuleTopology F L.EndV := ⟨rfl⟩
instance instIsTopologicalRingEndV : IsTopologicalRing L.EndV :=
  isTopologicalRing_of_moduleTopology F L.EndV

instance instMeasurableSpaceSOV : MeasurableSpace ↥L.SOV := borel _
instance instBorelSpaceSOV : BorelSpace ↥L.SOV := ⟨rfl⟩
instance instMeasurableSpaceUbar : MeasurableSpace ↥L.Ubar := borel _
instance instBorelSpaceUbar : BorelSpace ↥L.Ubar := ⟨rfl⟩
instance instMeasurableSpaceHbar' : MeasurableSpace ↥L.Hbar' := borel _
instance instBorelSpaceHbar' : BorelSpace ↥L.Hbar' := ⟨rfl⟩
instance instMeasurableSpaceUHbar : MeasurableSpace ↥L.UHbar := borel _
instance instBorelSpaceUHbar : BorelSpace ↥L.UHbar := ⟨rfl⟩
instance instMeasurableSpaceSoW : MeasurableSpace ↥L.soW := borel _
instance instBorelSpaceSoW : BorelSpace ↥L.soW := ⟨rfl⟩
instance instMeasurableSpaceSoV : MeasurableSpace ↥L.soV := borel _
instance instBorelSpaceSoV : BorelSpace ↥L.soV := ⟨rfl⟩

/-- `𝔲 = Lie(U)` (`lieN`), with the module topology. -/
def lieU : Submodule F L.EndV := L.lieN

instance instMeasurableSpaceLieU : MeasurableSpace ↥L.lieU := borel _
instance instBorelSpaceLieU : BorelSpace ↥L.lieU := ⟨rfl⟩

/-- The dimension `d_an` of the anisotropic kernel of `(U, Q|_U)` (W1 §7.1):
`dim U − 2 · (Witt index)`. -/
def anisoDim (U : Submodule F L.V) : ℕ :=
  finrank F U - 2 * wittIndex (L.QV.comp U.subtype)

/-- `d_an` for a subspace of `W`. -/
def anisoDimW (U : Submodule F L.W) : ℕ :=
  finrank F U - 2 * wittIndex (L.QW.comp U.subtype)

end Topology

/-! ## Special lattices and `κ_N` (W1 §7.1, §7.2) -/

section Kappa

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- `ϖ` is a uniformizer: `|ϖ|_F` is the largest absolute value `< 1`.  With it, `val_F(x) ≥ c`
is `|x|_F ≤ |ϖ|_F^c` and `val_F(x) = c` is `|x|_F = |ϖ|_F^c`. -/
def IsUniformizer (ϖ : F) : Prop :=
  0 < absF ϖ ∧ absF ϖ < 1 ∧ ∀ x : F, absF x < 1 → absF x ≤ absF ϖ

/-- **Special lattices** (W1 §7.1, p. 34).  `R ⊆ U` is special for `(U, Q)` if there are an
orthogonal decomposition `U = Z' ⊕ U_an` with `Q|_{U_an}` anisotropic and a hyperbolic basis
`(w_i)_{i = ±1, …, ±n}` of `Z'` (`q(w_i, w_j) = δ_{i,-j}`), and `c ∈ ℤ` (with `val_F(q(v)) = c`
for some `v ∈ U_an` if `U_an ≠ 0`), such that `R = R_{Z'} ⊕ R_an`, where
`R_an = {v ∈ U_an : val_F(q(v)) ≥ c}` and `R_{Z'}` is the `𝔬_F`-lattice spanned by the `w_i`,
`i = 1, …, n`, and the `ϖ^c w_{-i}`.  Here `q(v) = ½ q(v, v) = ½ Q(v)` is W1's quadratic form. -/
def IsSpecialLattice {U : Type*} [AddCommGroup U] [Module F U] (Q : QuadraticForm F U) (ϖ : F)
    (R : Set U) : Prop :=
  ∃ (Uan : Submodule F U) (n : ℕ) (w : ℤ → U) (c : ℤ),
    (∀ v ∈ Uan, Q v = 0 → v = 0) ∧
    (∀ i j : ℤ, 1 ≤ |i| → |i| ≤ n → 1 ≤ |j| → |j| ≤ n →
      bform Q (w i) (w j) = if i + j = 0 then 1 else 0) ∧
    (∀ i : ℤ, 1 ≤ |i| → |i| ≤ n → ∀ v ∈ Uan, bform Q (w i) v = 0) ∧
    Submodule.span F (w '' {i : ℤ | 1 ≤ |i| ∧ |i| ≤ n}) ⊔ Uan = ⊤ ∧
    (Uan ≠ ⊥ → ∃ v ∈ Uan, absF (⅟(2 : F) * Q v) = absF ϖ ^ c) ∧
    R = {x | ∃ (a b : Fin n → F) (v : U), (∀ i, absF (a i) ≤ 1) ∧ (∀ i, absF (b i) ≤ 1) ∧
      v ∈ Uan ∧ absF (⅟(2 : F) * Q v) ≤ absF ϖ ^ c ∧
      x = ∑ i, a i • w ((i : ℕ) + 1) + ∑ i, b i • (ϖ ^ c • w (-((i : ℕ) + 1 : ℤ))) + v}

variable (L : LuoDatum F)

/-- The lattice `R = R₀ ⊕ R_Z` of `V` (W1 §7.2), for a lattice `R₀` of `V₀` and the lattice `R_Z`
of `Z` with basis `(c_i z_i)_{1 ≤ |i| ≤ r}`. -/
def latR (R0 : Set ↥L.V0sub) (cZ : ℤ → F) : Set L.V :=
  {x | ∃ x₀ ∈ R0, ∃ a : ℤ → F, (∀ i, absF (a i) ≤ 1) ∧
    x = (x₀ : L.V) + ∑ i ∈ (Finset.Icc (-(L.r : ℤ)) L.r).filter (· ≠ 0), a i • cZ i • L.zV i}

/-- `K`, the stabilizer of `R` in `G(F)` (W1 §7.2). -/
def stabK (R : Set L.V) : Set L.EndVˣ :=
  {k | k ∈ L.SOV ∧ (fun v => L.asV (k : L.EndV) v) '' R = R}

/-- `a ∈ A(F)` with `|val_F(a_i)| ≤ N`: `A` is the maximal subtorus of `SO(Z)` preserving each
line `F z_i` (acting trivially on `V₀`), `a_i` the eigenvalue on `z_i` (W1 §7.2). -/
def AN (ϖ : F) (N : ℕ) : Set L.EndVˣ :=
  {a | a ∈ L.SOV ∧ (∀ v ∈ L.V0sub, L.asV (a : L.EndV) v = v) ∧
    ∀ i : ℤ, 1 ≤ |i| → |i| ≤ L.r → ∃ t : F, L.asV (a : L.EndV) (L.zV i) = t • L.zV i ∧
      (0 < i → absF ϖ ^ N ≤ absF t ∧ absF t ≤ absF ϖ ^ (-(N : ℤ)))}

/-- `g₀ ∈ G₀(F) = SO(V₀)(F)` (acting trivially on `Z`) with `val_{R₀}(g₀⁻¹ v₀) ≥ −N`, i.e.
`g₀⁻¹ v₀ ∈ ϖ^{-N} R₀` (W1 §7.1, §7.2). -/
def G0N (ϖ : F) (R0 : Set ↥L.V0sub) (N : ℕ) : Set L.EndVˣ :=
  {g | g ∈ L.SOV ∧ (∀ v ∈ L.Zsub, L.asV (g : L.EndV) v = v) ∧
    ∃ x ∈ R0, L.asV ((g⁻¹ : L.EndVˣ) : L.EndV) (L.zV 0) = ϖ ^ (-(N : ℤ)) • (x : L.V)}

open Classical in
/-- **`κ_N`** (W1 §7.2, p. 35): the function on `G(F)`, left `U(F)`-invariant and right
`K`-invariant, whose restriction to `M(F) = A(F) G₀(F)` is the characteristic function of the
`a g₀` with `|val_F(a_i)| ≤ N` (`i = 1, …, r`) and `val_{R₀}(g₀⁻¹ v₀) ≥ −N`.  Written as: `1` if
`g = u a g₀ k` with `u ∈ U(F)`, `a g₀` as above and `k ∈ K`, else `0`. -/
def kappa (ϖ : F) (R0 : Set ↥L.V0sub) (cZ : ℤ → F) (N : ℕ) (g : ↥L.SOV) : ℂ :=
  if ∃ u : L.EndVˣ, u ∈ L.Nset ∧ ∃ a ∈ L.AN ϖ N, ∃ g₀ ∈ L.G0N ϖ R0 N, ∃ k ∈ L.stabK (L.latR R0 cZ),
      (g : L.EndVˣ) = u * a * g₀ * k then 1 else 0

end Kappa

/-! ## `I(θ, f, g)` and `I_N(θ, f)` (W1 §7.9) -/

section IN

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (L : LuoDatum F)

/-- A function on `𝔤(F)`, extended by `0` to `End V`. -/
def extV (f : ↥L.soV → ℂ) (X : L.EndV) : ℂ :=
  open Classical in if h : X ∈ L.soV then f ⟨X, h⟩ else 0

/-- `^g f^ξ(Y) = ∫_{𝔲(F)} f(g⁻¹ (Y + N) g) ξ(N) dN` (W1 §7.9), for `Y ∈ 𝔥(F)`. -/
def fXi (ψ : NontrivialAddChar F) (ξc : Fin L.r → F) (μU : Measure ↥L.lieU) (f : ↥L.soV → ℂ)
    (g : ↥L.SOV) (Y : L.EndW) : ℂ :=
  ∫ N : ↥L.lieU, L.extV f ((((g⁻¹ : ↥L.SOV) : L.EndVˣ) : L.EndV) *
      (L.ofV (L.extLie Y) + (N : L.EndV)) * (((g : ↥L.SOV) : L.EndVˣ) : L.EndV)) *
    ψ (L.xiArg ξc (L.asV N)) ∂μU

/-- `I(θ, f, g) = ∫_{𝔥(F)} θ(Y) ^g f^ξ(Y) dY` (W1 §7.9). -/
def Ig (ψ : NontrivialAddChar F) (ξc : Fin L.r → F) (μH : Measure ↥L.soW) (μU : Measure ↥L.lieU)
    (θ : ↥L.soW → ℂ) (f : ↥L.soV → ℂ) (g : ↥L.SOV) : ℂ :=
  ∫ Y : ↥L.soW, θ Y * L.fXi ψ ξc μU f g Y ∂μH

end IN

/-! ## Very cuspidal functions and `θ_f` on `𝔤(F)` (W1 §6.1) -/

section VeryCuspidal

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (L : LuoDatum F)

/-- `𝔭 = Lie(P_{F_V}) ∩ 𝔤` for an isotropic flag of `V`. -/
def lieParV (FV : IsotropicFlag L.QV) : Submodule F L.EndV :=
  L.soV.toSubmodule ⊓ (endFlagStab FV : Submodule F (Module.End F L.V))

/-- `𝔲_P = Lie(U_P) ∩ 𝔤`, the nilpotent radical of `𝔭`. -/
def lieUnipV (FV : IsotropicFlag L.QV) : Submodule F L.EndV :=
  L.soV.toSubmodule ⊓ (endFlagUnip FV : Submodule F (Module.End F L.V))

instance instMeasurableSpaceLieUnipV (FV : IsotropicFlag L.QV) :
    MeasurableSpace ↥(L.lieUnipV FV) := borel _

/-- The stabilizer of the flag is a proper parabolic subgroup of `G`: some `g ∈ G(F)` does not
stabilize it.  (Every parabolic subgroup of `SO(V)` is the stabilizer of an isotropic flag.) -/
def IsProperFlagV (FV : IsotropicFlag L.QV) : Prop :=
  ∃ g ∈ L.SOV, ¬ ∀ i, (FV.sub i).map (L.asV ((g : L.EndVˣ) : L.EndV)) ≤ FV.sub i

/-- **Very cuspidal functions on `𝔤(F)`** (W1 §6.1 (1)): `f ∈ C_c^∞(𝔤(F))` with
`∫_{𝔲(F)} f(X + N) dN = 0` for every proper parabolic `P = MU` of `G` and every `X ∈ 𝔪(F)`.
We quantify over `X ∈ 𝔭(F)` (the same condition, since `𝔭 = 𝔪 ⊕ 𝔲` and `dN` is invariant) and
over every Haar measure on `𝔲(F)` (they are proportional), the integrand being integrable. -/
def IsVeryCuspidal (f : ↥L.soV → ℂ) : Prop :=
  IsTestFn f ∧ ∀ FV : IsotropicFlag L.QV, L.IsProperFlagV FV →
    ∀ X : ↥L.soV, (X : L.EndV) ∈ L.lieParV FV →
      ∀ μ : Measure ↥(L.lieUnipV FV), μ.IsAddHaarMeasure →
        Integrable (fun N : ↥(L.lieUnipV FV) =>
            f ⟨(X : L.EndV) + N, L.soV.add_mem X.2 (Submodule.mem_inf.1 N.2).1⟩) μ ∧
          ∫ N : ↥(L.lieUnipV FV),
            f ⟨(X : L.EndV) + N, L.soV.add_mem X.2 (Submodule.mem_inf.1 N.2).1⟩ ∂μ
            = 0

/-- **`τ` is `θ_f`** (W1 §6.1): `τ` is a quasi-character on `𝔤(F)`, locally integrable,
continuous on `𝔤_reg(F)`, and represents the orbital pairing of `f`:
`∫_{𝔤(F)} τ f' dX = ∫_{G(F)} ∫_{𝔤(F)} f(g⁻¹ X g) f'(X) dX dg` for every test function `f'`,
with the self-dual measure `dX` for `ψ ∘ ⟨·,·⟩` (W1 §1.2) and the Haar measure `μG` on `G(F)`.
W1 defines `θ_f` on `𝔤_reg(F)` by weighted orbital integrals, which are not formalized; the identity
used here to pin it down is W1 §6.1 (2), `J(φ̂, f) = ∫ φ̂ θ_f`, with the geometric side `J` of the
local trace formula for `𝔤` written as the kernel integral (as in `luo_lie_geomExpansion_SO`
(b)); two continuous functions on `𝔤_reg(F)` with this property agree there. -/
def IsThetaFW1 (ψ : NontrivialAddChar F) (μG : Measure ↥L.SOV) (f τ : ↥L.soV → ℂ) : Prop :=
  IsLieQuasiCharacter L.SOV L.soV L.bV ψ τ ∧
    LocallyIntegrable τ (selfDualHaar L.soV L.bV ψ) ∧
    ContinuousOn τ {X : ↥L.soV | IsRegularSS L.soV (X : L.EndV)} ∧
    ∀ f' : ↥L.soV → ℂ, IsTestFn f' →
      ∫ X, τ X * f' X ∂selfDualHaar L.soV L.bV ψ =
        ∫ g : ↥L.SOV, (∫ X : ↥L.soV, L.extV f ((((g⁻¹ : ↥L.SOV) : L.EndVˣ) : L.EndV) *
          (X : L.EndV) * (((g : ↥L.SOV) : L.EndVˣ) : L.EndV)) * f' X
            ∂selfDualHaar L.soV L.bV ψ) ∂μG

end VeryCuspidal

/-! ## The geometric side `I(θ, f)` (W1 §7.3, §7.9) -/

section Geom

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (L : LuoDatum F)

/-- `T_Y`: the `h ∈ H(F)` commuting with `Y ∈ 𝔥(F)` and acting trivially on `W''(Y) = ker Y`
(`torusW`).  For `Y ∈ 𝔱_♮(F)`, `T ∈ 𝒯`, this is `T(F)` (W1 §7.3: `Z_H(t) = T H''`). -/
def torusH (Y : L.EndW) : Subgroup L.EndWˣ := L.torusW Y

/-- **`V''(Y) = W''(Y) ⊕ D ⊕ Z`** with `W''(Y) = ker Y` (W1 §7.3, §7.9). -/
def V2sub (Y : L.EndW) : Submodule F L.V := (LinearMap.ker (L.asW Y)).prod ⊤

/-- W1 §7.3 condition (4): if `d = dim V` is even, `d_an(W'') = 1`; if `d` is odd,
`d_an(V'') = 1`. -/
def Cond4 (Y : L.EndW) : Prop :=
  if Even (finrank F L.V) then L.anisoDimW (LinearMap.ker (L.asW Y)) = 1
  else L.anisoDim (L.V2sub Y) = 1

/-- `Y ∈ 𝔥(F)` defines a torus of `𝒯` (W1 §7.3): `Y` is semisimple and `T_Y` is a torus
(commutative `F`-points) with `A_T = 1` (compact `F`-points), and condition (4) holds.  Conditions
(2) (`dim W'` even, `W' = Y(W)`, automatic for semisimple skew `Y`) and (3) (`T` a maximal torus of
`SO(W')`) are built into `T = T_Y`. -/
def IsW1Elt (Y : L.EndW) : Prop :=
  Y ∈ L.soW ∧ IsSS F Y ∧ (∀ a ∈ L.torusH Y, ∀ b ∈ L.torusH Y, Commute a b) ∧
    CompactSpace ↥(L.torusH Y) ∧ L.Cond4 Y

/-- The tori `𝒯` (W1 §7.3). -/
def W1Torus : Type _ := {T : Subgroup L.EndWˣ // ∃ Y, L.IsW1Elt Y ∧ L.torusH Y = T}

/-- `H(F)`-conjugacy of tori. -/
def W1TorusConj (T T' : L.W1Torus) : Prop :=
  ∃ h ∈ L.SOW, T'.1 = T.1.map (MulAut.conj h).toMonoidHom

/-- The `H(F)`-conjugacy classes of `𝒯`. -/
def W1Class : Type _ := Quot L.W1TorusConj

/-- `|W(H, T)| = |Norm_{H(F)}(T)/Z_{H(F)}(T)|` (W1 §7.3). -/
def weylW1 (T : Subgroup L.EndWˣ) : ℕ :=
  Nat.card (↥(Subgroup.normalizer ((T.subgroupOf L.SOW : Subgroup ↥L.SOW) : Set ↥L.SOW)) ⧸
    (Subgroup.centralizer ((T.subgroupOf L.SOW : Subgroup ↥L.SOW) : Set ↥L.SOW)).subgroupOf
      (Subgroup.normalizer ((T.subgroupOf L.SOW : Subgroup ↥L.SOW) : Set ↥L.SOW)))

/-- The common fixed space `W''_T` of `T` in `W`. -/
def fixedW (T : Subgroup L.EndWˣ) : Submodule F L.W :=
  ⨅ t : ↥T, LinearMap.ker (L.asW ((t : L.EndWˣ) : L.EndW) - 1)

/-- `𝔱 = Lie(T)`: the `Y ∈ 𝔥` commuting with `T` and killing `W''_T`. -/
def lieTorusW (T : Subgroup L.EndWˣ) : Submodule F L.EndW where
  carrier := {Y | Y ∈ L.soW ∧ (∀ t ∈ T, ((t : L.EndWˣ) : L.EndW) * Y = Y * (t : L.EndWˣ)) ∧
    ∀ w ∈ L.fixedW T, (L.asW Y) w = 0}
  add_mem' := fun {X Y} hX hY => ⟨L.soW.add_mem hX.1 hY.1,
    fun t ht => by rw [mul_add, add_mul, hX.2.1 t ht, hY.2.1 t ht],
    fun w hw => by
      show (L.asW X) w + (L.asW Y) w = 0
      rw [hX.2.2 w hw, hY.2.2 w hw, add_zero]⟩
  zero_mem' := ⟨L.soW.zero_mem, fun _ _ => by simp, fun _ _ => rfl⟩
  smul_mem' := fun c {X} hX => ⟨L.soW.smul_mem c hX.1,
    fun t ht => by rw [mul_smul_comm, smul_mul_assoc, hX.2.1 t ht],
    fun w hw => by
      show c • (L.asW X) w = 0
      rw [hX.2.2 w hw, smul_zero]⟩

instance instMeasurableSpaceLieTorusW (T : Subgroup L.EndWˣ) :
    MeasurableSpace ↥(L.lieTorusW T) := borel _

instance instBorelSpaceLieTorusW (T : Subgroup L.EndWˣ) : BorelSpace ↥(L.lieTorusW T) := ⟨rfl⟩

/-- **`Y ∈ 𝔱_♮(F)`** (W1 §7.9): `Y ∈ 𝔱`, `ker Y = W''_T`, and the eigenvalues of `Y` on
`W' = Y(W)` are distinct (squarefree characteristic polynomial; characteristic `0`). -/
def IsNatW (T : Subgroup L.EndWˣ) (Y : L.EndW) : Prop :=
  Y ∈ L.lieTorusW T ∧ LinearMap.ker (L.asW Y) = L.fixedW T ∧
    Squarefree (LinearMap.charpoly ((L.asW Y).restrict
      (p := LinearMap.range (L.asW Y)) (q := LinearMap.range (L.asW Y))
      (fun v _ => LinearMap.mem_range_self _ v)))

/-- `Δ(Y) = |det(Y|_{W/W''(Y)})|_F` (W1 §7.9), computed on `Y(W) ≅ W/ker Y`. -/
def deltaW (Y : L.EndW) : ℝ :=
  absF (LinearMap.det ((L.asW Y).restrict
    (p := LinearMap.range (L.asW Y)) (q := LinearMap.range (L.asW Y))
    (fun v _ => LinearMap.mem_range_self _ v)))

/-- `ν(T) dY`: the measure on `𝔱(F)` deduced through `exp` from the measure `d_c t = ν(T) dt` on
`T(F)`, which for `A_T = 1` has total mass `1` (W1 §1.2). -/
def IsExpCompatTW (T : Subgroup L.EndWˣ) (μ : Measure ↥(L.lieTorusW T)) : Prop :=
  letI : MeasurableSpace ↥T := borel _
  haveI : BorelSpace ↥T := ⟨rfl⟩
  μ.IsAddHaarMeasure ∧
    ∃ O ∈ 𝓝 (0 : ↥(L.lieTorusW T)), ∀ S : Set ↥(L.lieTorusW T), MeasurableSet S → S ⊆ O →
      μ S = probHaar ↥T {t | ∃ X ∈ S, ((t : L.EndWˣ) : L.EndW) = expA F (X : L.EndW)}

/-- W1's choice of orbit for `c_θ` at `Y ∈ 𝔱_♮(F)` (W1 §7.3, §7.9), as a condition on a nilpotent
`N ∈ 𝔥_Y`: if `d` is odd and `dim W''(Y) ≥ 4`, `N ∈ O_{−ν₀}` on `W''(Y)`; otherwise the regular
orbit is unique (W1 §7.3) and there is no condition.  `IsInOrbitNu Q U ν` asks for an anisotropic
line of `Q`-value `ν`, i.e. of W1-value `ν/2`; W1's `ν₀ = q(v₀) = ½ Q(z₀) = nu0 / 2`, so W1's
`O_{±ν₀}` is `IsInOrbitNu … (±nu0)`. -/
def SpecH (Y N : L.EndW) : Prop :=
  if ¬ Even (finrank F L.V) ∧ 4 ≤ finrank F (LinearMap.ker (L.asW Y)) then
    IsInOrbitNu L.QW (LinearMap.ker (L.asW Y)) (-L.nu0) N
  else True

/-- W1's choice of orbit for `c_f` at `Y` (W1 §7.3, §7.9): if `d` is even and
`dim V''(Y) ≥ 4`, `N ∈ O_{ν₀}` on `V''(Y)`; otherwise the regular orbit is unique. -/
def SpecG (Y : L.EndW) (N : L.EndV) : Prop :=
  if Even (finrank F L.V) ∧ 4 ≤ finrank F (L.V2sub Y) then
    IsInOrbitNu L.QV (L.V2sub Y) L.nu0 N
  else True

open Classical in
/-- The regular nilpotent orbit of `𝔥_Y` selected by `SpecH` (the zero orbit if none). -/
def orbitH (Y : L.EndW) : NilOrbit (lieGrpCentralizer L.SOW Y) (lieCentralizer L.soW Y) :=
  if h : ∃ O ∈ NilReg (lieGrpCentralizer L.SOW Y) (lieCentralizer L.soW Y),
      ∃ N ∈ nilOrbitSet O, L.SpecH Y (N : L.EndW)
  then h.choose
  else Quotient.mk (nilSetoid _ _) ⟨0, LieSubalgebra.zero_mem _, IsNilpotent.zero⟩

open Classical in
/-- The regular nilpotent orbit of `𝔤_Y` selected by `SpecG` (the zero orbit if none). -/
def orbitG (Y : L.EndW) :
    NilOrbit (lieGrpCentralizer L.SOV (L.extLie Y : L.EndV)) (lieCentralizer L.soV (L.extLie Y)) :=
  if h : ∃ O ∈ NilReg (lieGrpCentralizer L.SOV (L.extLie Y : L.EndV))
      (lieCentralizer L.soV (L.extLie Y)), ∃ N ∈ nilOrbitSet O, L.SpecG Y (N : L.EndV)
  then h.choose
  else Quotient.mk (nilSetoid _ _) ⟨0, LieSubalgebra.zero_mem _, IsNilpotent.zero⟩

/-- `c_θ(Y) = c_{θ, O}(Y)` (W1 §7.3, §7.9), for a quasi-character `θ` on `𝔥(F)`. -/
def cThetaW (ψ : NontrivialAddChar F) (θ : ↥L.soW → ℂ) (Y : L.EndW) : ℂ :=
  germLie L.SOW L.soW L.bW ψ θ Y (L.orbitH Y)

/-- `c_f(Y) = c_{θ_f, O}(Y)` (W1 §7.3, §7.9), with `τ = θ_f`. -/
def cFW (ψ : NontrivialAddChar F) (τ : ↥L.soV → ℂ) (Y : L.EndW) : ℂ :=
  germLie L.SOV L.soV L.bV ψ τ (L.extLie Y) (L.orbitG Y)

open Classical in
/-- The integrand `c_θ(Y) c_f(Y) D^H(Y) Δ(Y)^r` on `𝔱(F)`, `0` off `𝔱_♮(F)`. -/
def geomIntegrand (ψ : NontrivialAddChar F) (θ : ↥L.soW → ℂ) (τ : ↥L.soV → ℂ)
    (T : Subgroup L.EndWˣ) (Y : L.EndW) : ℂ :=
  if L.IsNatW T Y then
    L.cThetaW ψ θ Y * L.cFW ψ τ Y * (weylDiscLie L.soW Y : ℂ) * ((L.deltaW Y ^ L.r : ℝ) : ℂ)
  else 0

/-- **`I(θ, f) = Σ_{T ∈ 𝒯} |W(H, T)|⁻¹ ν(T) ∫_{𝔱(F)} c_θ(Y) c_f(Y) D^H(Y) Δ(Y)^r dY`**
(W1 §7.9), over representatives of the `H(F)`-conjugacy classes, with `μT` the measures
`ν(T) dY` and `τ = θ_f`. -/
def Igeom (ψ : NontrivialAddChar F) (μT : ∀ T : L.W1Torus, Measure ↥(L.lieTorusW T.1))
    (θ : ↥L.soW → ℂ) (τ : ↥L.soV → ℂ) : ℂ :=
  ∑' c : L.W1Class, ((L.weylW1 (Quot.out c).1 : ℂ))⁻¹ *
    ∫ Y : ↥(L.lieTorusW (Quot.out c).1), L.geomIntegrand ψ θ τ (Quot.out c).1 Y ∂μT (Quot.out c)

end Geom

/-! ## The data of W1 §7.2 and the measures (W1 §1.2) -/

section Input

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (L : LuoDatum F)

/-- **The data of W1 §7.2 and the measures of W1 §1.2, §7.2.**
* `ξc`: the `ξ_i ∈ F^×`;
* `ϖ`, `R0`, `cZ`: a special lattice `R₀` of `V₀` and a lattice `R_Z` of `Z` with basis
  `(c_i z_i)` such that `R = R₀ ⊕ R_Z` is special; `K` is its stabilizer (`κ_N`);
* `μG` on `G(F)`, `μU` on `U(F)`, `μH` on `H(F)`, `μUH` on `U(F)H(F)` with `d(uh) = du dh`, and
  `m` the quotient measure on `U(F)H(F)\G(F)`;
* `μ𝔥` on `𝔥(F)` and `μ𝔲` on `𝔲(F)` deduced from `μH` and `μU` through `exp` (Jacobian `1`
  near `0`, W1 §1.2: "en inversant le procédé ci-dessus, on munit aussi `u(F)` d'une mesure");
* `μT`, the measures `ν(T) dY` on the `𝔱(F)`.
W1 fixes the measures absolutely (self-dual on `𝔤(F)` and `𝔥(F)`, the group measures compatible
with them through `exp`, the measure on `U(F)` normalized by `K`); here `μG` is any Haar measure,
which multiplies both sides of the theorem by the same constant (through `θ_f`), and `μ𝔥`, `μ𝔲`
appear only together with `μH`, `μU`, through the ratio fixed by `exp`. -/
structure W1Input (ψ : NontrivialAddChar F) where
  ξc : Fin L.r → F
  ξc_ne : ∀ i, ξc i ≠ 0
  ϖ : F
  hϖ : IsUniformizer ϖ
  R0 : Set ↥L.V0sub
  hR0 : IsSpecialLattice (L.QV.comp L.V0sub.subtype) ϖ R0
  cZ : ℤ → F
  cZ_ne : ∀ i, cZ i ≠ 0
  hR : IsSpecialLattice L.QV ϖ (L.latR R0 cZ)
  μG : Measure ↥L.SOV
  μG_haar : μG.IsHaarMeasure
  μU : Measure ↥L.Ubar
  μU_haar : μU.IsHaarMeasure
  μH : Measure ↥L.Hbar'
  μH_haar : μH.IsHaarMeasure
  μUH : Measure ↥L.UHbar
  μUH_haar : μUH.IsHaarMeasure
  μUH_prod : ∀ φ : ↥L.UHbar → ℝ, Continuous φ → HasCompactSupport φ →
    ∫ x, φ x ∂μUH = ∫ u, ∫ h, φ (Subgroup.inclusion L.Ubar_le_UHbar u *
      Subgroup.inclusion L.Hbar'_le_UHbar h) ∂μH ∂μU
  m : Measure (CosetSpace L.UHbar.subtype)
  hm : IsWeilMeasure L.UHbar.subtype μG μUH m
  μ𝔥 : Measure ↥L.soW
  h𝔥 : μ𝔥.IsAddHaarMeasure ∧ ∃ O ∈ 𝓝 (0 : ↥L.soW), ∀ S : Set ↥L.soW, MeasurableSet S → S ⊆ O →
    μ𝔥 S = μH {h | ∃ Y ∈ S, ((((h : ↥L.SOV) : L.EndVˣ)) : L.EndV) =
      expA F (L.ofV (L.extLie (L.asW (Y : L.EndW))))}
  μ𝔲 : Measure ↥L.lieU
  h𝔲 : μ𝔲.IsAddHaarMeasure ∧ ∃ O ∈ 𝓝 (0 : ↥L.lieU), ∀ S : Set ↥L.lieU, MeasurableSet S → S ⊆ O →
    μ𝔲 S = μU {u | ∃ N ∈ S, ((((u : ↥L.SOV) : L.EndVˣ)) : L.EndV) = expA F (N : L.EndV)}
  μT : ∀ T : L.W1Torus, Measure ↥(L.lieTorusW T.1)
  hμT : ∀ T : L.W1Torus, L.IsExpCompatTW T.1 (μT T)

variable {L} {ψ : NontrivialAddChar F}

/-- `I(θ, f, g)` for the data `I`. -/
def W1Input.Ig (I : L.W1Input ψ) (θ : ↥L.soW → ℂ) (f : ↥L.soV → ℂ) (g : ↥L.SOV) : ℂ :=
  L.Ig ψ I.ξc I.μ𝔥 I.μ𝔲 θ f g

/-- **`I_N(θ, f) = ∫_{U(F)H(F)\G(F)} I(θ, f, g) κ_N(g) dg`** (W1 §7.9), evaluated on the chosen
representative of each coset (both factors are left `U(F)H(F)`-invariant). -/
def W1Input.IN (I : L.W1Input ψ) (θ : ↥L.soW → ℂ) (f : ↥L.soV → ℂ) (N : ℕ) : ℂ :=
  ∫ q, I.Ig θ f (CosetSpace.out L.UHbar.subtype q) *
    L.kappa I.ϖ I.R0 I.cZ N (CosetSpace.out L.UHbar.subtype q) ∂I.m

/-- `I(θ, f)` for the data `I`. -/
def W1Input.Igeom (I : L.W1Input ψ) (θ : ↥L.soW → ℂ) (τ : ↥L.soV → ℂ) : ℂ :=
  L.Igeom ψ I.μT θ τ

end Input

end LuoDatum

end GSpinGGP
