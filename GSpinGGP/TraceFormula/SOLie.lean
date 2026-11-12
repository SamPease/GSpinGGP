/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LieAlgebra
import GSpinGGP.Literature.Measure
import GSpinGGP.Literature.Fourier
import GSpinGGP.TraceFormula.SelfDual
import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.SpecialOrthogonal

/-!
# The special orthogonal GGP triple on the Lie algebra (Luo's objects)

Definitions of the objects of Luo, *A local trace formula for the local Gan–Gross–Prasad
conjecture for special orthogonal groups* (arXiv:2009.13947v1), §2.1, §4, §7.1, for the
special orthogonal GGP triple `(Ḡ, H̄, ξ)` of an admissible pair `(W, V)`, on the Lie algebra
`𝔤 = so(W) ⊕ so(V)`.  They are defined **directly on the quadratic spaces**, with
`Ḡ = SO(W) × SO(V)` inside the units of `End W × End V`; nothing here refers to Clifford
algebras or to `GSpin`.  They are the objects of the literature axiom
`luo_lie_geomExpansion_SO` (`Literature/Luo.lean`).  The identification with the objects of the
general spin triple on `𝔤⁰` (`TraceFormula/LieAlgebra.lean`) is `TraceFormula/LuoTransfer.lean`.

The generic Lie-algebra notions are reused: `selfDualHaar`, `IsTestFn`, `IsLieQuasiCharacter`,
`germLie` (with `jHat`), `weylDiscLie`, `regularSetLie`, `NilReg`, `IsInOrbitNu`, `probHaar`,
`CosetSpace`, `IsWeilMeasure`.

## Contents
* `LuoDatum`: an admissible pair `V = W ⊕^⊥ D ⊕^⊥ Z` with Luo's basis `z_{-r}, …, z_r`,
  `q(z_i, z_j) = δ_{i,-j}` (`i, j ≠ 0`), `ν₀ = q(z₀, z₀) ≠ 0` (Luo §2.1, Def 2.1.3).
* `Amb = End W × End V`, `Gbar = SO(W) × SO(V)`, `lie = so(W) ⊕ so(V)`, the trace form
  `traceForm = ½(tr_W + tr_V)` (Luo §2.1).
* `lieN`, `Nset`, `Hbar = SO(W) ⋉ N`, `lieH = so(W) ⊕ 𝔫`, `lam` (`λ`), `xi` (`ξ`) (Luo §2.1).
* `IsExpCompat`, `kernelLie`, `distribJLie` (`J^Lie`, Luo §4), with the measure data passed as
  arguments (Haar measures, `exp`-compatible measure on `𝔥`, Weil quotient measure).
* `IsScusp`: strongly cuspidal Schwartz–Bruhat functions on `𝔤(F)` (Luo p. 7; BP §5.1;
  Waldspurger 2010 §6.1).
* `orbitalPairing`.
* `isClosed_Gbar`: `Ḡ(F)` is closed in `(End W × End V)ˣ`, hence locally compact.
* `Γ^Lie(Ḡ, H̄)` (Luo §7.1): `torusOf`, `IsGammaElt`, `GammaTorus`, `GammaClass`, `lieTorus`,
  `IsNat` (`t_♮`), `weylCard` (`|W(H̄,T)|`), `IsExpCompatT`, `delta` (`Δ`), `OrbitSpec`,
  `orbitChoice`, `gammaIntegrand`, `mGeomLieS`.
-/

noncomputable section

open MeasureTheory Topology Filter Module

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

/-- **An admissible pair with Luo's basis** (Luo §2.1, Def 2.1.3; Waldspurger 2010 §7.2):
`W = F^m` with a nondegenerate quadratic form `QW` (`m = 0` allowed), and
`V = W ⊕^⊥ (D ⊕ Z)` with `D ⊕ Z = F^{2r+1}` carrying `QZ` and vectors `z_{-r}, …, z_r` such that
`q(z_i, z_j) = δ_{i,-j}` for `i, j ∈ {±1, …, ±r}`, `q(z₀, z_i) = 0` for `i ≠ 0`, and
`ν₀ = q(z₀, z₀) ≠ 0`; here `q` is the symmetric bilinear form with `q(v, v) = QZ(v)`
(`bform`).  The `2r + 1` vectors then form a basis of `F^{2r+1}` (their Gram matrix is
invertible), `D = F z₀` is an anisotropic line and `Z = ⟨z_{±1}, …, z_{±r}⟩` is hyperbolic. -/
structure LuoDatum (K : Type*) [Field K] [Invertible (2 : K)] where
  m : ℕ
  QW : QuadraticForm K (Fin m → K)
  nondeg : IsNondeg QW
  r : ℕ
  QZ : QuadraticForm K (Fin (2 * r + 1) → K)
  z : ℤ → (Fin (2 * r + 1) → K)
  gram : ∀ i j : ℤ, |i| ≤ r → |j| ≤ r →
    bform QZ (z i) (z j) = if i + j = 0 then (if i = 0 then QZ (z 0) else 1) else 0
  aniso : QZ (z 0) ≠ 0

namespace LuoDatum

variable {K : Type*} [Field K] [Invertible (2 : K)] (L : LuoDatum K)

/-- `W = K^m`. -/
abbrev W : Type _ := Fin L.m → K

/-- `D ⊕ Z = K^{2r+1}`. -/
abbrev Zs : Type _ := Fin (2 * L.r + 1) → K

/-- `V = W ⊕^⊥ (D ⊕ Z)`. -/
abbrev V : Type _ := L.W × L.Zs

/-- The form on `V`. -/
abbrev QV : QuadraticForm K L.V := L.QW.prod L.QZ

/-- `ν₀ = q(z₀, z₀)` (Luo §2.1). -/
def nu0 : K := L.QZ (L.z 0)

/-- `z_i` as a vector of `V`. -/
def zV (i : ℤ) : L.V := (0, L.z i)

/-- `Z_k = ⟨z_r, …, z_{r-k+1}⟩` (`Z_0 = 0`), the members of the isotropic flag
`⟨z_r⟩ ⊂ ⟨z_r, z_{r-1}⟩ ⊂ ⋯ ⊂ ⟨z_r, …, z_1⟩` of Luo §2.1 (`0 ≤ k ≤ r`). -/
def flagSub (k : ℕ) : Submodule K L.V :=
  Submodule.span K (Set.range fun j : Fin k => L.zV ((L.r : ℤ) - (j : ℕ)))

/-- The extension `End W → End V`, `X ↦ X ⊕ 0` (the Lie-algebra form of `SO(W) ⊆ SO(V)`). -/
def extLie : Module.End K L.W →ₗ[K] Module.End K L.V :=
  (LinearMap.prodMapAlgHom K L.W L.Zs).toLinearMap.comp
    (LinearMap.inl K (Module.End K L.W) (Module.End K L.Zs))

/-- The embedding `End W →* End V`, `g ↦ g ⊕ 1` (`SO(W) ⊆ SO(V)` acting trivially on `D ⊕ Z`). -/
def extGrp : Module.End K L.W →* Module.End K L.V :=
  (LinearMap.prodMapAlgHom K L.W L.Zs).toMonoidHom.comp (MonoidHom.inl _ _)

/-! ## The ambient algebra `End W × End V` and `Ḡ = SO(W) × SO(V)` -/

/-- The ambient algebra `End W × End V` of `Ḡ = SO(W) × SO(V)` and of `𝔤 = so(W) ⊕ so(V)`
(a type synonym, so that its Lie algebra structure is the commutator one). -/
def Amb : Type _ := Module.End K L.W × Module.End K L.V

instance : Ring L.Amb := inferInstanceAs (Ring (Module.End K L.W × Module.End K L.V))

instance : Algebra K L.Amb := inferInstanceAs (Algebra K (Module.End K L.W × Module.End K L.V))

instance : Module.Finite K L.Amb :=
  inferInstanceAs (Module.Finite K (Module.End K L.W × Module.End K L.V))

/-- The pair `(X_W, X_V)` as an element of `Amb`. -/
def pair (a : Module.End K L.W) (b : Module.End K L.V) : L.Amb := (a, b)

/-- The `End W`-component. -/
def fstA : L.Amb →ₐ[K] Module.End K L.W := AlgHom.fst K (Module.End K L.W) (Module.End K L.V)

/-- The `End V`-component. -/
def sndA : L.Amb →ₐ[K] Module.End K L.V := AlgHom.snd K (Module.End K L.W) (Module.End K L.V)

@[simp] theorem fstA_pair (a b) : L.fstA (L.pair a b) = a := rfl
@[simp] theorem sndA_pair (a b) : L.sndA (L.pair a b) = b := rfl

/-- `SO(U)` as a subgroup of `(End U)ˣ` (`SOGrp` through `GL(U) ≃ Aut(U)`). -/
def SOu {U : Type*} [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) :
    Subgroup (Module.End K U)ˣ :=
  (SOGrp Q).comap (LinearMap.GeneralLinearGroup.generalLinearEquiv K U).toMonoidHom

/-- The `GL(W)`-component of a unit of `Amb`. -/
def unitFst : L.Ambˣ →* (Module.End K L.W)ˣ := Units.map L.fstA.toMonoidHom

/-- The `GL(V)`-component of a unit of `Amb`. -/
def unitSnd : L.Ambˣ →* (Module.End K L.V)ˣ := Units.map L.sndA.toMonoidHom

/-- **`Ḡ = SO(W) × SO(V)`** (Luo §2.1), as a subgroup of `(End W × End V)ˣ`. -/
def Gbar : Subgroup L.Ambˣ := (SOu L.QW).comap L.unitFst ⊓ (SOu L.QV).comap L.unitSnd

/-- The diagonal embedding `(End W)ˣ → (End W × End V)ˣ`, `g ↦ (g, g ⊕ 1)`. -/
def diagU : (Module.End K L.W)ˣ →* L.Ambˣ :=
  Units.map ((MonoidHom.id _).prod L.extGrp : Module.End K L.W →* L.Amb)

/-- The diagonal embedding `End W → End W × End V`, `X ↦ (X, X ⊕ 0)` on the Lie algebra. -/
def diagLie (X : Module.End K L.W) : L.Amb := L.pair X (L.extLie X)

/-! ## `𝔤 = so(W) ⊕ so(V)` and the trace form -/

/-- **`𝔤 = so(W) ⊕ so(V)`** (Luo §2.1): the pairs of endomorphisms that are skew for the
bilinear forms of `W` and `V`. -/
def lie : LieSubalgebra K L.Amb where
  carrier := {X | L.fstA X ∈ skewAdjointLieSubalgebra (bform L.QW) ∧
    L.sndA X ∈ skewAdjointLieSubalgebra (bform L.QV)}
  add_mem' := fun {X Y} hX hY => ⟨by rw [map_add]; exact add_mem hX.1 hY.1,
    by rw [map_add]; exact add_mem hX.2 hY.2⟩
  zero_mem' := ⟨by rw [map_zero]; exact zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  smul_mem' := fun c {X} hX => ⟨by rw [map_smul]; exact Submodule.smul_mem _ c hX.1,
    by rw [map_smul]; exact Submodule.smul_mem _ c hX.2⟩
  lie_mem' := fun {X Y} hX hY => by
    refine ⟨?_, ?_⟩
    · have h := LieSubalgebra.lie_mem _ hX.1 hY.1
      rw [Ring.lie_def] at h
      rw [Ring.lie_def, map_sub, map_mul, map_mul]
      exact h
    · have h := LieSubalgebra.lie_mem _ hX.2 hY.2
      rw [Ring.lie_def] at h
      rw [Ring.lie_def, map_sub, map_mul, map_mul]
      exact h

theorem mem_lie {X : L.Amb} : X ∈ L.lie ↔ L.fstA X ∈ skewAdjointLieSubalgebra (bform L.QW) ∧
    L.sndA X ∈ skewAdjointLieSubalgebra (bform L.QV) := Iff.rfl

/-- **The trace form `B(X, Y) = ½ (tr(X_W Y_W) + tr(X_V Y_V))`** on `End W × End V`
(Luo §2.1, p. 10). -/
def traceForm : LinearMap.BilinForm K L.Amb :=
  LinearMap.mk₂ K (fun X Y => ⅟(2 : K) * (LinearMap.trace K L.W (L.fstA X * L.fstA Y) +
      LinearMap.trace K L.V (L.sndA X * L.sndA Y)))
    (fun X X' Y => by simp only [map_add, add_mul]; ring)
    (fun c X Y => by simp only [map_smul, smul_mul_assoc, smul_eq_mul]; ring)
    (fun X Y Y' => by simp only [map_add, mul_add]; ring)
    (fun c X Y => by simp only [map_smul, mul_smul_comm, smul_eq_mul]; ring)

end LuoDatum

/-! ## `SO(Q)` is closed -/

section SOClosed

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- `SO(Q)` is closed in `GL(V)` (Tau Ceti's `isClosed_specialOrthogonalGroup`). -/
theorem isClosed_SOGrp [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    [FiniteDimensional K V] (Q : QuadraticForm K V) :
    IsClosed (SOGrp Q : Set (V ≃ₗ[K] V)) := by
  rw [SOGrp_eq_specialOrthogonalGroup]
  exact TauCeti.QuadraticMap.isClosed_specialOrthogonalGroup Q

end SOClosed

/-! ## Topology on `End W × End V` -/

namespace LuoDatum

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (L : LuoDatum F)

/-- The module topology on `End W × End V`. -/
instance instTopologicalSpaceAmb : TopologicalSpace L.Amb := moduleTopology F L.Amb

instance instIsModuleTopologyAmb : IsModuleTopology F L.Amb := ⟨rfl⟩

instance instIsTopologicalRingAmb : IsTopologicalRing L.Amb :=
  isTopologicalRing_of_moduleTopology F L.Amb

instance instMeasurableSpaceGbar : MeasurableSpace ↥L.Gbar := borel _

instance instBorelSpaceGbar : BorelSpace ↥L.Gbar := ⟨rfl⟩

instance instMeasurableSpaceLie : MeasurableSpace ↥L.lie := borel _

instance instBorelSpaceLie : BorelSpace ↥L.lie := ⟨rfl⟩

example : IsTopologicalGroup ↥L.Gbar := inferInstance

theorem continuous_fstA : Continuous (L.fstA : L.Amb → Module.End F L.W) := by
  exact IsModuleTopology.continuous_of_linearMap L.fstA.toLinearMap

theorem continuous_sndA : Continuous (L.sndA : L.Amb → Module.End F L.V) := by
  exact IsModuleTopology.continuous_of_linearMap L.sndA.toLinearMap

/-- **`Ḡ(F) = SO(W)(F) × SO(V)(F)` is closed in `(End W × End V)ˣ`**: it is the preimage of
`SO(W) × SO(V)` (closed, `isClosed_SOGrp`) under the continuous map to `GL(W) × GL(V)`. -/
theorem isClosed_Gbar : IsClosed (L.Gbar : Set L.Ambˣ) := by
  have hW : Continuous fun u : L.Ambˣ =>
      LinearMap.GeneralLinearGroup.generalLinearEquiv F L.W (L.unitFst u) := by
    rw [TauCeti.continuous_linearEquiv_iff]
    exact ⟨L.continuous_fstA.comp Units.continuous_val,
      L.continuous_fstA.comp Units.continuous_coe_inv⟩
  have hV : Continuous fun u : L.Ambˣ =>
      LinearMap.GeneralLinearGroup.generalLinearEquiv F L.V (L.unitSnd u) := by
    rw [TauCeti.continuous_linearEquiv_iff]
    exact ⟨L.continuous_sndA.comp Units.continuous_val,
      L.continuous_sndA.comp Units.continuous_coe_inv⟩
  exact ((isClosed_SOGrp L.QW).preimage hW).inter ((isClosed_SOGrp L.QV).preimage hV)

/-- `Ḡ(F)` is locally compact (`isClosed_Gbar`). -/
instance instLocallyCompactSpaceGbar : LocallyCompactSpace ↥L.Gbar :=
  subgroup_locallyCompactSpace_of_isClosed F L.Amb L.Gbar L.isClosed_Gbar

/-- `Ḡ(F)` is Hausdorff. -/
instance instT2SpaceGbar : T2Space ↥L.Gbar := subgroup_t2Space F L.Amb L.Gbar

/-! ## `N`, `H̄ = SO(W) ⋉ N`, `𝔥 = so(W) ⊕ 𝔫` and `ξ` (Luo §2.1) -/

section H

variable {K : Type*} [Field K] [Invertible (2 : K)] (L : LuoDatum K)

/-- **`𝔫 = Lie(N)`**: the `X ∈ so(V)` with `X Z_{k+1} ⊆ Z_k` (`k < r`) and
`X (Z_r^⊥) ⊆ Z_r`, i.e. the nilpotent radical of the parabolic subalgebra of `so(V)` stabilizing
the flag `Z_1 ⊂ ⋯ ⊂ Z_r` (it acts by `0` on the graded pieces of
`0 ⊂ Z_1 ⊂ ⋯ ⊂ Z_r ⊂ Z_r^⊥ ⊂ ⋯ ⊂ Z_1^⊥ ⊂ V`; the conditions on `Z_k^⊥` follow by skewness). -/
def lieN : Submodule K (Module.End K L.V) where
  carrier := {X | X ∈ skewAdjointLieSubalgebra (bform L.QV) ∧
    (∀ k : ℕ, k < L.r → ∀ v ∈ L.flagSub (k + 1), X v ∈ L.flagSub k) ∧
    ∀ v ∈ (bform L.QV).orthogonal (L.flagSub L.r), X v ∈ L.flagSub L.r}
  add_mem' := fun hX hY => ⟨add_mem hX.1 hY.1,
    fun k hk v hv => add_mem (hX.2.1 k hk v hv) (hY.2.1 k hk v hv),
    fun v hv => add_mem (hX.2.2 v hv) (hY.2.2 v hv)⟩
  zero_mem' := ⟨zero_mem _, fun _ _ _ _ => zero_mem _, fun _ _ => zero_mem _⟩
  smul_mem' := fun c _ hX => ⟨Submodule.smul_mem _ c hX.1,
    fun k hk v hv => Submodule.smul_mem _ c (hX.2.1 k hk v hv),
    fun v hv => Submodule.smul_mem _ c (hX.2.2 v hv)⟩

/-- **The unipotent radical `N`** of the parabolic subgroup `P_V` of `SO(V)` stabilizing the flag
`⟨z_r⟩ ⊂ ⋯ ⊂ ⟨z_r, …, z_1⟩` (Luo §2.1): the `n ∈ SO(V)` acting trivially on the graded pieces,
`(n − 1) Z_{k+1} ⊆ Z_k` (`k < r`) and `(n − 1)(Z_r^⊥) ⊆ Z_r` (the conditions on `Z_k^⊥` follow
since `n` is an isometry). -/
def Nset : Set (Module.End K L.V)ˣ :=
  {n | n ∈ SOu L.QV ∧
    (∀ k : ℕ, k < L.r → ∀ v ∈ L.flagSub (k + 1), (n : Module.End K L.V) v - v ∈ L.flagSub k) ∧
    ∀ v ∈ (bform L.QV).orthogonal (L.flagSub L.r), (n : Module.End K L.V) v - v ∈ L.flagSub L.r}

/-- `GL(V) → (End W × End V)ˣ`, `n ↦ (1, n)`. -/
def inrU : (Module.End K L.V)ˣ →* L.Ambˣ :=
  Units.map (MonoidHom.inr (Module.End K L.W) (Module.End K L.V) : Module.End K L.V →* L.Amb)

/-- **`H̄ = SO(W) ⋉ N`** (Luo §2.1), the subgroup of `(End W × End V)ˣ` generated by the diagonal
`SO(W)` (`g ↦ (g, g ⊕ 1)`) and `{1} × N`.  (`SO(W)` normalizes `N`, so this is the set of
products `(g, (g ⊕ 1) n)`.) -/
def HbarU : Subgroup L.Ambˣ :=
  Subgroup.closure (L.diagU '' (SOu L.QW : Set (Module.End K L.W)ˣ) ∪ L.inrU '' L.Nset)

/-- `H̄` as a subgroup of `Ḡ` (`H̄ ⊆ Ḡ`). -/
def Hbar : Subgroup ↥L.Gbar := L.HbarU.subgroupOf L.Gbar

/-- **`𝔥 = Lie(H̄) = so(W) ⊕ 𝔫`**: the `X = (X_W, X_V) ∈ 𝔤` with `X_V − (X_W ⊕ 0) ∈ 𝔫`. -/
def lieH : Submodule K L.Amb where
  carrier := {X | X ∈ L.lie ∧ L.sndA X - L.extLie (L.fstA X) ∈ L.lieN}
  add_mem' := fun {X Y} hX hY => ⟨add_mem hX.1 hY.1, by
    have e : L.sndA (X + Y) - L.extLie (L.fstA (X + Y)) =
        (L.sndA X - L.extLie (L.fstA X)) + (L.sndA Y - L.extLie (L.fstA Y)) := by
      simp only [map_add]; abel
    rw [e]; exact add_mem hX.2 hY.2⟩
  zero_mem' := ⟨zero_mem _, by simp⟩
  smul_mem' := fun c {X} hX => ⟨Submodule.smul_mem _ c hX.1, by
    have e : L.sndA (c • X) - L.extLie (L.fstA (c • X)) =
        c • (L.sndA X - L.extLie (L.fstA X)) := by
      simp only [map_smul, smul_sub]
    rw [e]; exact Submodule.smul_mem _ c hX.2⟩

/-- **`λ` on `𝔥`** (Luo §2.1, p. 9): `λ(X) = Σ_{i=0}^{r-1} q(z_{-i-1}, X z_i)`, the differential
of `λ(n) = Σ_{i=0}^{r-1} q(z_{-i-1}, n z_i)` (it vanishes on `so(W)`, which kills `D ⊕ Z`). -/
def lam (X : L.Amb) : K :=
  ∑ i : Fin L.r, bform L.QV (L.zV (-(i : ℤ) - 1)) (L.sndA X (L.zV (i : ℕ)))

end H

/-! ## Measures and `J^Lie` (Luo §4) -/

namespace JLie

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (L : LuoDatum F)

instance instMeasurableSpaceHbar : MeasurableSpace ↥L.Hbar := borel _

instance instBorelSpaceHbar : BorelSpace ↥L.Hbar := ⟨rfl⟩

instance instMeasurableSpaceLieH : MeasurableSpace ↥L.lieH := borel _

instance instBorelSpaceLieH : BorelSpace ↥L.lieH := ⟨rfl⟩

end JLie

open JLie

section JLieDefs

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (L : LuoDatum F)

/-- `ξ(X) = ψ(λ(X))` on `𝔥(F)` (Luo §2.1: trivial on `so(W)`, `ξ ∘ exp` on `𝔫`). -/
def xi (ψ : NontrivialAddChar F) (X : L.Amb) : ℂ := ψ (L.lam X)

/-- A function on `𝔤(F)`, extended by `0` to `End W × End V` (used only at points of `𝔤`:
`x⁻¹ X x ∈ 𝔤` for `x ∈ Ḡ`, `X ∈ 𝔤`). -/
def extFn (f : ↥L.lie → ℂ) (Y : L.Amb) : ℂ :=
  open Classical in if h : Y ∈ L.lie then f ⟨Y, h⟩ else 0

/-- `x⁻¹ Y x` for `x ∈ Ḡ`. -/
def conjInv (x : ↥L.Gbar) (Y : L.Amb) : L.Amb :=
  (((x⁻¹ : ↥L.Gbar) : L.Ambˣ) : L.Amb) * Y * ((x : L.Ambˣ) : L.Amb)

/-- `μ_𝔥` is a Haar measure on `𝔥(F)` compatible through `exp` with the Haar measure `μ_H` on
`H̄(F)` (BP §1.6: the measure on a group is the one deduced from a Haar measure on its Lie algebra
through the exponential, whose Jacobian is `1` near `0` in the `p`-adic case; `B` is degenerate on
`𝔥`, so an arbitrary Haar measure on `𝔥(F)` is lifted): on a neighbourhood `U` of `0`, every
measurable `S ⊆ U` has the `μ_H`-measure of `{e^X : X ∈ S}`. -/
def IsExpCompatH (μH : Measure ↥L.Hbar) (μ : Measure ↥L.lieH) : Prop :=
  μ.IsAddHaarMeasure ∧
    ∃ U ∈ 𝓝 (0 : ↥L.lieH), ∀ S : Set ↥L.lieH, MeasurableSet S → S ⊆ U →
      μ S = μH {h | ∃ X ∈ S, ((((h : ↥L.Gbar) : L.Ambˣ)) : L.Amb) = expA F (X : L.Amb)}

/-- `K^Lie(f, x) = ∫_{𝔥(F)} f(x⁻¹ X x) ξ(X) dX` (Luo §4). -/
def kernelLie (ψ : NontrivialAddChar F) (μ : Measure ↥L.lieH) (f : ↥L.lie → ℂ) (x : ↥L.Gbar) : ℂ :=
  ∫ X : ↥L.lieH, L.extFn f (L.conjInv x X) * L.xi ψ X ∂μ

/-- **`J^Lie(f) = ∫_{H̄(F)\Ḡ(F)} K^Lie(f, x) dx`** (Luo §4), for a quotient measure `m` on
`H̄(F)\Ḡ(F)` and the measure `μ` on `𝔥(F)` (`K^Lie(f, ·)` is left `H̄(F)`-invariant, so it is
evaluated at the chosen representative of each coset). -/
def distribJLie (ψ : NontrivialAddChar F) (μ : Measure ↥L.lieH)
    (m : Measure (CosetSpace L.Hbar.subtype)) (f : ↥L.lie → ℂ) : ℂ :=
  ∫ q, L.kernelLie ψ μ f (CosetSpace.out L.Hbar.subtype q) ∂m

end JLieDefs

/-! ## Strongly cuspidal functions, `θ_f` and quasi-characters on `𝔤(F)` -/

section Scusp

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- The Lie algebra of the stabilizer of an isotropic flag: `X Z_i ⊆ Z_i` for all `i`. -/
def endFlagStab {U : Type*} [AddCommGroup U] [Module K U] {Q : QuadraticForm K U}
    (Fl : IsotropicFlag Q) : Submodule K (Module.End K U) where
  carrier := {X | ∀ i, ∀ v ∈ Fl.sub i, X v ∈ Fl.sub i}
  add_mem' := fun hX hY i v hv => add_mem (hX i v hv) (hY i v hv)
  zero_mem' := fun _ _ _ => zero_mem _
  smul_mem' := fun c _ hX i v hv => Submodule.smul_mem _ c (hX i v hv)

/-- The nilpotent radical of `endFlagStab`: `X Z_{i+1} ⊆ Z_i` and `X (Z_len^⊥) ⊆ Z_len`. -/
def endFlagUnip {U : Type*} [AddCommGroup U] [Module K U] {Q : QuadraticForm K U}
    (Fl : IsotropicFlag Q) : Submodule K (Module.End K U) where
  carrier := {X | (∀ i : Fin Fl.len, ∀ v ∈ Fl.sub i.succ, X v ∈ Fl.sub i.castSucc) ∧
    ∀ v ∈ (bform Q).orthogonal Fl.top, X v ∈ Fl.top}
  add_mem' := fun hX hY => ⟨fun i v hv => add_mem (hX.1 i v hv) (hY.1 i v hv),
    fun v hv => add_mem (hX.2 v hv) (hY.2 v hv)⟩
  zero_mem' := ⟨fun _ _ _ => zero_mem _, fun _ _ => zero_mem _⟩
  smul_mem' := fun c _ hX => ⟨fun i v hv => Submodule.smul_mem _ c (hX.1 i v hv),
    fun v hv => Submodule.smul_mem _ c (hX.2 v hv)⟩

variable (L : LuoDatum K)

/-- `𝔭 = Lie(P_{F_W} × P_{F_V}) ∩ 𝔤` for a pair of isotropic flags. -/
def liePar (FW : IsotropicFlag L.QW) (FV : IsotropicFlag L.QV) : Submodule K L.Amb :=
  L.lie.toSubmodule ⊓ ((endFlagStab FW).comap L.fstA.toLinearMap ⊓
    (endFlagStab FV).comap L.sndA.toLinearMap)

/-- `𝔲 = Lie(U_P)`, the nilpotent radical of `𝔭`. -/
def lieUnip (FW : IsotropicFlag L.QW) (FV : IsotropicFlag L.QV) : Submodule K L.Amb :=
  L.lie.toSubmodule ⊓ ((endFlagUnip FW).comap L.fstA.toLinearMap ⊓
    (endFlagUnip FV).comap L.sndA.toLinearMap)

theorem lieUnip_le_lie (FW : IsotropicFlag L.QW) (FV : IsotropicFlag L.QV) :
    L.lieUnip FW FV ≤ L.lie.toSubmodule := inf_le_left

/-- The parabolic subgroup `P_{F_W} × P_{F_V}` (the stabilizer in `Ḡ` of both flags) is a
*proper* parabolic subgroup: some element of `Ḡ` does not stabilize the pair.  (Every parabolic
subgroup of `SO(W) × SO(V)` is such a stabilizer.) -/
def IsProperFlagPair (FW : IsotropicFlag L.QW) (FV : IsotropicFlag L.QV) : Prop :=
  ∃ g ∈ L.Gbar, ¬ ((∀ i, (FW.sub i).map (L.fstA (g : L.Amb)) ≤ FW.sub i) ∧
    ∀ i, (FV.sub i).map (L.sndA (g : L.Amb)) ≤ FV.sub i)

end Scusp

section ScuspF

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (L : LuoDatum F)

instance instMeasurableSpaceLieUnip (FW : IsotropicFlag L.QW) (FV : IsotropicFlag L.QV) :
    MeasurableSpace ↥(L.lieUnip FW FV) := borel _

/-- **`S_scusp(𝔤(F))`** (Luo p. 7, following BP §5.1; for `p`-adic `F` these are Waldspurger's
"fonctions très cuspidales", Waldspurger 2010 §6.1): locally constant compactly supported `f`
with `∫_{𝔲(F)} f(X + N) dN = 0` for every proper parabolic subgroup `P = MU` and every
`X ∈ 𝔭(F)` (Waldspurger quantifies over `X ∈ 𝔪(F)`; since `𝔭 = 𝔪 ⊕ 𝔲` and `dN` is invariant,
this is the same condition), for every Haar measure `dN` on `𝔲(F)` (they are proportional), the
integrand being integrable. -/
def IsScusp (f : ↥L.lie → ℂ) : Prop :=
  IsTestFn f ∧ ∀ (FW : IsotropicFlag L.QW) (FV : IsotropicFlag L.QV), L.IsProperFlagPair FW FV →
    ∀ X : ↥L.lie, (X : L.Amb) ∈ L.liePar FW FV →
      ∀ μ : Measure ↥(L.lieUnip FW FV), μ.IsAddHaarMeasure →
        Integrable (fun N : ↥(L.lieUnip FW FV) =>
            f ⟨(X : L.Amb) + N, L.lie.add_mem X.2 (L.lieUnip_le_lie FW FV N.2)⟩) μ ∧
          ∫ N : ↥(L.lieUnip FW FV),
            f ⟨(X : L.Amb) + N, L.lie.add_mem X.2 (L.lieUnip_le_lie FW FV N.2)⟩ ∂μ = 0

/-- The self-dual Haar measure `dX` on `𝔤(F)` for `ψ` and the trace form `B` (BP §1.6). -/
def measLie (ψ : NontrivialAddChar F) : Measure ↥L.lie := selfDualHaar L.lie L.traceForm ψ

/-- The orbital pairing `∫_{Ḡ(F)} ∫_{𝔤(F)} f(x⁻¹ X x) f'(X) dX dx` (BP §5.5:
`∫ K^A_{f,f'}(x, x) dx`, with `A_Ḡ = 1`), for a Haar measure `μG` on `Ḡ(F)`. -/
def orbitalPairing (ψ : NontrivialAddChar F) (μG : Measure ↥L.Gbar) (f f' : ↥L.lie → ℂ) : ℂ :=
  ∫ x : ↥L.Gbar, (∫ X : ↥L.lie, L.extFn f (L.conjInv x X) * f' X ∂L.measLie ψ) ∂μG

/-- **The trace form is nondegenerate on `so(W) ⊕ so(V)`** (for `V` nondegenerate): on each factor
`(X, Y) ↦ tr(XY)` separates skew maps (`exists_mem_skewAdjoint_trace_mul_ne_zero`, rank-one skew
maps `u ∧ w`). -/
theorem restrictForm_lie_traceForm_nondegenerate (hV : IsNondeg L.QV) :
    (restrictForm L.lie L.traceForm).Nondegenerate := by
  have hsymm : ∀ X Y : ↥L.lie, restrictForm L.lie L.traceForm X Y =
      restrictForm L.lie L.traceForm Y X := by
    intro X Y
    simp only [restrictForm, LinearMap.compl₁₂_apply, traceForm, LinearMap.mk₂_apply]
    rw [LinearMap.trace_mul_comm F (L.fstA (X : L.Amb)), LinearMap.trace_mul_comm F (L.sndA (X : L.Amb))]
  have hL : ∀ X : ↥L.lie, (∀ Y : ↥L.lie, restrictForm L.lie L.traceForm X Y = 0) → X = 0 := by
    intro X hX
    have hval : ∀ a b (ha : L.pair a b ∈ L.lie),
        ⅟(2 : F) * (LinearMap.trace F L.W (L.fstA (X : L.Amb) * a) +
          LinearMap.trace F L.V (L.sndA (X : L.Amb) * b)) = 0 := fun a b ha => hX ⟨_, ha⟩
    have h2 : ⅟(2 : F) ≠ 0 := invOf_ne_zero 2
    have e1 : L.fstA (X : L.Amb) = 0 := by
      by_contra hne
      obtain ⟨Y, hY, hYt⟩ := exists_mem_skewAdjoint_trace_mul_ne_zero
        (QuadraticMap.associated_isSymm F L.QW) L.nondeg X.2.1 hne
      have := hval Y 0 ⟨hY, zero_mem (skewAdjointLieSubalgebra (bform L.QV))⟩
      rw [mul_zero, map_zero, add_zero] at this
      exact hYt ((mul_eq_zero.mp this).resolve_left h2)
    have e2 : L.sndA (X : L.Amb) = 0 := by
      by_contra hne
      obtain ⟨Y, hY, hYt⟩ := exists_mem_skewAdjoint_trace_mul_ne_zero
        (QuadraticMap.associated_isSymm F L.QV) hV X.2.2 hne
      have := hval 0 Y ⟨zero_mem (skewAdjointLieSubalgebra (bform L.QW)), hY⟩
      rw [mul_zero, map_zero, zero_add] at this
      exact hYt ((mul_eq_zero.mp this).resolve_left h2)
    exact Subtype.ext (Prod.ext e1 e2)
  exact ⟨hL, fun Y hY => hL Y fun X => by rw [hsymm]; exact hY X⟩

/-- A self-dual measure exists on `so(W) ⊕ so(V)` for the trace form (`V` nondegenerate). -/
theorem exists_isSelfDual_lie (hV : IsNondeg L.QV) (ψ : NontrivialAddChar F) :
    ∃ μ, IsSelfDual μ (restrictForm L.lie L.traceForm) ψ := by
  have := t2Space_of_moduleTopology F L.Amb
  have := IsModuleTopology.toContinuousSMul F L.Amb
  exact exists_isSelfDual_of_isInducing L.lie.incl.toLinearMap IsInducing.subtypeVal
    Subtype.val_injective _ (L.restrictForm_lie_traceForm_nondegenerate hV) ψ

/-- `measLie` is a Haar measure on `so(W) ⊕ so(V)` (not the junk value `0`), for `V`
nondegenerate. -/
theorem isAddHaarMeasure_measLie (hV : IsNondeg L.QV) (ψ : NontrivialAddChar F) :
    (L.measLie ψ).IsAddHaarMeasure :=
  selfDualMeasure_isAddHaar (L.exists_isSelfDual_lie hV ψ)

end ScuspF

/-! ## `Γ^Lie(Ḡ, H̄)` and `m^Lie_geom` (Luo §7.1; Waldspurger 2010 §7.3, §7.9) -/

section Gamma

variable {K : Type*} [Field K] [Invertible (2 : K)] (L : LuoDatum K)

/-- `H''_X = SO(W''_X)_X` for `X ∈ so(W)` (Luo §7.1, (7.1.4)): the `g ∈ SO(W)` commuting with
`X` and acting trivially on `W'_X = ker X`. -/
def torusW (X : Module.End K L.W) : Subgroup (Module.End K L.W)ˣ where
  carrier := {g | g ∈ SOu L.QW ∧ (g : Module.End K L.W) * X = X * g ∧
    ∀ w ∈ LinearMap.ker X, (g : Module.End K L.W) w = w}
  one_mem' := ⟨(SOu L.QW).one_mem, by simp, fun _ _ => rfl⟩
  mul_mem' := fun {a b} ha hb => ⟨(SOu L.QW).mul_mem ha.1 hb.1, by
      rw [Units.val_mul, mul_assoc, hb.2.1, ← mul_assoc, ha.2.1, mul_assoc],
    fun w hw => by rw [Units.val_mul, Module.End.mul_apply, hb.2.2 w hw, ha.2.2 w hw]⟩
  inv_mem' := fun {a} ha => ⟨(SOu L.QW).inv_mem ha.1, by
      calc ((a⁻¹ : (Module.End K L.W)ˣ) : Module.End K L.W) * X =
            ((a⁻¹ : (Module.End K L.W)ˣ) : Module.End K L.W) * (X * a) *
              ((a⁻¹ : (Module.End K L.W)ˣ) : Module.End K L.W) := by simp [mul_assoc]
        _ = ((a⁻¹ : (Module.End K L.W)ˣ) : Module.End K L.W) * ((a : Module.End K L.W) * X) *
              ((a⁻¹ : (Module.End K L.W)ˣ) : Module.End K L.W) := by rw [ha.2.1]
        _ = X * ((a⁻¹ : (Module.End K L.W)ˣ) : Module.End K L.W) := by simp [← mul_assoc],
    fun w hw => by
      have h := ha.2.2 w hw
      calc ((a⁻¹ : (Module.End K L.W)ˣ) : Module.End K L.W) w =
            ((a⁻¹ : (Module.End K L.W)ˣ) : Module.End K L.W) ((a : Module.End K L.W) w) := by
              rw [h]
        _ = w := by rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]⟩

/-- `H''_X` embedded diagonally in `Ḡ`, `g ↦ (g, g ⊕ 1)` (a subgroup of `H̄`). -/
def torusOf (X : Module.End K L.W) : Subgroup L.Ambˣ := (L.torusW X).map L.diagU

/-- The common fixed space `W'_T` in `W` of a subgroup `T` (for `T = H''_X`, `W'_X = ker X`). -/
def fixedOf (T : Subgroup L.Ambˣ) : Submodule K L.W :=
  ⨅ t : ↥T, LinearMap.ker (L.fstA ((t : L.Ambˣ) : L.Amb) - 1)

/-- **`𝔱 = Lie(T)`** for a torus `T = H''_X` of `𝒯`, embedded diagonally in `𝔤`: the
`(Y, Y ⊕ 0)` with `Y ∈ so(W)` commuting with `T` and killing `W'_T`. -/
def lieTorus (T : Subgroup L.Ambˣ) : Submodule K L.Amb where
  carrier := {X | L.sndA X = L.extLie (L.fstA X) ∧
    L.fstA X ∈ skewAdjointLieSubalgebra (bform L.QW) ∧
    (∀ t ∈ T, L.fstA ((t : L.Ambˣ) : L.Amb) * L.fstA X = L.fstA X * L.fstA ((t : L.Ambˣ) : L.Amb)) ∧
    ∀ w ∈ L.fixedOf T, L.fstA X w = 0}
  add_mem' := fun {X Y} hX hY => ⟨by rw [map_add, map_add, map_add, hX.1, hY.1],
    by rw [map_add]; exact add_mem hX.2.1 hY.2.1,
    fun t ht => by rw [map_add, mul_add, add_mul, hX.2.2.1 t ht, hY.2.2.1 t ht],
    fun w hw => by rw [map_add, LinearMap.add_apply, hX.2.2.2 w hw, hY.2.2.2 w hw, add_zero]⟩
  zero_mem' := ⟨by simp, by rw [map_zero]; exact zero_mem _, fun _ _ => by simp,
    fun _ _ => by simp⟩
  smul_mem' := fun c {X} hX => ⟨by rw [map_smul, map_smul, map_smul, hX.1],
    by rw [map_smul]; exact Submodule.smul_mem _ c hX.2.1,
    fun t ht => by rw [map_smul, mul_smul_comm, smul_mul_assoc, hX.2.2.1 t ht],
    fun w hw => by rw [map_smul, LinearMap.smul_apply, hX.2.2.2 w hw, smul_zero]⟩

/-- **`X ∈ 𝔱_♮(F)`** (Luo §7.1, (7.1.5); Waldspurger 2010 §7.9): `X ∈ 𝔱`, `ker X_W = W'_T`, and
`X_W` acts on `W''_T = X_W(W)` with distinct eigenvalues (its characteristic polynomial there is
squarefree; over a field of characteristic `0` this is "distinct eigenvalues", and it makes `X_W`
regular in `so(W''_T)`). -/
def IsNat (T : Subgroup L.Ambˣ) (X : L.Amb) : Prop :=
  X ∈ L.lieTorus T ∧ LinearMap.ker (L.fstA X) = L.fixedOf T ∧
    Squarefree (LinearMap.charpoly ((L.fstA X).restrict (p := LinearMap.range (L.fstA X))
      (q := LinearMap.range (L.fstA X)) (fun v _ => LinearMap.mem_range_self _ v)))

/-- `|W(H̄, T)| = |N_{H̄(F)}(T)/Z_{H̄(F)}(T)|` (Luo §7.1). -/
def weylCardOf (T : Subgroup L.Ambˣ) : ℕ :=
  Nat.card (↥(Subgroup.normalizer ((T.subgroupOf L.HbarU : Subgroup ↥L.HbarU) : Set ↥L.HbarU)) ⧸
    (Subgroup.centralizer ((T.subgroupOf L.HbarU : Subgroup ↥L.HbarU) : Set ↥L.HbarU)).subgroupOf
      (Subgroup.normalizer ((T.subgroupOf L.HbarU : Subgroup ↥L.HbarU) : Set ↥L.HbarU)))

end Gamma

section GammaF

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (L : LuoDatum F)

/-- `Δ(X) = |det(X_W|_{W''_X})|_F` with `W''_X = X_W(W)` (Luo (7.1.7)). -/
def delta (X : L.Amb) : ℝ :=
  absF (LinearMap.det ((L.fstA X).restrict (p := LinearMap.range (L.fstA X))
    (q := LinearMap.range (L.fstA X)) (fun v _ => LinearMap.mem_range_self _ v)))

instance instMeasurableSpaceLieTorus (T : Subgroup L.Ambˣ) :
    MeasurableSpace ↥(L.lieTorus T) := borel _

instance instBorelSpaceLieTorus (T : Subgroup L.Ambˣ) : BorelSpace ↥(L.lieTorus T) := ⟨rfl⟩

/-- `X ∈ so(W)` defines an element of `Γ^Lie(Ḡ, H̄)` (Luo §7.1): `X` is semisimple and
`H''_X = SO(W''_X)_X` is an anisotropic torus.  "Torus": its `F`-points commute (`H''_X` is
connected reductive, so its `F`-points are Zariski dense); "anisotropic": its `F`-points are
compact. -/
def IsGammaElt (X : Module.End F L.W) : Prop :=
  X ∈ skewAdjointLieSubalgebra (bform L.QW) ∧ IsSS F X ∧
    (∀ a ∈ L.torusOf X, ∀ b ∈ L.torusOf X, Commute a b) ∧ CompactSpace ↥(L.torusOf X)

/-- The tori `𝒯` (Luo §7.1): the `H''_X`, `X ∈ Γ^Lie(Ḡ, H̄)`. -/
def GammaTorus : Type _ := {T : Subgroup L.Ambˣ // ∃ X, L.IsGammaElt X ∧ L.torusOf X = T}

/-- `H̄(F)`-conjugacy of tori. -/
def TorusConj (T T' : L.GammaTorus) : Prop :=
  ∃ h ∈ L.HbarU, T'.1 = T.1.map (MulAut.conj h).toMonoidHom

/-- The index set of `Γ^Lie(Ḡ, H̄) = ⊔_{T ∈ 𝒯} 𝔱_♮(F)/W(H̄, T)` (Luo (7.1.5)): the
`H̄(F)`-conjugacy classes of tori in `𝒯`. -/
def GammaClass : Type _ := Quot L.TorusConj

/-- `μ` is the measure `ν(T) dX` on `𝔱(F)` (Luo §7.1: `ν(T)` makes the total mass of `T(F)` equal
to `1` for `ν(T) dt`, and `dt` is deduced from `dX` through `exp`, BP §1.6): an additive Haar
measure compatible through `exp` with the probability Haar measure of the compact group `T(F)`. -/
def IsExpCompatT (T : Subgroup L.Ambˣ) (μ : Measure ↥(L.lieTorus T)) : Prop :=
  letI : MeasurableSpace ↥T := borel _
  haveI : BorelSpace ↥T := ⟨rfl⟩
  μ.IsAddHaarMeasure ∧
    ∃ U ∈ 𝓝 (0 : ↥(L.lieTorus T)), ∀ S : Set ↥(L.lieTorus T), MeasurableSet S → S ⊆ U →
      μ S = probHaar ↥T {t | ∃ X ∈ S, ((t : L.Ambˣ) : L.Amb) = expA F (X : L.Amb)}

/-- The choice of regular nilpotent orbit (Luo §7.1 at `X = 0`; Waldspurger 2010 §7.3, §7.9 at
`X ∈ 𝔱_♮`), as a condition on `Y ∈ 𝔤_X`, with `U = W'_X = ker X_W` and `V'_X = W'_X ⊕ (D ⊕ Z)`:
* if `dim V'_X ≥ 4` is even: `Y_V ∈ O_{ν₀}` on `V'_X`;
* else if `dim W'_X ≥ 4` is even: `Y_W ∈ O_{−ν₀}` on `W'_X`;
* otherwise no condition (the regular nilpotent orbit is unique). -/
def OrbitSpec (U : Submodule F L.W) (Y : L.Amb) : Prop :=
  if Even (finrank F ↥(U.prod (⊤ : Submodule F L.Zs))) ∧
      4 ≤ finrank F ↥(U.prod (⊤ : Submodule F L.Zs)) then
    IsInOrbitNu L.QV (U.prod ⊤) L.nu0 (L.sndA Y)
  else if Even (finrank F ↥U) ∧ 4 ≤ finrank F ↥U then
    IsInOrbitNu L.QW U (-L.nu0) (L.fstA Y)
  else True

open Classical in
/-- The regular nilpotent orbit `O_X ∈ Nil_reg(𝔤_X)` selected by `OrbitSpec`; the zero orbit if
there is none (then `G_X` is not quasi-split, `Nil_reg(𝔤_X) = ∅` and `c_θ(X) = 0`, BP
Prop 4.5.1 2.(i); `germLie` vanishes off `Nil_reg`). -/
def orbitChoice (X : L.Amb) : NilOrbit (lieGrpCentralizer L.Gbar X) (lieCentralizer L.lie X) :=
  if h : ∃ O ∈ NilReg (lieGrpCentralizer L.Gbar X) (lieCentralizer L.lie X),
      ∃ Y ∈ nilOrbitSet O, L.OrbitSpec (LinearMap.ker (L.fstA X)) (Y : L.Amb)
  then h.choose
  else Quotient.mk (nilSetoid _ _) ⟨0, LieSubalgebra.zero_mem _, IsNilpotent.zero⟩

/-- `c_θ(X) = c_{θ, O_X}(X)` (Luo §7.1; Waldspurger 2010 §7.3, §7.9), for the trace form. -/
def cTheta (ψ : NontrivialAddChar F) (θ : ↥L.lie → ℂ) (X : L.Amb) : ℂ :=
  germLie L.Gbar L.lie L.traceForm ψ θ X (L.orbitChoice X)

open Classical in
/-- The integrand `D^G(X)^{1/2} c_θ(X) Δ(X)^{s−1/2}` on `𝔱(F)`, `0` off `𝔱_♮(F)`. -/
def gammaIntegrand (ψ : NontrivialAddChar F) (θ : ↥L.lie → ℂ) (T : Subgroup L.Ambˣ) (s : ℝ)
    (X : L.Amb) : ℂ :=
  if L.IsNat T X then
    (Real.sqrt (weylDiscLie L.lie X) : ℂ) * L.cTheta ψ θ X * ((L.delta X ^ (s - 1 / 2) : ℝ) : ℂ)
  else 0

/-- **`m^Lie_{geom,s}(θ) = ∫_{Γ^Lie(Ḡ,H̄)} D^G(X)^{1/2} c_θ(X) Δ(X)^{s−1/2} dX
= Σ_{T ∈ 𝒯} |W(H̄, T)|⁻¹ ν(T) ∫_{𝔱(F)} …`** (Luo §7.1, (7.1.5), Prop 7.1.2(3)), for a family
`μT` of measures `ν(T) dX` on the `𝔱(F)` (`IsExpCompatT`), evaluated on a representative of
each class. -/
def mGeomLieS (ψ : NontrivialAddChar F) (μT : ∀ T : L.GammaTorus, Measure ↥(L.lieTorus T.1))
    (θ : ↥L.lie → ℂ) (s : ℝ) : ℂ :=
  ∑' c : L.GammaClass, ((L.weylCardOf (Quot.out c).1 : ℂ))⁻¹ *
    ∫ X : ↥(L.lieTorus (Quot.out c).1), L.gammaIntegrand ψ θ (Quot.out c).1 s X ∂μT (Quot.out c)

end GammaF

end LuoDatum

end GSpinGGP
