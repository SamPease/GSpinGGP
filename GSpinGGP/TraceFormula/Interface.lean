/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.ThetaF
import GSpinGGP.GGP.Triple

/-!
# Interface: the shared definitions of the trace-formula decomposition

This file holds the *definitions* used by more than one of the trace-formula files, and
only lemmas that are proved here.  Every sorried statement of the decomposition lives in the file
that proves it (`TraceFormula/MGeom.lean`, `Scusp.lean`, `Spectral.lean`, `Geometric.lean`,
`Lie.lean`); `TraceFormula/Spine.lean` proves the three spine statements from them.

* `GeomAt`, `HYP`: the geometric expansion at `(d, χ)` and the induction hypothesis (HYP) of
  Thesis §7.2 (stated here so that the other files can state results under (HYP)).
* `QC d χ`: quasi-characters `θ` on `G(F)` with `θ(ag) = χ(a)⁻¹ θ(g)` on `G_reg(F)`
  (Thesis §4.1.1, §7.2; BP §4.1).  **Convention**: this is the space
  `QC(G(F), χ⁻¹)` (cf. BP §4.1): it is
  matched with `ScuspTestFn d χ = 𝒞_scusp(A_G(F)\G(F), χ⁻¹)`, so that `θ_f ∈ QC d χ` for
  `f ∈ ScuspTestFn d χ` (`thetaF_mem_QC`, proved), and `θ_P ∈ QC d η.inv` for a virtual
  representation `P` with central character `η` (`vChar_mem_QC`, `MGeom.lean`).
  The quasi-character condition is required for every `ψ` (as in `thetaF_spec`, `bp_thetaF_exists`):
  the notion does not depend on `ψ`, which only normalizes the `ĵ(O,·)`.
  The topology of `QC` (BP §4.4) is not defined here.
* `QCfin d`: the span of all `QC d χ`, the domain on which `m_geom` is shown to be linear
  (finite sums of characters with different central characters occur in Thesis (6.7.2)).
* `IsInvariantClopen d Ω`: `Ω ⊆ G(F)` open, closed, conjugation invariant and `A_G(F)`-stable.
  (Such a set is completely `G(F)`-invariant in the sense of BP §3.1, since the semisimple part of
  `x` lies in the closure of the conjugacy class of `x`.)  These are the sets used to cut a
  quasi-character into a part near `A_G(F)` and a part away from it.
* `VanishesNearOne d θ`: `1 ∉ Supp θ` (Thesis Prop 12.3.1).
* `HasCompactSupportModConjAG d θ`: the support of `θ` on `G_reg(F)` is compact modulo
  conjugation and `A_G(F)` (the space `QC_c` of BP §4.1, in the `χ`-equivariant setting).
* Proved: `ScuspTestFn` is closed under `+`, `•`, `-`; `thetaF_mem_QC`.
-/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-! ## 1. The geometric expansion and the induction hypothesis -/

section Hyp

variable (ψ : NontrivialAddChar F)

/-- **The geometric expansion at `(d, χ)`** (Thesis Thm 7.2.1 = Thm 12.2.1):
`J(f) = m_geom(θ_f)` for every `f ∈ 𝒞_scusp(A_G(F)\G(F), χ⁻¹)`, here in its
`C_c^∞`-modulo-`A_G` form `ScuspTestFn d χ`. -/
def GeomAt (d : GGPData F) (χ : CentralCharOn d) : Prop :=
  ∀ f ∈ ScuspTestFn d χ, distribJ d ψ f = mGeom ψ d (thetaF d f)

/-- **The induction hypothesis (HYP)** (Thesis §7.2, `HYPa`): the
geometric expansion (for every central character) and the multiplicity formula hold for every GGP
triple `d'` with `dim G' < dim G`.  The measure is `dimG = dim GSpin(W) + dim GSpin(V)`,
the thesis's `dim(G)`. -/
def HYP (d : GGPData F) : Prop :=
  ∀ d' : GGPData F, d'.dimG < d.dimG → (∀ χ' : CentralCharOn d', GeomAt ψ d' χ') ∧ MultAt ψ d'

end Hyp

/-! ## 2. The test-function space is a vector space -/

section Scusp

variable (d : GGPData F) (χ : CentralCharOn d)

theorem add_mem_scuspTestFn {f g : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ)
    (hg : g ∈ ScuspTestFn d χ) : f + g ∈ ScuspTestFn d χ := by
  obtain ⟨hf1, hf2, ⟨C₁, hC₁, hs₁⟩, hf4⟩ := hf
  obtain ⟨hg1, hg2, ⟨C₂, hC₂, hs₂⟩, hg4⟩ := hg
  refine ⟨hf1.add hg1, fun a x => ?_, ⟨C₁ ∪ C₂, hC₁.union hC₂, fun x hx => ?_⟩,
    fun FW FV hP p hp => ?_⟩
  · simp only [Pi.add_apply, hf2 a x, hg2 a x, mul_add]
  · rcases Function.support_add f g hx with h | h
    · exact Set.mul_subset_mul_left Set.subset_union_left (hs₁ h)
    · exact Set.mul_subset_mul_left Set.subset_union_right (hs₂ h)
  · obtain ⟨i₁, e₁⟩ := hf4 FW FV hP p hp
    obtain ⟨i₂, e₂⟩ := hg4 FW FV hP p hp
    refine ⟨i₁.add i₂, ?_⟩
    simp only [Pi.add_apply]
    rw [integral_add i₁ i₂, e₁, e₂, add_zero]

theorem smul_mem_scuspTestFn (c : ℂ) {f : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ) :
    c • f ∈ ScuspTestFn d χ := by
  obtain ⟨hf1, hf2, ⟨C, hC, hs⟩, hf4⟩ := hf
  refine ⟨hf1.comp (fun z => c * z), fun a x => ?_, ⟨C, hC, fun x hx => hs ?_⟩,
    fun FW FV hP p hp => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hf2 a x]
    ring
  · exact fun h => hx (by simp [h])
  · obtain ⟨i, e⟩ := hf4 FW FV hP p hp
    refine ⟨i.smul c, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, e, mul_zero]

theorem sub_mem_scuspTestFn {f g : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ)
    (hg : g ∈ ScuspTestFn d χ) : f - g ∈ ScuspTestFn d χ := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ g]
  exact add_mem_scuspTestFn d χ hf (smul_mem_scuspTestFn d χ (-1) hg)

end Scusp

/-! ## 3. Quasi-characters with a central character -/

section QC

variable (d : GGPData F)

/-- **`QC(G(F), χ⁻¹)`** (Thesis §4.1.1, §7.2; BP §4.1, in the `χ`-equivariant setting):
quasi-characters `θ` on `G(F)` (for every `ψ`) with `θ(ag) = χ(a)⁻¹ θ(g)` for
`a ∈ A_G(F)` and `g ∈ G_reg(F)` (values off `G_reg(F)` are irrelevant).  This is the space of
`θ_f`, `f ∈ ScuspTestFn d χ` (`thetaF_mem_QC`), written `QC(G(F), χ⁻¹)`; here the
inversion is built into the definition, exactly as in `IsChiEquivariant` (do not invert twice). -/
def QC (χ : CentralCharOn d) : Submodule ℂ (↥d.G → ℂ) where
  carrier := {θ | (∀ ψ : NontrivialAddChar F, IsQuasiCharacter d.G d.lie d.bilin ψ θ) ∧
    ∀ (a : ↥d.AG) (g : ↥d.G), g ∈ regularSet d.G d.lie →
      θ ((a : ↥d.G) * g) = (((χ.toHom a)⁻¹ : Circle) : ℂ) * θ g}
  zero_mem' := ⟨fun ψ => isQuasiCharacter_zero d ψ, fun _ _ _ => by simp⟩
  add_mem' := fun {θ₁ θ₂} h₁ h₂ =>
    ⟨fun ψ => isQuasiCharacter_add d ψ (h₁.1 ψ) (h₂.1 ψ), fun a g hg => by
      simp only [Pi.add_apply, h₁.2 a g hg, h₂.2 a g hg, mul_add]⟩
  smul_mem' := fun c {θ} h =>
    ⟨fun ψ => isQuasiCharacter_smul d ψ c (h.1 ψ), fun a g hg => by
      simp only [Pi.smul_apply, smul_eq_mul, h.2 a g hg]
      ring⟩

theorem mem_QC {χ : CentralCharOn d} {θ : ↥d.G → ℂ} :
    θ ∈ QC d χ ↔ (∀ ψ : NontrivialAddChar F, IsQuasiCharacter d.G d.lie d.bilin ψ θ) ∧
      ∀ (a : ↥d.AG) (g : ↥d.G), g ∈ regularSet d.G d.lie →
        θ ((a : ↥d.G) * g) = (((χ.toHom a)⁻¹ : Circle) : ℂ) * θ g := Iff.rfl

/-- **`θ_f ∈ QC(G(F), χ⁻¹)`** for `f ∈ 𝒞_scusp(A_G(F)\G(F), χ⁻¹)` (Thesis Prop 4.8.1(ii) in
the `χ`-equivariant setting): from `thetaF_spec` and
`thetaF_mul_AG`.  This is the consistency check of the sign convention of `QC`. -/
theorem thetaF_mem_QC (χ : CentralCharOn d) {f : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d χ) :
    thetaF d f ∈ QC d χ :=
  ⟨(thetaF_spec d χ hf).2, fun a _ hg => thetaF_mul_AG d χ hf a hg⟩

/-- The span of all `QC(G(F), χ⁻¹)`, `χ` running over the characters of `A_G(F)` trivial on
`A_{G,H}(F)`: the domain on which `m_geom` is linear (Thesis Prop 12.1.1(i), extended by
linearity to finite sums with different central characters, as used in Thesis (6.7.2)). -/
def QCfin : Submodule ℂ (↥d.G → ℂ) := ⨆ χ : CentralCharOn d, QC d χ

theorem QC_le_QCfin (χ : CentralCharOn d) : QC d χ ≤ QCfin d :=
  le_iSup (fun χ : CentralCharOn d => QC d χ) χ

theorem mem_QCfin_of_mem_QC {χ : CentralCharOn d} {θ : ↥d.G → ℂ} (h : θ ∈ QC d χ) :
    θ ∈ QCfin d :=
  QC_le_QCfin d χ h

end QC

/-! ## 4. Supports -/

section Support

variable (d : GGPData F)

/-- `Ω ⊆ G(F)` is open, closed, invariant under conjugation and stable under `A_G(F)`.  Such sets
cut quasi-characters (`indicator_mem_QC`, `Scusp.lean`).  Examples: `Set.univ`; `A_G(F)·exp(ω)`
for a `G(F)`-excellent compact open neighbourhood `ω` of `0` in `𝔤(F)` (Thesis §12.4, BP §3.3). -/
def IsInvariantClopen (Ω : Set ↥d.G) : Prop :=
  IsOpen Ω ∧ IsClosed Ω ∧ (∀ x g : ↥d.G, g ∈ Ω → x * g * x⁻¹ ∈ Ω) ∧
    ∀ (a : ↥d.AG) (g : ↥d.G), g ∈ Ω → (a : ↥d.G) * g ∈ Ω

theorem isInvariantClopen_univ : IsInvariantClopen d Set.univ :=
  ⟨isOpen_univ, isClosed_univ, fun _ _ _ => trivial, fun _ _ _ => trivial⟩

/-- **`1 ∉ Supp(θ)`** (Thesis Prop 12.3.1): `θ` vanishes on the regular
elements of a neighbourhood of `1`.  (`Supp θ` is the closure of `{g ∈ G_reg(F) : θ(g) ≠ 0}`; for
`θ ∈ QC d χ` it is `A_G(F)`-stable, so this is also `A_G(F) ∩ Supp θ = ∅`.) -/
def VanishesNearOne (θ : ↥d.G → ℂ) : Prop :=
  ∃ U ∈ 𝓝 (1 : ↥d.G), ∀ g ∈ U, g ∈ regularSet d.G d.lie → θ g = 0

/-- **Compact support modulo conjugation and `A_G(F)`** (BP §4.1, `QC_c`; Thesis §4.1.1, in the
`χ`-equivariant setting): every regular `g` with `θ(g) ≠ 0` is of the form
`a · x c x⁻¹` with `a ∈ A_G(F)`, `x ∈ G(F)` and `c` in a fixed compact set `C`. -/
def HasCompactSupportModConjAG (θ : ↥d.G → ℂ) : Prop :=
  ∃ C : Set ↥d.G, IsCompact C ∧ ∀ g ∈ regularSet d.G d.lie, θ g ≠ 0 →
    ∃ (a : ↥d.AG) (x c : ↥d.G), c ∈ C ∧ g = (a : ↥d.G) * (x * c * x⁻¹)

end Support

end GSpinGGP
