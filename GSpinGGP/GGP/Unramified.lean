/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.LeviSubgroup
import GSpinGGP.Foundations.RepresentationTwist

/-!
# Unramified characters of a Levi subgroup, unramified twists and their orbits

For a reduced flag Levi datum `L` with Levi subgroup `M = L.M` of `G = GSpin(W) × GSpin(V)`,
this file builds the objects of Beuzart-Plessis, Astérisque 418, §1.1 (pp. 11–12) and §2.2
(p. 40), and Thesis §2.1 and §3.1.2:

* `a*_M = X^*(M) ⊗ ℝ` and its complexification `a*_{M,ℂ}`, in the coordinates dual to those of
  `a_M = L.aM` (the rational characters `L.char c`), with the pairing `⟨λ, H⟩ = ∑_c λ_c H_c`;
* the unramified character `χ_λ(m) = e^{⟨λ, H_M(m)⟩}` of `M(F)` for `λ ∈ a*_{M,ℂ}`;
* the lattice `𝒜_{M,F} = H_M(M(F))` and its dual `𝒜^∨_{M,F} = Hom(𝒜_{M,F}, 2πℤ)` (BP §1.1),
  and the identification of `i a*_{M,F} = i a*_M / i 𝒜^∨_{M,F}` with a group of unitary
  unramified characters (`torusChar_injective`);
* the twist `σ_λ = σ ⊗ χ_λ` of a unitary representation of `M(F)` (BP §2.2: "`π_λ` acts on the
  same space as `π` and `π_λ(g) = e^{λ(H_G(g))} π(g)`"), its stabilizer `i a^∨_{M,σ}` and the
  orbit relation;
* the twist of the inducing datum of `parInd` (`ParIndData.unramTwist`), so that
  `parInd (D.unramTwist L hL λ)` is `i_P^G(σ_λ)`.

Normalization: `L.HM` uses the norm `‖·‖` of `F`, a positive power `|·|_F^s` of the normalized
absolute value, so `L.HM = s · H_M`; hence `unramChar L λ` is the source's `χ_{sλ}` and
`dualLattice` is `s⁻¹` times the source's `𝒜^∨_{M,F}`.  The family of characters is the same.

The dual lattice is `𝒜^∨_{M,F} = Hom(𝒜_{M,F}, 2πℤ)`, the homomorphisms on the lattice
`𝒜_{M,F} = H_M(M(F))`, as printed in BP §1.1.

## Main definitions

* `ReducedLeviDatum.aMDual`, `aMDualC`: `a*_M`, `a*_{M,ℂ}` (coordinates); `dualPair`,
  `dualPairC`: the pairings with `a_M`.
* `ReducedLeviDatum.unramChar λ : M →* ℂˣ`: `χ_λ`, `λ ∈ a*_{M,ℂ}`.
* `ReducedLeviDatum.unitaryUnramChar ν : M →ₜ* Circle`: `χ_{iν}`, `ν ∈ a*_M`.
* `ReducedLeviDatum.rangeHM`: `𝒜_{M,F} = H_M(M(F))`; `dualLattice`: `𝒜^∨_{M,F}`;
  `iaMF`: `a*_M / 𝒜^∨_{M,F}`; `torusChar : iaMF →+ Additive (M →ₜ* Circle)`.
* `ReducedLeviDatum.unramTwist σ ν`: `σ_{iν}`; `twistStab σ`: its stabilizer;
  `unramOrbitSetoid`: `σ ∼ σ'` iff `σ' ≅ σ_{iν}` for some `ν`.
* `ReducedLeviDatum.charQuot hL ν`: `χ_{iν}` on the Levi quotient `P/U`;
  `GGPData.ParIndData.unramTwist`: the inducing datum `(P, K, σ_{iν})`.

## Main results

* `continuous_unramChar`: `χ_λ` is a continuous character.
* `norm_unramChar_eq_one_iff`: `χ_λ` is unitary iff `Re λ` vanishes on `𝒜_{M,F}`;
  `norm_unramChar_eq_one_of_re_eq_zero`: in particular for `λ ∈ i a*_M`.
* `unramChar_eq_unramChar_iff`: `χ_λ = χ_μ` iff `⟨λ − μ, H_M(m)⟩ ∈ 2πiℤ` for all `m`;
  `unitaryUnramChar_eq_iff`: `χ_{iν} = χ_{iν'}` iff `ν − ν' ∈ 𝒜^∨_{M,F}`;
  `ker_unitaryUnramCharHom`, `torusChar_injective`.
* `unramTwist` is unitary by construction; `isIrreducible_unramTwist_iff`;
  `isEquivalent_unramTwist_zero`, `isEquivalent_unramTwist_add`,
  `unramTwist_eq_of_sub_mem` (depends only on `ν` mod `𝒜^∨_{M,F}`),
  `dualLattice_le_twistStab`.
* `ParIndData.mem_smoothSpace_unramTwist_iff`: the smooth vectors of `i_P^G(σ_λ)` are the
  `f` with `f(pg) = δ_P(p)^{1/2} e^{⟨λ, H_M(p)⟩} σ(p) f(g)`.

Not done here: that `𝒜_{M,F}` is a lattice of full rank (so that `i a*_{M,F}` is a compact torus
and the unitarity criterion becomes `Re λ = 0`), and the restriction-to-`K` identification of the
`i_P^G(σ_λ)` (the compact picture).
-/

noncomputable section

open Topology Filter Module
open scoped Real

namespace GSpinGGP

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {d : GGPData F}

namespace ReducedLeviDatum

variable (L : d.ReducedLeviDatum)

/-! ## 1. `a*_M`, `a*_{M,ℂ}` and the pairing -/

/-- **`a*_M = X^*(M) ⊗ ℝ`** (Thesis §2.1; Beuzart-Plessis §1.1), in the basis of rational
characters `L.char c` dual to the coordinates of `a_M` (`L.aM`). -/
abbrev aMDual : Type := L.Coord → ℝ

/-- **`a*_{M,ℂ}`**, the complexification of `a*_M`, in the same coordinates. -/
abbrev aMDualC : Type := L.Coord → ℂ

/-- The pairing `⟨ν, H⟩ = ∑_c ν_c H_c` of `a*_M` with `a_M`. -/
def dualPair (ν : L.aMDual) (H : L.aM) : ℝ := ∑ c, ν c * H c

/-- The pairing `⟨λ, H⟩ = ∑_c λ_c H_c` of `a*_{M,ℂ}` with `a_M`. -/
def dualPairC (μ : L.aMDualC) (H : L.aM) : ℂ := ∑ c, μ c * (H c : ℂ)

theorem dualPair_add_right (ν : L.aMDual) (H H' : L.aM) :
    L.dualPair ν (H + H') = L.dualPair ν H + L.dualPair ν H' := by
  simp [dualPair, mul_add, Finset.sum_add_distrib]

theorem dualPair_add_left (ν ν' : L.aMDual) (H : L.aM) :
    L.dualPair (ν + ν') H = L.dualPair ν H + L.dualPair ν' H := by
  simp [dualPair, add_mul, Finset.sum_add_distrib]

theorem dualPair_neg_left (ν : L.aMDual) (H : L.aM) :
    L.dualPair (-ν) H = -L.dualPair ν H := by
  simp [dualPair, Finset.sum_neg_distrib]

theorem dualPair_sub_left (ν ν' : L.aMDual) (H : L.aM) :
    L.dualPair (ν - ν') H = L.dualPair ν H - L.dualPair ν' H := by
  simp [dualPair, sub_mul, Finset.sum_sub_distrib]

@[simp] theorem dualPair_zero_left (H : L.aM) : L.dualPair 0 H = 0 := by simp [dualPair]

@[simp] theorem dualPair_zero_right (ν : L.aMDual) : L.dualPair ν 0 = 0 := by simp [dualPair]

theorem dualPairC_add_right (μ : L.aMDualC) (H H' : L.aM) :
    L.dualPairC μ (H + H') = L.dualPairC μ H + L.dualPairC μ H' := by
  simp [dualPairC, mul_add, Finset.sum_add_distrib]

theorem dualPairC_sub_left (μ μ' : L.aMDualC) (H : L.aM) :
    L.dualPairC (μ - μ') H = L.dualPairC μ H - L.dualPairC μ' H := by
  simp [dualPairC, sub_mul, Finset.sum_sub_distrib]

@[simp] theorem dualPairC_zero_right (μ : L.aMDualC) : L.dualPairC μ 0 = 0 := by
  simp [dualPairC]

/-- `Re ⟨λ, H⟩ = ⟨Re λ, H⟩`. -/
theorem re_dualPairC (μ : L.aMDualC) (H : L.aM) :
    (L.dualPairC μ H).re = L.dualPair (fun c => (μ c).re) H := by
  simp [dualPairC, dualPair, Complex.re_sum]

/-- `⟨iν, H⟩ = i⟨ν, H⟩`. -/
theorem dualPairC_mul_I (ν : L.aMDual) (H : L.aM) :
    L.dualPairC (fun c => (ν c : ℂ) * Complex.I) H = (L.dualPair ν H : ℂ) * Complex.I := by
  simp only [dualPairC, dualPair, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => by ring

/-! ## 2. `H_M` is a continuous homomorphism; `𝒜_{M,F}` -/

/-- **`H_M` is continuous** (each `log ‖χ_c(m)‖` is, `χ_c` being continuous with values in
`F^×`). -/
theorem continuous_HM : Continuous L.HM :=
  continuous_pi fun c =>
    (continuous_norm.comp (L.continuous_char c)).log fun m =>
      norm_ne_zero_iff.2 (L.char c m).ne_zero

theorem HM_inv (m : ↥L.M) : L.HM m⁻¹ = -L.HM m := by
  rw [eq_neg_iff_add_eq_zero, ← HM_mul, inv_mul_cancel, HM_one]

/-- **`𝒜_{M,F} = H_M(M(F))`** (Thesis §2.1; Beuzart-Plessis §1.1, p. 11), a subgroup of `a_M`. -/
def rangeHM : AddSubgroup L.aM where
  carrier := Set.range L.HM
  zero_mem' := ⟨1, L.HM_one⟩
  add_mem' := by
    rintro _ _ ⟨m, rfl⟩ ⟨m', rfl⟩
    exact ⟨m * m', L.HM_mul m m'⟩
  neg_mem' := by
    rintro _ ⟨m, rfl⟩
    exact ⟨m⁻¹, L.HM_inv m⟩

theorem mem_rangeHM {H : L.aM} : H ∈ L.rangeHM ↔ ∃ m, L.HM m = H := Iff.rfl

/-! ## 3. Unramified characters `χ_λ`, `λ ∈ a*_{M,ℂ}` -/

/-- **The unramified character `χ_λ(m) = e^{⟨λ, H_M(m)⟩}`** of `M(F)`, `λ ∈ a*_{M,ℂ}`
(Thesis §2.1, §3.1.2; Beuzart-Plessis §1.1, §2.2). -/
def unramChar (μ : L.aMDualC) : ↥L.M →* ℂˣ where
  toFun m := Units.mk0 (Complex.exp (L.dualPairC μ (L.HM m))) (Complex.exp_ne_zero _)
  map_one' := by ext; simp [HM_one]
  map_mul' m m' := by ext; simp [HM_mul, dualPairC_add_right, Complex.exp_add]

@[simp] theorem coe_unramChar (μ : L.aMDualC) (m : ↥L.M) :
    (L.unramChar μ m : ℂ) = Complex.exp (L.dualPairC μ (L.HM m)) := rfl

/-- **`χ_λ` is continuous.** -/
theorem continuous_unramChar (μ : L.aMDualC) : Continuous fun m => (L.unramChar μ m : ℂ) :=
  Complex.continuous_exp.comp <| continuous_finsetSum _ fun c _ =>
    continuous_const.mul
      (Complex.continuous_ofReal.comp ((continuous_apply c).comp L.continuous_HM))

/-- `|χ_λ(m)| = e^{⟨Re λ, H_M(m)⟩}`. -/
theorem norm_unramChar (μ : L.aMDualC) (m : ↥L.M) :
    ‖(L.unramChar μ m : ℂ)‖ = Real.exp (L.dualPair (fun c => (μ c).re) (L.HM m)) := by
  rw [coe_unramChar, Complex.norm_exp, re_dualPairC]

/-- **`χ_λ` is unitary iff `Re λ` vanishes on `𝒜_{M,F} = H_M(M(F))`.** -/
theorem norm_unramChar_eq_one_iff (μ : L.aMDualC) :
    (∀ m, ‖(L.unramChar μ m : ℂ)‖ = 1) ↔
      ∀ H ∈ L.rangeHM, L.dualPair (fun c => (μ c).re) H = 0 := by
  simp only [norm_unramChar, Real.exp_eq_one_iff, mem_rangeHM]
  exact ⟨fun h _ ⟨m, hm⟩ => hm ▸ h m, fun h m => h _ ⟨m, rfl⟩⟩

/-- **`χ_λ` is unitary for `λ ∈ i a*_M`** (`Re λ = 0`). -/
theorem norm_unramChar_eq_one_of_re_eq_zero {μ : L.aMDualC} (h : ∀ c, (μ c).re = 0)
    (m : ↥L.M) : ‖(L.unramChar μ m : ℂ)‖ = 1 := by
  rw [norm_unramChar]
  simp [h, dualPair]

/-- **Periodicity**: `χ_λ = χ_μ` iff `⟨λ − μ, H_M(m)⟩ ∈ 2πiℤ` for every `m ∈ M(F)`. -/
theorem unramChar_eq_unramChar_iff (μ μ' : L.aMDualC) :
    L.unramChar μ = L.unramChar μ' ↔
      ∀ m, ∃ n : ℤ, L.dualPairC (μ - μ') (L.HM m) = n * (2 * π * Complex.I) := by
  constructor
  · intro h m
    have hm := congrArg (fun χ : ↥L.M →* ℂˣ => (χ m : ℂ)) h
    simp only [coe_unramChar] at hm
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hm
    exact ⟨n, by rw [dualPairC_sub_left, hn]; ring⟩
  · intro h
    ext m
    obtain ⟨n, hn⟩ := h m
    rw [dualPairC_sub_left, sub_eq_iff_eq_add] at hn
    simp only [coe_unramChar]
    exact Complex.exp_eq_exp_iff_exists_int.2 ⟨n, by rw [hn]; ring⟩

/-! ## 4. Unitary unramified characters, `𝒜^∨_{M,F}` and `i a*_{M,F}` -/

/-- **The unitary unramified character `χ_{iν}(m) = e^{i⟨ν, H_M(m)⟩}`**, `ν ∈ a*_M`, as a
continuous homomorphism into the circle (Beuzart-Plessis §1.1: the pairing
`(λ, g) ∈ i a*_{M,F} × M(F) ↦ e^{⟨λ, H_M(g)⟩}`). -/
def unitaryUnramChar (ν : L.aMDual) : ↥L.M →ₜ* Circle where
  toFun m := Circle.exp (L.dualPair ν (L.HM m))
  map_one' := by simp [HM_one]
  map_mul' m m' := by simp [HM_mul, dualPair_add_right, Circle.exp_add]
  continuous_toFun :=
    Circle.exp.continuous.comp <| continuous_finsetSum _ fun c _ =>
      continuous_const.mul ((continuous_apply c).comp L.continuous_HM)

theorem unitaryUnramChar_apply (ν : L.aMDual) (m : ↥L.M) :
    L.unitaryUnramChar ν m = Circle.exp (L.dualPair ν (L.HM m)) := rfl

/-- `χ_{iν}` is the unramified character `χ_λ` of `λ = iν ∈ i a*_M`. -/
theorem coe_unitaryUnramChar (ν : L.aMDual) (m : ↥L.M) :
    ((L.unitaryUnramChar ν m : Circle) : ℂ) =
      (L.unramChar (fun c => (ν c : ℂ) * Complex.I) m : ℂ) := by
  rw [unitaryUnramChar_apply, Circle.coe_exp, coe_unramChar, dualPairC_mul_I]

@[simp] theorem unitaryUnramChar_zero : L.unitaryUnramChar 0 = 1 := by
  ext m; simp [unitaryUnramChar_apply]

theorem unitaryUnramChar_add (ν ν' : L.aMDual) :
    L.unitaryUnramChar (ν + ν') = L.unitaryUnramChar ν * L.unitaryUnramChar ν' := by
  ext m
  simp [unitaryUnramChar_apply, dualPair_add_left, Circle.exp_add]

/-- `ν ↦ χ_{iν}` as an additive homomorphism into the (multiplicative) group of unitary
characters. -/
def unitaryUnramCharHom : L.aMDual →+ Additive (↥L.M →ₜ* Circle) where
  toFun ν := Additive.ofMul (L.unitaryUnramChar ν)
  map_zero' := by simp
  map_add' ν ν' := by rw [unitaryUnramChar_add]; rfl

/-- **The dual lattice `𝒜^∨_{M,F} = Hom(𝒜_{M,F}, 2πℤ)`** (Beuzart-Plessis §1.1, p. 11): the
`ν ∈ a*_M` with `⟨ν, H⟩ ∈ 2πℤ` for every `H ∈ 𝒜_{M,F} = H_M(M(F))`. -/
def dualLattice : AddSubgroup L.aMDual where
  carrier := {ν | ∀ H ∈ L.rangeHM, ∃ n : ℤ, L.dualPair ν H = n * (2 * π)}
  zero_mem' := fun _ _ => ⟨0, by simp⟩
  add_mem' := by
    intro ν ν' hν hν' H hH
    obtain ⟨n, hn⟩ := hν H hH
    obtain ⟨n', hn'⟩ := hν' H hH
    exact ⟨n + n', by rw [dualPair_add_left, hn, hn']; push_cast; ring⟩
  neg_mem' := by
    intro ν hν H hH
    obtain ⟨n, hn⟩ := hν H hH
    exact ⟨-n, by rw [dualPair_neg_left, hn]; push_cast; ring⟩

/-- **`χ_{iν}` is trivial iff `ν ∈ 𝒜^∨_{M,F}`.** -/
theorem unitaryUnramChar_eq_one_iff (ν : L.aMDual) :
    L.unitaryUnramChar ν = 1 ↔ ν ∈ L.dualLattice := by
  constructor
  · intro h H hH
    obtain ⟨m, rfl⟩ := hH
    have := DFunLike.congr_fun h m
    rw [unitaryUnramChar_apply] at this
    exact Circle.exp_eq_one.1 this
  · intro h
    ext m
    obtain ⟨n, hn⟩ := h _ ⟨m, rfl⟩
    rw [unitaryUnramChar_apply, Circle.exp_eq_one.2 ⟨n, hn⟩]
    rfl

/-- **`χ_{iν}` depends only on `ν` modulo `𝒜^∨_{M,F}`**, and determines it. -/
theorem unitaryUnramChar_eq_iff (ν ν' : L.aMDual) :
    L.unitaryUnramChar ν = L.unitaryUnramChar ν' ↔ ν - ν' ∈ L.dualLattice := by
  rw [← unitaryUnramChar_eq_one_iff, sub_eq_add_neg, unitaryUnramChar_add]
  have hneg : L.unitaryUnramChar (-ν') = (L.unitaryUnramChar ν')⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← unitaryUnramChar_add, neg_add_cancel, unitaryUnramChar_zero]
  rw [hneg, mul_inv_eq_one]

theorem ker_unitaryUnramCharHom : L.unitaryUnramCharHom.ker = L.dualLattice := by
  ext ν
  rw [AddMonoidHom.mem_ker, ← unitaryUnramChar_eq_one_iff]
  exact Additive.ofMul.injective.eq_iff' rfl

/-- **`i a*_{M,F} = a*_M / 𝒜^∨_{M,F}`** (Thesis §2.1; Beuzart-Plessis §1.1; written additively
and without the factor `i`). -/
abbrev iaMF : Type := L.aMDual ⧸ L.dualLattice

/-- `i a*_{M,F} → {unitary unramified characters of M(F)}`, `ν ↦ χ_{iν}`. -/
def torusChar : L.iaMF →+ Additive (↥L.M →ₜ* Circle) :=
  QuotientAddGroup.lift L.dualLattice L.unitaryUnramCharHom (L.ker_unitaryUnramCharHom ▸ le_rfl)

theorem torusChar_mk (ν : L.aMDual) :
    L.torusChar (QuotientAddGroup.mk ν) = Additive.ofMul (L.unitaryUnramChar ν) := rfl

/-- **`i a*_{M,F}` is identified with a group of unitary unramified characters of `M(F)`**
(Thesis §2.1; Beuzart-Plessis §1.1): `ν ↦ χ_{iν}` is injective on `a*_M / 𝒜^∨_{M,F}`. -/
theorem torusChar_injective : Function.Injective L.torusChar := by
  intro x y hxy
  induction x using QuotientAddGroup.induction_on
  induction y using QuotientAddGroup.induction_on
  rename_i ν ν'
  rw [torusChar_mk, torusChar_mk, Additive.ofMul.injective.eq_iff, unitaryUnramChar_eq_iff] at hxy
  rw [QuotientAddGroup.eq, ← neg_mem_iff, neg_add, neg_neg, ← sub_eq_add_neg]
  exact hxy

/-! ## 5. Unramified twists `σ_λ`, stabilizers and orbits -/

/-- **The unramified twist `σ_{iν} = σ ⊗ χ_{iν}`** of a unitary representation of `M(F)`, for
`ν ∈ a*_M` (Thesis §3.1.2: "`π_λ` acts on the same space as `π` and
`π_λ(g) = e^{λ(H_G(g))} π(g)`"; Beuzart-Plessis §2.2, p. 40).  It is unitary by construction
(`ContRepresentation.IsUnitary.charTwist`). -/
def unramTwist (σ : UnitaryRep ↥L.M) (ν : L.aMDual) : UnitaryRep ↥L.M :=
  σ.twist (L.unitaryUnramChar ν)

theorem unramTwist_ρ_apply (σ : UnitaryRep ↥L.M) (ν : L.aMDual) (m : ↥L.M) (v : σ.H) :
    (L.unramTwist σ ν).ρ m v = Complex.exp (L.dualPair ν (L.HM m) * Complex.I) • σ.ρ m v := by
  change ((L.unitaryUnramChar ν m : Circle) : ℂ) • σ.ρ m v = _
  rw [unitaryUnramChar_apply, Circle.coe_exp]

theorem isIrreducible_unramTwist_iff (σ : UnitaryRep ↥L.M) (ν : L.aMDual) :
    (L.unramTwist σ ν).IsIrreducible ↔ σ.IsIrreducible :=
  σ.isIrreducible_twist_iff _

theorem isEquivalent_unramTwist_zero (σ : UnitaryRep ↥L.M) : (L.unramTwist σ 0).IsEquivalent σ := by
  rw [unramTwist, unitaryUnramChar_zero]
  exact σ.isEquivalent_twist_one

theorem isEquivalent_unramTwist_add (σ : UnitaryRep ↥L.M) (ν ν' : L.aMDual) :
    (L.unramTwist (L.unramTwist σ ν) ν').IsEquivalent (L.unramTwist σ (ν + ν')) := by
  unfold unramTwist
  rw [unitaryUnramChar_add]
  exact σ.isEquivalent_twist_twist _ _

theorem UnitaryRep.IsEquivalent.unramTwist {σ σ' : UnitaryRep ↥L.M} (h : σ.IsEquivalent σ')
    (ν : L.aMDual) : (L.unramTwist σ ν).IsEquivalent (L.unramTwist σ' ν) :=
  h.twist _

/-- **The twist depends only on `ν` modulo `𝒜^∨_{M,F}`**, i.e. on its class in `i a*_{M,F}`. -/
theorem unramTwist_eq_of_sub_mem (σ : UnitaryRep ↥L.M) {ν ν' : L.aMDual}
    (h : ν - ν' ∈ L.dualLattice) : L.unramTwist σ ν = L.unramTwist σ ν' := by
  rw [unramTwist, unramTwist, (L.unitaryUnramChar_eq_iff ν ν').2 h]

/-- **The stabilizer `i a^∨_{M,σ}`** of `σ` for the action of `i a*_M` by unramified twists
(Thesis §3.1.2; Beuzart-Plessis §2.2, p. 40), up to unitary equivalence. -/
def twistStab (σ : UnitaryRep ↥L.M) : AddSubgroup L.aMDual where
  carrier := {ν | (L.unramTwist σ ν).IsEquivalent σ}
  zero_mem' := L.isEquivalent_unramTwist_zero σ
  add_mem' := by
    intro ν ν' (hν : (L.unramTwist σ ν).IsEquivalent σ) (hν' : (L.unramTwist σ ν').IsEquivalent σ)
    exact (L.isEquivalent_unramTwist_add σ ν ν').symm.trans
      ((UnitaryRep.IsEquivalent.unramTwist L hν ν').trans hν')
  neg_mem' := by
    intro ν (hν : (L.unramTwist σ ν).IsEquivalent σ)
    have h1 := (UnitaryRep.IsEquivalent.unramTwist L hν.symm (-ν)).trans
      (L.isEquivalent_unramTwist_add σ ν (-ν))
    rw [add_neg_cancel] at h1
    exact h1.trans (L.isEquivalent_unramTwist_zero σ)

/-- **`i 𝒜^∨_{M,F} ⊆ i a^∨_{M,σ}`** (Thesis §3.1.2: "we always have
`i𝒜^∨_{G,F} ⊆ i𝒜^∨_{G,π}`"). -/
theorem dualLattice_le_twistStab (σ : UnitaryRep ↥L.M) : L.dualLattice ≤ L.twistStab σ := by
  intro ν hν
  change (L.unramTwist σ ν).IsEquivalent σ
  rw [L.unramTwist_eq_of_sub_mem σ (show ν - 0 ∈ L.dualLattice by rwa [sub_zero])]
  exact L.isEquivalent_unramTwist_zero σ

/-- **The orbits of `i a*_M` acting by unramified twists** (Thesis §3.1.2, §3.4;
Beuzart-Plessis §2.2: `Π₂(G)/i𝒜*_{G,F}`): `σ ∼ σ'` iff `σ'` is unitarily equivalent to some
`σ_{iν}`. -/
def unramOrbitSetoid : Setoid (UnitaryRep ↥L.M) where
  r σ σ' := ∃ ν : L.aMDual, (L.unramTwist σ ν).IsEquivalent σ'
  iseqv := by
    refine ⟨fun σ => ⟨0, L.isEquivalent_unramTwist_zero σ⟩, ?_, ?_⟩
    · rintro σ σ' ⟨ν, h⟩
      refine ⟨-ν, ?_⟩
      have h1 := (UnitaryRep.IsEquivalent.unramTwist L h.symm (-ν)).trans
        (L.isEquivalent_unramTwist_add σ ν (-ν))
      rw [add_neg_cancel] at h1
      exact h1.trans (L.isEquivalent_unramTwist_zero σ)
    · rintro σ σ' σ'' ⟨ν, h⟩ ⟨ν', h'⟩
      exact ⟨ν + ν', (L.isEquivalent_unramTwist_add σ ν ν').symm.trans
        ((UnitaryRep.IsEquivalent.unramTwist L h ν').trans h')⟩

/-! ## 6. Twisting the inducing datum of `parInd` -/

variable {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV}

/-- `proj : P → M` kills the unipotent radical. -/
theorem proj_eq_one_of_mem (hL : d.IsLevi FW FV L.M) {u : ↥(d.whittB FW FV)}
    (hu : (u : ↥d.G) ∈ d.whittU FW FV) : hL.proj u = 1 := by
  have h := hL.proj_mul (1 : ↥L.M) hu
  rwa [show (⟨((1 : ↥L.M) : ↥d.G) * u, _⟩ : ↥(d.whittB FW FV)) = u from
    Subtype.ext (one_mul _)] at h

/-- **`χ_{iν}` on the Levi quotient `P/U`** (the model of `M` used by `parInd`): the descent of
`p ↦ χ_{iν}(proj p)`, continuous since `proj` is (`IsLevi.continuous_proj`). -/
def charQuot (hL : d.IsLevi FW FV L.M) (ν : L.aMDual) : d.LeviQuot FW FV →ₜ* Circle where
  toMonoidHom := QuotientGroup.lift _ ((L.unitaryUnramChar ν : ↥L.M →* Circle).comp hL.proj)
    fun u hu => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, L.proj_eq_one_of_mem hL hu, map_one]
  continuous_toFun :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
      ((L.unitaryUnramChar ν).continuous.comp hL.continuous_proj)

@[simp] theorem charQuot_mk (hL : d.IsLevi FW FV L.M) (ν : L.aMDual) (p : ↥(d.whittB FW FV)) :
    L.charQuot hL ν (QuotientGroup.mk p) = L.unitaryUnramChar ν (hL.proj p) := rfl

/-- On `M`, `charQuot` is `χ_{iν}` transported along `M ≅ P/U` (`IsLevi.leviQuotEquiv`). -/
theorem charQuot_leviQuotEquiv (hL : d.IsLevi FW FV L.M) (ν : L.aMDual) (m : ↥L.M) :
    L.charQuot hL ν (hL.leviQuotEquiv m) = L.unitaryUnramChar ν m := by
  rw [IsLevi.leviQuotEquiv_apply, charQuot_mk]
  congr 1
  have h := hL.proj_mul m (d.whittU FW FV).one_mem
  rwa [show (⟨(m : ↥d.G) * 1, _⟩ : ↥(d.whittB FW FV)) = ⟨(m : ↥d.G), hL.le m.property⟩
    from Subtype.ext (mul_one _)] at h

end ReducedLeviDatum

namespace ParIndData

/-- **The inducing datum of `i_P^G(σ_λ)`**, `λ = iν ∈ i a*_M` (Thesis §3.2, Lemma 3.2.1;
Beuzart-Plessis §2.3: `π_λ = i_P^G(σ_λ)`): the same `P` and `K`, with `σ` on `P/U ≅ M` twisted by
`χ_{iν}`, for a Levi subgroup `M = L.M` of `P`.  `parInd (D.unramTwist L hL ν)` is
`i_P^G(σ_{iν})`. -/
def unramTwist (D : d.ParIndData) (L : d.ReducedLeviDatum) (hL : d.IsLevi D.FW D.FV L.M)
    (ν : L.aMDual) : d.ParIndData :=
  { D with σ := D.σ.twist (L.charQuot hL ν) }

/-- **The smooth vectors of `i_P^G(σ_{iν})`**: the `f` with
`f(pg) = δ_P(p)^{1/2} e^{i⟨ν, H_M(proj p)⟩} σ(pU) f(g)`, right invariant under an open
subgroup. -/
theorem mem_smoothSpace_unramTwist_iff (D : d.ParIndData) (L : d.ReducedLeviDatum)
    (hL : d.IsLevi D.FW D.FV L.M) (ν : L.aMDual) (f : ↥d.G → D.σ.H) :
    f ∈ (D.unramTwist L hL ν).smoothSpace ↔
      (∀ (p : ↥D.P) (g : ↥d.G), f ((p : ↥d.G) * g) =
        ((Real.sqrt (D.toIwasawaPair.delta p) : ℝ) : ℂ) •
          (Complex.exp (L.dualPair ν (L.HM (hL.proj p)) * Complex.I) •
            D.σ.ρ (QuotientGroup.mk p) (f g))) ∧
      ∃ K' : Subgroup ↥d.G, IsOpen (K' : Set ↥d.G) ∧ ∀ g : ↥d.G, ∀ k ∈ K', f (g * k) = f g := by
  rfl

end ParIndData

end GGPData

end GSpinGGP
