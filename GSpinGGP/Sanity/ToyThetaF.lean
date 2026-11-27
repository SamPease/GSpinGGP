/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.DcQuotientAudit
import GSpinGGP.Sanity.AxiomRedTeam.BPThetaF

/-!
# Sanity check: `θ_f` at the toy datum, from Beuzart-Plessis' formula

At the toy datum `toyD` (`G = GL₁ × GL₁ = A_G`), every reduced Levi datum has `M = G`, every
point is regular and elliptic (`toyD_isMx_all`), and a special `GoodK` exists for every `L`
(`toyD_specialK`).  So `thetaPres` is never `none` at `toyD` (`toyD_thetaPres_isSome`, proved
without `exists_isMx` or `exists_specialK`), and `thetaF` is Beuzart-Plessis' formula at every
point: `θ_f = c f` for **every** `f`, `c = dcScaleAG = haar(A_G(𝒪))` (`toyD_thetaF_eq`, from
`toyD_thetaFBP_eq` and `toyD_dcScaleAG`).  No axiom about `θ_f` is used.

With it, the toy trace formula of `Sanity/Witnesses.lean` §6 closes: `toy_thetaF`, `toy_geomAt`
(the geometric expansion `J(f) = m_geom(θ_f)` at `toyD`), and through the spine `toy_multAt`,
`toy_defect_zero`.
-/

noncomputable section

open MeasureTheory GSpinGGP.GGPData GSpinGGP.AxiomRedTeam

namespace GSpinGGP

namespace Sanity

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝕋" => (toyD (F := F))

/-- **`thetaPres` is never `none` at `toyD`**, without `exists_isMx` or `exists_specialK`. -/
theorem toyD_thetaPres_isSome (x : ↥(𝕋).G) : ((𝕋).thetaPres ((𝕋).centG x)).isSome := by
  have hx : x ∈ regularSet (𝕋).G (𝕋).lie := by rw [toy_regularSet_eq_univ]; trivial
  obtain ⟨L, -⟩ := toyD_thetaFBP (F := F)
  exact thetaPres_isSome ⟨x, hx, rfl, L, toyD_specialK L, toyD_isMx_all L x,
    toyD_specialK_isSpecial L⟩

/-- **`θ_f = c f` on all of `G` at `toyD`, for every `f`**, `c = dcScaleAG`: `thetaF` evaluates
Beuzart-Plessis' formula for the chosen presentation, which is `haar(A_G(𝒪)) · f` for every
presentation (`toyD_thetaFBP_eq`), and `haar(A_G(𝒪)) = dcScaleAG` (`toyD_dcScaleAG`).  So the
formula agrees with the function representing the orbital pairing for `dg / d_c a`
(`toyD_isThetaF`). -/
theorem toyD_thetaF_eq (f : ↥(𝕋).G → ℂ) :
    thetaF (𝕋) f = ((𝕋).dcScaleAG.toReal : ℂ) • f := by
  funext x
  have hx : x ∈ regularSet (𝕋).G (𝕋).lie := by rw [toy_regularSet_eq_univ]; trivial
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (toyD_thetaPres_isSome x)
  rw [thetaF_of_thetaPres hx hp, toyD_thetaFBP_eq, Pi.smul_apply, smul_eq_mul, toyD_dcScaleAG,
    Measure.real]

/-- At `toyD` the formula `thetaF` represents the orbital pairing of every continuous `f`. -/
theorem toyD_isThetaF_thetaF {f : ↥(𝕋).G → ℂ} (hf : Continuous f) :
    IsThetaF (𝕋) f (thetaF (𝕋) f) := by
  rw [toyD_thetaF_eq]; exact toyD_isThetaF hf

/-- **`thetaF = thetaFBP` at `toyD`**: for the Levi datum `M = G` and good compact subgroup of
`toyD_thetaFBP`, `thetaF` is Beuzart-Plessis' formula, for every `f`. -/
theorem toyD_thetaF_eq_thetaFBP :
    ∃ (L : (𝕋).ReducedLeviDatum) (K : (𝕋).GoodK L.toFlagLeviDatum), (∀ x, L.IsMx x) ∧
      ∀ f : ↥(𝕋).G → ℂ, thetaF (𝕋) f = L.thetaFBP K f := by
  obtain ⟨L, K, hMx, -, -, hBP⟩ := toyD_thetaFBP (F := F)
  refine ⟨L, K, hMx, fun f => funext fun x => ?_⟩
  rw [toyD_thetaF_eq, hBP x f, Pi.smul_apply, smul_eq_mul, toyD_dcScaleAG, Measure.real]

section Toy

variable (χ : CentralCharOn (toyD (F := F)))

/-- **`θ_f = c · f` with `c` the mass of the point `G/A_G`** for `measGmodAG = dg / d_c a`, for
`f ∈ 𝒞_scusp`; `c = haar_G(A_G(𝒪))` (`toyD_dcScaleAG`). -/
theorem toyD_thetaF {f : ↥(𝕋).G → ℂ} (_hf : f ∈ ScuspTestFn (𝕋) χ) :
    thetaF (𝕋) f = (((𝕋).measGmodAG.real Set.univ : ℝ) : ℂ) • f := by
  rw [toy_measGmodAG_real_univ]
  exact toyD_thetaF_eq f

/-- **The geometric expansion holds for the toy datum** (Thesis Thm 12.2.1 at `m = r = 0`):
`J(f) = c f(1) = m_geom(θ_f)` for every `f ∈ 𝒞_scusp`, every `χ`, `c = dcScaleAG`.
This checks that `J`, `θ_f` and `m_geom` are normalized consistently *at the zero orbit*:
`dx` on the point `H\G/A_G` and `dg / d_c a` on `G/A_G` both have mass `c`, the probability measure
on `T/A_{G,H}` is the point mass, and `ĵ(0,·) = 1`.  It does not test nonzero orbits.
Uses the literature axiom `exists_isSelfDual` (via `exists_isSelfDual_toyLie`). -/
theorem toyD_geomAt (ψ : NontrivialAddChar F) : GeomAt ψ (𝕋) χ := by
  intro f hf
  rw [toyD_distribJ χ ψ hf.2.1, toyD_thetaF_eq f]
  have h := toyD_mGeom ψ (θ := ((𝕋).dcScaleAG.toReal : ℂ) • f)
    (hf.1.comp fun z => ((𝕋).dcScaleAG.toReal : ℂ) * z)
    (fun t => by simp only [Pi.smul_apply, toyD_apply_diag χ hf.2.1])
  rw [h, Pi.smul_apply, smul_eq_mul]

end Toy

/-- **The geometric expansion for the toy datum** (`GeomAt` for `toyData` itself; see
`toyD_geomAt`). -/
theorem toy_geomAt (ψ : NontrivialAddChar F) (χ' : CentralCharOn (toyData (K := F))) :
    GeomAt ψ toyData χ' :=
  toyD_geomAt χ' ψ

/-- **The multiplicity formula for the toy datum, from the spine** (`multAt_of_hyp_geom`, with
`toy_hyp` and `toy_geomAt`).  Not a direct computation: it goes through the spine `sorry`s
`prop_11_5_1_ii_ell` and `exists_scusp_ell` (and, among others, the axiom
`emoryTakeda_mult_le_one`), so
it checks only that the spine closes at the bottom of the induction, where (HYP) is empty. -/
theorem toyD_multAt (ψ : NontrivialAddChar F) : MultAt ψ (𝕋) :=
  multAt_of_hyp_geom ψ (𝕋) (toyD_hyp ψ) (fun χ' => toyD_geomAt χ' ψ)

/-- `toyD_multAt` for `toyData` itself. -/
theorem toy_multAt (ψ : NontrivialAddChar F) : MultAt ψ (toyData (K := F)) :=
  toyD_multAt ψ

/-- **The defect vanishes on all virtual tempered representations of the toy datum**
(`defect = m − m_geom`, Thesis §7.4), from `toy_multAt` (so with the same dependencies). -/
theorem toy_defect_zero (ψ : NontrivialAddChar F) (η : CentralCharOn (toyData (K := F)))
    (P : VirtualTemp toyData η) : defect ψ toyData P = 0 := by
  induction P using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add P Q hP hQ => rw [map_add, hP, hQ, add_zero]
  | single c a =>
    rw [defect_single, ((toy_multAt ψ) c.rep c.isTempCC_rep.1
      (isTrivialOn_AGH_of_hasCentralChar c.isTempCC_rep.2)).2, sub_self,
      mul_zero]

/-- **`θ_f = c · f`, `c` the mass of the point `G/A_G` for `dg / d_c a`, for the toy datum**
(Thesis §4.8). -/
theorem toy_thetaF (χ' : CentralCharOn (toyData (K := F))) {f : ↥(toyData (K := F)).G → ℂ}
    (hf : f ∈ ScuspTestFn toyData χ') :
    thetaF toyData f =
      (((toyD (F := F)).measGmodAG.real Set.univ : ℝ) : ℂ) • f :=
  toyD_thetaF χ' hf

end Sanity

end GSpinGGP
