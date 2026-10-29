/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Basic
import GSpinGGP.TraceFormula.Interface
import GSpinGGP.TraceFormula.MGeom
import GSpinGGP.TraceFormula.Scusp
import GSpinGGP.TraceFormula.Spectral
import GSpinGGP.TraceFormula.Geometric
import GSpinGGP.TraceFormula.Lie
import GSpinGGP.GGP.Triple
import GSpinGGP.Literature.HarishChandra
import GSpinGGP.Literature.GSpin

/-!
# The spine of the local trace formula: geometric expansion ⇒ multiplicity formula

This file derives the multiplicity
formula `MultiplicityFormula F ψ` (Thesis Thm 7.2.2 = Thm 1.0.2) from three
precisely stated statements of the dissertation's own analytic work, by the strong induction on
`dim G` of Thesis §7.2.

* `GeomAt ψ d χ`: the geometric expansion `J(f) = m_geom(θ_f)` at `(d, χ)` (Thesis Thm 7.2.1 =
  Thm 12.2.1); defined in `TraceFormula/Interface.lean`.
* `HYP ψ d`: the induction hypothesis (HYP) of Thesis §7.2; defined in
  `TraceFormula/Interface.lean`.
* The three analytic statements, the whole analytic content of Thesis Ch. 8–12, are **proved here
  from the interface statements** of the other `TraceFormula/` files:
  - `geomAt_of_hyp` (Thesis Thm 12.2.1 under (HYP)) from `geomAt_near` (`Lie.lean`),
    `geomAt_away` (`Geometric.lean`), `exists_scusp_cut` (`Scusp.lean`), `mGeom_add` and
    `mGeom_congr_regularSet` (`MGeom.lean`);
  - `prop_11_5_1_ii_ell` (Thesis Prop 7.4.1(ii), restricted to the elliptic set) from
    `exists_virtual_spectral_ell` and `defect_eq_zero_of_vChar_eq_zero_ell` (`Spectral.lean`);
  - `exists_scusp_ell` (elliptic isolation, BP Cor 5.7.2(i) in χ-equivariant form) from
    `exists_scusp_ell_bp` (`Scusp.lean`).
* Proved: `centralCharOf` (the central character of a tempered `π` on `A_G(F)`, from Schur),
  `mult_ne_top_of_tempered` (Emory–Takeda), `defect_eq_zero_of_geom`, `multAt_of_hyp_geom`
  (Thesis Prop 7.4.1(iii), direction "Thm 7.2.1 ⇒ Thm 7.2.2"), `geom_mult_all` and
  `multiplicityFormula_of_traceFormula`.

## Convention on central characters

`f ∈ ScuspTestFn d χ` means `f(ag) = χ(a)⁻¹ f(g)` (Thesis §2.3: `𝒞(A_G(F)\G(F), χ⁻¹)`), and then
`θ_f(ag) = χ(a)⁻¹ θ_f(g)`.  So `θ_f` is matched with characters of representations with central
character `χ⁻¹` on `A_G(F)`; in this file a virtual representation `Π` with central character `η`
is matched with `f ∈ ScuspTestFn d η.inv`.  This is the thesis's pairing of `θ_f` with
`θ_{π̄}`, `π ∈ 𝒳(G, χ)` (Thesis Prop 4.8.1(ii)).
-/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (ψ : NontrivialAddChar F)

/-! ## 1. The geometric expansion and the induction hypothesis

`GeomAt` and `HYP` are defined in `TraceFormula/Interface.lean`. -/

/-! ## 2. The three analytic statements (the dissertation's own work)

These are the whole analytic content of Thesis Ch. 8–12.  Each is stated so that it is
a consequence of results of the thesis (plus literature results), and none is stronger than what
the thesis proves.  Each is proved from the interface statements of the other `TraceFormula/`
files; the `sorry`s are there. -/

/-- **Thesis Thm 12.2.1 under (HYP)** (Thesis §7.2).  Assuming (HYP) for `d`, the geometric expansion `J(f) = m_geom(θ_f)` holds at
`d` for every central character `χ`.

Status: **proved from the interface statements**.  Choose the clopen invariant
`Ω ∋ 1` of `geomAt_near`; cut `θ_f = θ_{f₁} + θ_{f − f₁}` with `θ_{f₁} = 1_Ω θ_f` and `f₁`
supported in `Ω` (`exists_scusp_cut`); then `J(f₁) = m_geom(θ_{f₁})` by `geomAt_near`,
`J(f − f₁) = m_geom(θ_{f − f₁})` by `geomAt_away` (`θ_{f−f₁}` vanishes on `Ω ∋ 1`), and `J`, `m_geom`
are additive (`distribJ_add`, `mGeom_add`, `mGeom_congr_regularSet`).  The analytic heart, the
dissertation's own adaptation of BP Ch. 11, lies in those statements; it decomposes as follows:
* Thesis Prop 12.1.1: `m_geom` converges, is continuous and linear on
  quasi-characters, with semisimple descent (ii) and the Lie version (iii); BP Lemma B.1.2.
* Thesis Prop 12.2.3: under (HYP) there is a unique continuous `J_qc` on
  quasi-characters with `J(f) = J_qc(θ_f)` and support in the elliptic set (uses BP Cor 5.7.2(i),
  (ii), BP Prop 4.8.1(ii), BP (2.7.2)).
* Thesis Prop 12.3.1: `J_qc = m_geom` on quasi-characters
  supported away from `1`, by semisimple descent through the centralizer decomposition
  `G_x = G'_x · G''_x` (`GGP/Descent.lean`), (HYP) for the
  triple `(G'_x, H'_x, ξ'_x)` and Arthur's local trace formula for `(G''_x, H''_x, 1)`.
* Thesis Prop 12.4.1: descent to the Lie algebra `𝔤⁰ = so(W) ⊕ so(V)` near `1`.
* Thesis Prop 12.5.1 (BP Prop 11.8.1, 4.6.1): `J_qc^Lie − m_geom^Lie = Σ_O c_O c_{θ,O}(0)`.
* the endgame (Thesis §12.5): all `c_O = 0` (Waldspurger 2010 §11.4–11.6; Luo
  Prop 7.3.7), using the orbit choice `O_x` (`orbitChoice`).
* Thesis Thm 12.2.2: `J^Lie = J^Lie_geom`, from Props 12.4.1, 12.5.1, the endgame and (HYP).
Inputs from the literature: the spectral expansion of `J^Lie` (Thesis Thm 11.6.1; Waldspurger 2010
§9–10; Luo Thm 6.6.1), the endgame facts (BP §3.4, §11.9, Props 4.5.1, 4.6.1; Luo Lemma B.3.1,
Prop 7.3.7; Waldspurger 2010 §11.4–11.6), the descent machinery (BP Prop 5.7.1, Prop 4.4.1(v),
(3.2.5), (3.3.2), (11.1.2), Lemmas 11.1.1–11.1.2, Lemma B.1.2), and the convergence of `J`
(Thesis Thm 10.1.1; `TraceFormula/Analytic.lean`). -/
theorem geomAt_of_hyp (d : GGPData F) (h : HYP ψ d) (χ : CentralCharOn d) : GeomAt ψ d χ := by
  intro f hf
  -- near `A_G(F)` (`Lie.lean`) and away from it (`Geometric.lean`), glued by a clopen cut
  obtain ⟨Ω, hΩ, h1Ω, hnear⟩ := geomAt_near ψ d h χ
  obtain ⟨f₁, hf₁, hsupp, hθ₁⟩ := exists_scusp_cut d χ hf hΩ
  have hf₂ : f - f₁ ∈ ScuspTestFn d χ := sub_mem_scuspTestFn d χ hf hf₁
  have hsum : f₁ + (f - f₁) = f := add_sub_cancel f₁ f
  have hθsum : Set.EqOn (thetaF d f) (thetaF d f₁ + thetaF d (f - f₁))
      (regularSet d.G d.lie) := by
    have e := thetaF_add d χ hf₁ hf₂
    rwa [hsum] at e
  have hvan : VanishesNearOne d (thetaF d (f - f₁)) := by
    refine ⟨Ω, hΩ.1.mem_nhds h1Ω, fun g hg hreg => ?_⟩
    have e₁ := hθsum hreg
    have e₂ := hθ₁ hreg
    simp only [Pi.add_apply, Set.indicator_of_mem hg] at e₁ e₂
    linear_combination -e₁ - e₂
  have hJ := GGPData.distribJ_add d χ ψ f₁ (f - f₁) hf₁ hf₂
  rw [hsum] at hJ
  rw [hJ, hnear f₁ hf₁ hsupp, geomAt_away ψ d h χ hf₂ hvan, mGeom_congr_regularSet ψ d hθsum,
    mGeom_add ψ d (mem_QCfin_of_mem_QC d (thetaF_mem_QC d χ hf₁))
      (mem_QCfin_of_mem_QC d (thetaF_mem_QC d χ hf₂))]

/-- **Thesis Prop 7.4.1(ii), elliptic-restriction form**.  Assume (HYP) for `d`.  Let `f ∈ ScuspTestFn d η⁻¹` (so `θ_f` transforms by `η`)
and let `P` be a virtual tempered representation with central character `η` on `A_G(F)` whose
character agrees with `θ_f` on the elliptic regular set `G_ell,reg(F)`.  Then
`J(f) − m_geom(θ_f) = m(P) − m_geom(P)`, both sides of the defect being extended linearly in `P`
(`defect`).

Why this is the thesis's Prop 7.4.1(ii).  The thesis states
`J(f) − J_geom(f) = Σ_{π ∈ 𝒳_ell(G,χ)} D(π) θ̂_f(π) (m(π̄) − m_geom(π̄))`.  Put
`P_f := Σ_{π ∈ 𝒳_ell} D(π) θ̂_f(π) π̄`, a finite sum (BP Lemma 5.4.2(i)).
1. By BP Prop 5.6.1(ii) (`θ_f = ∫_{𝒳(G)} D(π) θ̂_f(π) θ_π̄ dπ`) and van Dijk's formula (induced
   characters vanish on `G_ell,reg`; BP (3.4.2)/(3.4.3) = Thesis (3.5.3.2)), `θ_{P_f} = θ_f` on
   `G_ell,reg(F)`.
2. **The fact used:** `R_ind(G,χ) = {Π ∈ R_temp(G,χ) : θ_Π = 0 on G_ell,reg(F)}`.  "⊆" is van
   Dijk's formula; "⊇" is the linear independence of the elliptic tempered characters on the
   elliptic set (Arthur, Acta Math. 171 (1993), orthogonality relations; number unverified;
   BP §2.7, (2.7.1)).  Hence any `P` as in the hypothesis differs from `P_f` by an element of
   `R_ind`.
3. The defect vanishes on `R_ind(G,χ)` by Thesis Prop 7.4.1(i) (from Thesis Cor 9.5.1,
   Thesis Lemma 7.3.1 = Luo Lemma 7.2.2 for GSpin, BP (3.4.3), BP Prop 4.8.1(i),
   Zelevinsky 1980 Thm 9.7, and (HYP)).
4. So the right-hand side of Prop 7.4.1(ii) is `defect(P_f) = defect(P)`.
The measure constants in `dπ` cancel because `P_f` and the right-hand side are built from the same
expansion.  Prop 7.4.1(ii) itself rests on the spectral expansion, Thesis Thm 10.2.1, which
is not stated in Lean here (it needs Arthur's weighted characters).

Status: **proved from the interface statements**: steps 1 and 4 are
`exists_virtual_spectral_ell`, steps 2 and 3 are `defect_eq_zero_of_vChar_eq_zero_ell` (both in
`TraceFormula/Spectral.lean`).  `P` is written `Π` in the thesis (the letter `Π` is
reserved in Lean). -/
theorem prop_11_5_1_ii_ell (d : GGPData F) (h : HYP ψ d) (η : CentralCharOn d)
    (f : ↥d.G → ℂ) (hf : f ∈ ScuspTestFn d η.inv) (P : VirtualTemp d η)
    (hP : ∀ x ∈ d.ellRegSet, vChar d P x = thetaF d f x) :
    distribJ d ψ f - mGeom ψ d (thetaF d f) = defect ψ d P := by
  -- `P_f` from the spectral expansion; `P - P_f` has character `0` on `G_ell,reg(F)`
  obtain ⟨Pf, hPf, hJ⟩ := exists_virtual_spectral_ell ψ d h η hf
  have h0 := defect_eq_zero_of_vChar_eq_zero_ell ψ d h η (P - Pf) fun x hx => by
    rw [map_sub, Pi.sub_apply, hP x hx, hPf x hx, sub_self]
  have hsplit : defect ψ d P = defect ψ d Pf + defect ψ d (P - Pf) := by
    rw [← map_add, add_sub_cancel]
  rw [hJ, hsplit, h0, add_zero]

/-- **Elliptic isolation, χ-equivariant, `C_c^∞`** (Thesis Cor 4.8.3(i) = BP Cor
5.7.2(i), in χ-equivariant form).  For every virtual tempered
representation `P` with central character `η` on `A_G(F)` there is a strongly cuspidal
`f ∈ ScuspTestFn d η⁻¹` with `θ_f = θ_P` on the elliptic regular set.

Status: **proved from the interface statements**, by `exists_scusp_ell_bp`
(`TraceFormula/Scusp.lean`: `exists_qc_cutoff_ell`, then `exists_scusp_of_qc_bp`).
Proof sketch (the core is a literature theorem, but its statement does not literally apply, since
`G(F)` has noncompact centre):
* cut `θ_P` off near the elliptic set by an invariant cutoff (BP Lemma 4.2.3), obtaining a
  quasi-character with compact support modulo conjugation on an invariant `Ω ⊇ G_ell` that is
  relatively compact modulo conjugation;
* in the `p`-adic case the map `S_scusp(Ω) → QC_c(Ω)`, `f ↦ θ_f`, is surjective (BP Cor 5.7.2(i),
  stated for compact centre: apply it to `A_G(F)\G(F)` acting on χ-twisted data);
* lift to the χ-equivariant space with `P_χ` (`chiProj`, `isThetaF_chiProj`, `ThetaF.lean`).
This differs from the Thesis, which uses BP Cor 5.7.2(iv) and Schwartz functions: here the test
functions `ScuspTestFn` are compactly supported modulo `A_G(F)`.

"Proper parabolic" is the thesis's notion, `whittB FW FV ≠ ⊤` (`GGPData.IsProperFlagPair`). -/
theorem exists_scusp_ell (d : GGPData F) (η : CentralCharOn d) (P : VirtualTemp d η) :
    ∃ f ∈ ScuspTestFn d η.inv, ∀ x ∈ d.ellRegSet, thetaF d f x = vChar d P x := by
  -- the χ-transfer of BP Cor 5.7.2(i) (axiom `bp_scusp_surj_ell`), via `exists_scusp_of_qc_bp`
  exact exists_scusp_ell_bp d η P

/-! ## 3. The central character of a tempered representation -/

section CentralChar

variable (d : GGPData F)

/-- `π` has *some* central character on `A_G(F)`: Schur's lemma (`schur_central`, Dixmier) for
the centre of `G(F)`, restricted to `A_G(F) ⊆ Z_G(F)` (`AG_le_center`). -/
theorem exists_hasCentralChar_AG (π : UnitaryRep ↥d.G) (hπ : π.IsIrreducible) :
    ∃ c : ↥d.AG → ℂ, HasCentralChar π d.AG c := by
  obtain ⟨χ, hχ⟩ := schur_central π hπ
  exact ⟨fun a => χ ⟨a, d.AG_le_center a.2⟩, fun a => hχ ⟨a, d.AG_le_center a.2⟩⟩

/-- The scalar by which `A_G(F)` acts in an irreducible `π` (chosen; `0` if `π` is reducible). -/
def centralScalar (π : UnitaryRep ↥d.G) : ↥d.AG → ℂ := by
  classical
  exact if hπ : π.IsIrreducible then (exists_hasCentralChar_AG d π hπ).choose else 0

theorem hasCentralChar_centralScalar (π : UnitaryRep ↥d.G) (hπ : π.IsIrreducible) :
    HasCentralChar π d.AG (centralScalar d π) := by
  classical
  unfold centralScalar
  rw [dite_eq_left_of_eq_true (eq_true hπ)]
  exact (exists_hasCentralChar_AG d π hπ).choose_spec

theorem norm_centralScalar (π : UnitaryRep ↥d.G) (hπ : π.IsIrreducible) (a : ↥d.AG) :
    ‖centralScalar d π a‖ = 1 :=
  (hasCentralChar_centralScalar d π hπ).norm_eq_one_of_irreducible hπ a

/-- If `π` is trivial on `A_{G,H}(F)`, its central scalar is `1` there. -/
theorem centralScalar_eq_one_of_mem_AGH (π : UnitaryRep ↥d.G) (hπ : π.IsIrreducible)
    (h1 : IsTrivialOn π (d.AGH : Set ↥d.G)) (a : ↥d.G) (ha : a ∈ d.AGH) :
    centralScalar d π ⟨a, d.AGH_le_AG ha⟩ = 1 := by
  have := hπ.1
  obtain ⟨v, hv⟩ := exists_ne (0 : π.H)
  have hc := hasCentralChar_centralScalar d π hπ ⟨a, d.AGH_le_AG ha⟩
  have h2 : π.ρ a = 1 := h1 a ha
  have h3 : (centralScalar d π ⟨a, d.AGH_le_AG ha⟩ • (1 : π.H →L[ℂ] π.H)) v =
      (1 : π.H →L[ℂ] π.H) v := by
    rw [← hc]; exact congrArg (fun T : π.H →L[ℂ] π.H => T v) h2
  simp at h3
  exact smul_left_injective ℂ hv (h3.trans (one_smul ℂ v).symm)

/-- The central character of an irreducible `π` on `A_G(F)` as a continuous homomorphism to the
unit circle: the scalars of Schur's lemma are unitary, multiplicative and continuous. -/
def centralCharHom (π : UnitaryRep ↥d.G) (hirr : π.IsIrreducible) : ↥d.AG →* Circle where
  toFun a := ⟨centralScalar d π a, by
    simp [Submonoid.unitSphere, norm_centralScalar d π hirr a]⟩
  map_one' := by
    have := hirr.1
    exact Circle.ext ((hasCentralChar_centralScalar d π hirr).map_one)
  map_mul' a b :=
    Circle.ext ((hasCentralChar_centralScalar d π hirr).mul_of_irreducible hirr a b)

@[simp] theorem coe_centralCharHom (π : UnitaryRep ↥d.G) (hirr : π.IsIrreducible) (a : ↥d.AG) :
    ((centralCharHom d π hirr a : Circle) : ℂ) = centralScalar d π a := rfl

theorem continuous_centralCharHom (π : UnitaryRep ↥d.G) (hirr : π.IsIrreducible) :
    Continuous (centralCharHom d π hirr) :=
  Continuous.subtype_mk ((hasCentralChar_centralScalar d π hirr).continuous_of_irreducible hirr) _

open Classical in
/-- **The central character of an irreducible tempered `π`, trivial on `A_{G,H}(F)`, as a
`CentralCharOn d`** (Thesis §3.1.2 and §7.1).  Its values are the
scalars of Schur's lemma (`schur_central`), which are unitary (`π` is unitary), multiplicative and
continuous (strong continuity of `π`); it is trivial on `A_{G,H}(F)` by hypothesis.  (Temperedness
includes irreducibility; without it the construction would fall back to the trivial character.) -/
def centralCharOf (π : UnitaryRep ↥d.G) (hπ : IsTempered π)
    (h1 : IsTrivialOn π (d.AGH : Set ↥d.G)) : CentralCharOn d where
  toHom := centralCharHom d π hπ.1
  continuous := continuous_centralCharHom d π hπ.1
  trivial_AGH a ha := Circle.ext (centralScalar_eq_one_of_mem_AGH d π hπ.1 h1 a ha)

/-- `π` lies in `Temp(G, η)` for `η = centralCharOf π`: it is tempered with central character `η`
on `A_G(F)`. -/
theorem centralCharOf_spec (π : UnitaryRep ↥d.G) (hπ : IsTempered π)
    (h1 : IsTrivialOn π (d.AGH : Set ↥d.G)) :
    IsTempCC d (centralCharOf d π hπ h1) π := by
  refine ⟨hπ, ?_⟩
  have hirr : π.IsIrreducible := hπ.1
  exact hasCentralChar_centralScalar d π hirr

end CentralChar

/-! ## 4. Finiteness of the multiplicity -/

/-- `m(π) ≠ ∞` for tempered `π`: `m(π) ≤ 1` by Emory–Takeda (`emoryTakeda_mult_le_one`;
Thesis Thm 5.5.1). -/
theorem mult_ne_top_of_tempered (d : GGPData F) (π : UnitaryRep ↥d.G) (hπ : IsTempered π) :
    mult ψ d π ≠ ⊤ := by
  have h := emoryTakeda_mult_le_one d ψ π hπ
  intro htop
  unfold mult at htop
  rw [htop] at h
  exact absurd h (by decide)

/-! ## 5. Geometric expansion ⇒ multiplicity formula, and the induction -/

/-- **The defect vanishes** (Thesis Prop 7.4.1(iii), the step "(ii) and Thm 7.2.1 give
`m = m_geom` on `R_temp`").  Under (HYP) and the geometric expansion
at `η⁻¹`, every virtual tempered representation `P` with central character `η` satisfies
`m(P) = m_geom(P)`: choose `f` by elliptic isolation (`exists_scusp_ell`), then
`0 = J(f) − m_geom(θ_f) = defect(P)` (`prop_11_5_1_ii_ell`). -/
theorem defect_eq_zero_of_geom (d : GGPData F) (h : HYP ψ d) (η : CentralCharOn d)
    (hg : GeomAt ψ d η.inv) (P : VirtualTemp d η) : defect ψ d P = 0 := by
  obtain ⟨f, hf, hθ⟩ := exists_scusp_ell d η P
  have hD := prop_11_5_1_ii_ell ψ d h η f hf P (fun x hx => (hθ x hx).symm)
  rw [hg f hf, sub_self] at hD
  exact hD.symm

/-- **Thesis Prop 7.4.1(iii), direction "Thm 7.2.1 ⇒ Thm 7.2.2"**.  Under (HYP), the geometric expansion at `d` (for all central characters) gives
the multiplicity formula at `d`.  For tempered `π` trivial on `A_{G,H}(F)`, let `η` be its central
character on `A_G(F)` (`centralCharOf`, Schur) and `P = [π]`; then `defect(P) = 0`
(`defect_eq_zero_of_geom`), i.e. `m(π_c) = m_geom(θ_{π_c})` for the representative `π_c` of the
class of `π`, which transfers to `π` (`TempClass.mult_rep_mk`, `TempClass.charG_rep_mk`);
`m(π) ≠ ∞` is Emory–Takeda.  This replaces the thesis's use of BP Cor 5.7.2(iv), (2.7.1) and
`m(π) = m(π̄)` (absorbed into `prop_11_5_1_ii_ell` and `exists_scusp_ell`). -/
theorem multAt_of_hyp_geom (d : GGPData F) (h : HYP ψ d) (hg : ∀ χ, GeomAt ψ d χ) :
    MultAt ψ d := by
  intro π hπ h1
  refine ⟨mult_ne_top_of_tempered ψ d π hπ, ?_⟩
  have hcc := centralCharOf_spec d π hπ h1
  have hD := defect_eq_zero_of_geom ψ d h _ (hg _)
    (Finsupp.single (TempClass.mk π hcc) (1 : ℂ))
  have key := (defect_single_one_eq_zero_iff ψ (TempClass.mk π hcc)).1 hD
  rwa [TempClass.mult_rep_mk, TempClass.charG_rep_mk] at key

/-- **The induction** (Thesis §7.2): the geometric
expansion (for every central character) and the multiplicity formula hold for every GGP datum.
Strong induction on `dimG`: (HYP) is the induction hypothesis, `geomAt_of_hyp` gives the geometric
expansion, and `multAt_of_hyp_geom` the multiplicity formula. -/
theorem geom_mult_all : ∀ d : GGPData F, (∀ χ, GeomAt ψ d χ) ∧ MultAt ψ d := by
  intro d
  induction hn : d.dimG using Nat.strong_induction_on generalizing d with
  | _ n ih =>
    have hyp : HYP ψ d := fun d' hd' => ih d'.dimG (hn ▸ hd') d' rfl
    have hg : ∀ χ, GeomAt ψ d χ := fun χ => geomAt_of_hyp ψ d hyp χ
    exact ⟨hg, multAt_of_hyp_geom ψ d hyp hg⟩

/-- **The multiplicity formula from the local trace formula** (Thesis Thm 7.2.2 = Thm 1.0.2):
`m(π) = m_geom(θ_π)` for every GGP datum and every tempered `π`
trivial on `A_{G,H}(F)`. -/
theorem multiplicityFormula_of_traceFormula : MultiplicityFormula F ψ :=
  (multiplicityFormula_iff ψ).2 fun d => (geom_mult_all ψ d).2

end GSpinGGP
