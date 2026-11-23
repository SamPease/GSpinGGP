/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Interface
import GSpinGGP.TraceFormula.MGeom
import GSpinGGP.GGP.Levi
import GSpinGGP.TraceFormula.EllipticRepresentations

/-!
# The spectral side: Thesis Prop 7.4.1(ii) in elliptic form

The two statements below are the interface consumed by
`Spine.lean`, which proves `prop_11_5_1_ii_ell` from them:
`defect(P) = defect(P_f) + defect(P − P_f)`, where `P_f` comes from
`exists_virtual_spectral_ell` and `θ_{P − P_f} = 0` on `G_ell,reg(F)`.

* `exists_virtual_spectral_ell` (Thesis Thm 10.2.1 + Prop 7.4.1(ii), elliptic form): the virtual
  representation `P_f = Σ_{π ∈ 𝒳_ell(G,χ)} D(π) θ̂_f(π) π̄`.
* `defect_eq_zero_of_vChar_eq_zero_ell`: the defect vanishes on virtual representations whose
  character vanishes on `G_ell,reg(F)`, i.e. on `R_ind(G, χ)` (Thesis Prop 7.4.1(i), with
  Arthur's orthogonality and van Dijk's formula).

How the two are proved here:

* **Parabolic induction and `R_ind`** are real definitions in `GGP/Levi.lean` §6–§7
  (`GGPData.parInd`, `GGPData.IsTempIndData`, `GGPData.Rind`, at the level of characters).
* **Thesis Prop 7.4.1(i)** (`defect_eq_zero_of_mem_Rind`, proved): the defect vanishes on `R_ind(G, η)` under
  (HYP), from the statement at a single induced representation, `mult_parInd_eq_mGeom` (Thesis
  Prop 7.4.1(i)), `hc_vMult_eq_mult_parInd`, and the linearity of `m_geom`
  on `QCfin` (`MGeom.lean`; `vMGeom_eq_mGeom_vChar`).  `mult_parInd_eq_mGeom` is proved from (HYP)
  at the Levi datum and three SORRYs: the `G̃`-factor `σ̃` of `σ` (`exists_leviFactor`), Thesis
  Cor 9.5.1(i) (`mult_parInd_eq_mult_leviFactor`) and the `m_geom` identity
  (`mGeom_charG_parInd_eq`), with the Levi embedding of `GGP/Levi.lean` (`exists_isLeviEmbedding`,
  SORRY).
* **The characterization** `R_ind(G, η) = {Π : θ_Π = 0 on G_ell,reg(F)}` (`mem_Rind_iff`, proved
  from van Dijk and Arthur, `TraceFormula/EllipticRepresentations.lean`).
* **The spectral side**: `ellVirtual d η f`, a virtual representation with `θ = θ_f` on the
  elliptic set (BP Prop 5.6.1(ii) + Lemma 5.4.2(i), axiom), and Thesis Thm 10.2.1 + Prop 7.4.1(ii)
  in elliptic form for it (`thm_9_1_1_ell`, SORRY).
* **The elliptic inner product** `ellInner` (Arthur 1993; BP §2.7) is defined in §5 and its
  sesquilinearity is proved; it is not used by the two statements (only vanishing on the elliptic
  set is used, so the unchecked normalization of Arthur's orthogonality relations, the "A93
  constant", plays no role).
-/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
variable (ψ : NontrivialAddChar F) (d : GGPData F)

/-! ## 1. `m_geom` of a virtual representation is `m_geom` of its character -/

/-- `vMGeom(Π) = m_geom(θ_Π)` (Thesis §7.2, "`m_geom(π) = m_geom(θ_π)` for all
`π ∈ R_temp(G,χ)`"): the linear extension of `π ↦ m_geom(θ_π)` agrees with `m_geom` of the
character, by the linearity of `m_geom` on `QCfin` (Thesis Prop 12.1.1(i); `mGeom_add`,
`mGeom_smul`) and `θ_π ∈ QC(G, η⁻¹)` (`charG_mem_QC`). -/
theorem vMGeom_eq_mGeom_vChar {η : CentralCharOn d} (P : VirtualTemp d η) :
    vMGeom ψ d P = mGeom ψ d (vChar d P) := by
  induction P using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, map_zero]
    have := mGeom_smul ψ d 0 (Submodule.zero_mem (QCfin d))
    rw [zero_smul, zero_mul] at this
    exact this.symm
  | add P Q hP hQ =>
    rw [map_add, map_add, hP, hQ, mGeom_add ψ d (mem_QCfin_of_mem_QC d (vChar_mem_QC d P))
      (mem_QCfin_of_mem_QC d (vChar_mem_QC d Q))]
  | single c a =>
    rw [vMGeom_single, vChar_single,
      mGeom_smul ψ d a (mem_QCfin_of_mem_QC d (charG_mem_QC d c.isTempCC_rep))]

/-! ## 2. The defect vanishes on `R_ind(G, η)` (Thesis Prop 7.4.1(i)) -/

/-- **The `G̃`-factor of an irreducible tempered representation of the Levi** (Thesis §9.3
(9.3.4)–(9.3.6): `σ = σ^{GL} ⊠ σ̃`, with `σ̃` tempered).  Let `i_P^G(σ)` be properly induced with
`σ` irreducible tempered on `M = P/U`, and let `ι : G̃(F) → M` be a Levi embedding.  Then some
irreducible tempered `σ̃` of `G̃(F)` embeds isometrically and equivariantly into `σ ∘ ι`.

Ingredients: `M(F) = C × ι(G̃(F))` with `C` a product of general linear groups commuting with
`ι(G̃(F))` (the Levi subgroups of `GSpin`: M. Asgari, *Local L-functions for split spinor
groups*, Canad. J. Math. 54 (2002), 673–693, §2); an irreducible unitary
representation of a direct product of two type I groups is an exterior tensor product
`σ^{GL} ⊠ σ̃` of irreducible unitary representations (Dixmier, *C\*-algebras*, 13.1.8), so
`σ ∘ ι` is a multiple of `σ̃`; `σ̃` is tempered since `σ` is weakly contained in the regular
representation of `M(F)`.  Status: SORRY. -/
theorem exists_leviFactor {η : CentralCharOn d} {D : d.ParIndData} (hD : d.IsTempIndData η D)
    {d' : GGPData F} {ι : ↥d'.G →* d.LeviQuot D.FW D.FV}
    (hι : d.IsLeviEmbedding D.FW D.FV d' ι) :
    ∃ σ' : UnitaryRep ↥d'.G, IsTempered σ' ∧
      ∃ T : σ'.H →ₗᵢ[ℂ] D.σ.H, ∀ g v, T (σ'.ρ g v) = D.σ.ρ (ι g) (T v) := by
  sorry

/-- **Thesis Cor 9.5.1(i)**: `m(i_Q^G σ) = m(σ̃)` for `σ` irreducible tempered on the Levi of a
proper parabolic and `σ̃` its `G̃`-factor (`IsLeviFactor`), the multiplicity of `σ̃` being taken for
the GGP triple `(G̃, H̃, ξ̃)` of the Levi pair.

Proof (thesis, own: the unitary-group argument of BP Ch. 7 redone for `GSpin`):
`m(π) ≠ 0 ⇔ 𝓛_π ≠ 0` (Thesis Thm 9.2.1, for `π` and for `σ̃`), `𝓛_π ≠ 0 ⇔ 𝓛_σ̃ ≠ 0` (Thesis
Prop 9.3.7, by induction in stages and the codimension-one computation),
`m(σ̃) ≤ 1` (`emoryTakeda_mult_le_one`), and `m(π) ≤ 1` (Thesis Lemma 9.2.3(ii): two orthogonal
irreducible subrepresentations with nonzero multiplicity would give `𝓛_π(T₁)𝓛_π(T₂) = 0`).
For special orthogonal groups this is Waldspurger, *Une formule intégrale reliée à la conjecture
locale de Gross–Prasad, 2e partie* (arXiv 0904.0314), §7.7, Lemme.
Differs from the dissertation in one degenerate case: a hyperbolic-plane factor with a one-line
flag is treated as `GL₁ × GSpin(0)` (`W̃ = 0`), where the thesis may keep `W̃ = W`; both give the
same answer.
Status: SORRY. -/
theorem mult_parInd_eq_mult_leviFactor {η : CentralCharOn d} {D : d.ParIndData}
    (hD : d.IsTempIndData η D) {d' : GGPData F} {σ' : UnitaryRep ↥d'.G} (hσ' : IsTempered σ')
    (hf : d.IsLeviFactor D.FW D.FV d' D.σ σ') :
    mult ψ d (d.parInd D) = mult ψ d' σ' := by
  sorry

/-- **`m_geom` of an induced character** (Thesis Prop 7.4.1(i), second step):
`m_geom(θ_{i_Q^G σ}) = m_geom^{G̃}(θ_σ̃)` for `σ` irreducible tempered on the Levi of a proper
parabolic and `σ̃` its `G̃`-factor.

Proof (thesis): `θ_{i_Q^G σ} = i_L^G(θ_σ)` (BP (3.4.3), van Dijk's formula); Thesis Lemma 7.3.1
(for `GSpin`: own; for special orthogonal groups it is Waldspurger, *Une formule intégrale reliée à
la conjecture locale de Gross–Prasad, 2e partie* (arXiv 0904.0314), §7.2, Lemme, p. 118, which Luo,
*A local trace formula for the local Gan–Gross–Prasad conjecture for special orthogonal groups*,
Lemma 7.2.2, cites) gives `m_geom(i_L^G θ_σ) = m_geom^{G̃}(θ_σ̃) ·
c_{θ_{σ^{GL}}, O_1}(1)`; and `c_{θ_{σ^{GL}}, O_1}(1) = 1` by BP Prop 4.8.1(i) for the general linear
factor (Rodier) and Zelevinsky 1980 Thm 9.7 (tempered representations of `GL_n` are generic).
The three steps are stated together because the character `θ_{σ^{GL}}` of the general linear
factor is not separately available here.
Differs from the dissertation in one degenerate case: a hyperbolic-plane factor with a one-line
flag is treated as `GL₁ × GSpin(0)` (`W̃ = 0`), where the thesis may keep `W̃ = W`; both give the
same answer.
Status: SORRY. -/
theorem mGeom_charG_parInd_eq {η : CentralCharOn d} {D : d.ParIndData}
    (hD : d.IsTempIndData η D) {d' : GGPData F} {σ' : UnitaryRep ↥d'.G} (hσ' : IsTempered σ')
    (hf : d.IsLeviFactor D.FW D.FV d' D.σ σ') :
    mGeom ψ d (charG d (d.parInd D)) = mGeom ψ d' (charG d' σ') := by
  sorry

/-- **Thesis Prop 7.4.1(i) at one induced representation**.  Assume (HYP).
For `π = i_Q^G(σ)` with `Q` proper and `σ` tempered with central character `η`,
`m(π) = m_geom(θ_π)`.

Proof (thesis): with `(G̃, H̃, ξ̃)` the GGP triple of the Levi pair (`GGPData.leviSmall`) and `σ̃`
the `G̃`-factor of `σ` (`exists_isLeviEmbedding`, `exists_leviFactor`),
1. `m(i_Q^G σ) = m(σ̃)` (`mult_parInd_eq_mult_leviFactor`, Thesis Cor 9.5.1(i));
2. `m_geom(θ_{i_Q^G σ}) = m_geom^{G̃}(θ_σ̃)` (`mGeom_charG_parInd_eq`: BP (3.4.3), Thesis
   Lemma 7.3.1, BP Prop 4.8.1(i) and Zelevinsky 1980 Thm 9.7);
3. `m(σ̃) = m_geom^{G̃}(θ_σ̃)` by (HYP) at `G̃`, since `dim G̃ < dim G` (`dimG_leviSmall_lt`) and
   `σ̃` is trivial on `A_{G̃,H̃}` (`IsLeviFactor.isTrivialOn_AGH`). -/
theorem mult_parInd_eq_mGeom (h : HYP ψ d) (η : CentralCharOn d) (D : d.ParIndData)
    (hD : d.IsTempIndData η D) :
    ((mult ψ d (d.parInd D)).toNat : ℂ) = mGeom ψ d (charG d (d.parInd D)) := by
  obtain ⟨ι, hι⟩ := d.exists_isLeviEmbedding D.FW D.FV (d.leviSmall_spec D.FW D.FV)
  obtain ⟨σ', hσ', T, hT⟩ := exists_leviFactor d hD hι
  have hf : d.IsLeviFactor D.FW D.FV (d.leviSmall D.FW D.FV) D.σ σ' := ⟨ι, hι, T, hT⟩
  obtain ⟨-, hmult⟩ := (h _ (d.dimG_leviSmall_lt hD.proper)).2 σ' hσ'
    (GGPData.IsLeviFactor.isTrivialOn_AGH d hD hf)
  rw [mult_parInd_eq_mult_leviFactor ψ d hD hσ' hf, hmult, mGeom_charG_parInd_eq ψ d hD hσ' hf]

/-- **The defect vanishes on properly induced virtual representations** (Thesis
Prop 7.4.1(i), extended linearly).  On a generator `Π` with
`θ_Π = θ_{i_Q^G σ}` on `G_reg(F)`: `m(Π) = m(i_Q^G σ)` (`hc_vMult_eq_mult_parInd`),
`m_geom(Π) = m_geom(θ_Π) = m_geom(θ_{i_Q^G σ})` (`vMGeom_eq_mGeom_vChar`,
`mGeom_congr_regularSet`), and the two agree by `mult_parInd_eq_mGeom`. -/
theorem defect_eq_zero_of_mem_Rind (h : HYP ψ d) (η : CentralCharOn d) {P : VirtualTemp d η}
    (hP : P ∈ d.Rind η) : defect ψ d P = 0 := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨D, hD, hPD⟩ := hP
    rw [defect, LinearMap.sub_apply, hc_vMult_eq_mult_parInd ψ d η D hD P hPD,
      vMGeom_eq_mGeom_vChar, mGeom_congr_regularSet ψ d hPD, mult_parInd_eq_mGeom ψ d h η D hD,
      sub_self]
  | zero => exact map_zero _
  | add P Q _ _ hP hQ => rw [map_add, hP, hQ, add_zero]
  | smul a P _ hP => rw [map_smul, hP, smul_zero]

/-! ## 3. `R_ind(G, η)` is the space of virtual representations with vanishing elliptic
character -/

/-- Characters of properly induced virtual representations vanish on `G_ell,reg(F)` (van Dijk,
`vanDijk_charG_parInd_ell`). -/
theorem vChar_eq_zero_of_mem_Rind {η : CentralCharOn d} {P : VirtualTemp d η}
    (hP : P ∈ d.Rind η) : ∀ x ∈ d.ellRegSet, vChar d P x = 0 := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨D, hD, hPD⟩ := hP
    intro x hx
    rw [hPD (d.ellRegSet_subset_regularSet hx), vanDijk_charG_parInd_ell d η D hD x hx]
  | zero => intro x _; simp
  | add P Q _ _ hP hQ => intro x hx; rw [map_add, Pi.add_apply, hP x hx, hQ x hx, add_zero]
  | smul a P _ hP => intro x hx; rw [map_smul, Pi.smul_apply, hP x hx, smul_zero]

/-- **`R_ind(G, η) = {Π ∈ R_temp(G, η) : θ_Π = 0 on G_ell,reg(F)}`** (BP §2.7, (2.7.1); Arthur
1993; van Dijk 1972): "⊆" is van Dijk's formula,
"⊇" Arthur's orthogonality relations. -/
theorem mem_Rind_iff {η : CentralCharOn d} (P : VirtualTemp d η) :
    P ∈ d.Rind η ↔ ∀ x ∈ d.ellRegSet, vChar d P x = 0 :=
  ⟨vChar_eq_zero_of_mem_Rind d, arthur_mem_Rind_of_vChar_ell d η P⟩

/-! ## 4. The spectral side in elliptic form (Thesis Thm 10.2.1, Prop 7.4.1(ii)) -/

open scoped Classical in
/-- **The elliptic part of `θ_f`** as a virtual representation: some `P_f ∈ R_temp(G, η)` with
`θ_{P_f} = θ_f` on `G_ell,reg(F)` (it exists for `f ∈ ScuspTestFn d η⁻¹` by BP Prop 5.6.1(ii) and
Lemma 5.4.2(i), `ellVirtual_spec`; junk value `0` otherwise).  The thesis's
`P_f = Σ_{π ∈ 𝒳_ell(G,χ)} D(π) θ̂_f(π) π̄` is one such choice; any two differ by an element of
`R_ind(G, η)` (`mem_Rind_iff`), on which the defect vanishes (`defect_eq_zero_of_mem_Rind`). -/
def ellVirtual (η : CentralCharOn d) (f : ↥d.G → ℂ) : VirtualTemp d η :=
  if h : ∃ P : VirtualTemp d η, ∀ x ∈ d.ellRegSet, vChar d P x = thetaF d f x then h.choose
  else 0

theorem ellVirtual_spec (η : CentralCharOn d) {f : ↥d.G → ℂ} (hf : f ∈ ScuspTestFn d η.inv) :
    ∀ x ∈ d.ellRegSet, vChar d (ellVirtual d η f) x = thetaF d f x := by
  have h := bp_exists_vChar_eq_thetaF_ell d η hf
  unfold ellVirtual
  split
  · rename_i h'; exact h'.choose_spec
  · rename_i h'; exact absurd h h'

/-- **Thesis Thm 10.2.1 and Prop 7.4.1(ii), elliptic form**.
Assume (HYP).  For `f ∈ ScuspTestFn d η⁻¹`,
`J(f) − m_geom(θ_f) = m(P_f) − m_geom(P_f)` with `P_f = ellVirtual d η f`.

Derivation (thesis): the spectral expansion `J(f) = ∫_{𝒳(G,χ)} D(π) θ̂_f(π) m(π̄) dπ` (Thm 10.2.1,
own: BP §9.2–9.3 in the `χ`-equivariant setting, from Thm 10.1.1, Arthur's local trace formula,
the matricial Paley–Wiener theorem, Thesis Thm 9.2.1, and Cor 9.5.1); split
`𝒳(G,χ) = 𝒳_ind ⊔ 𝒳_ell`; on `𝒳_ind`, `m = m_geom` by Prop 7.4.1(i) (under (HYP));
`J_geom(f) = ∫ D(π) θ̂_f(π) m_geom(π̄) dπ` by BP Prop 5.6.1(ii); this leaves
`Σ_{π ∈ 𝒳_ell} D(π) θ̂_f(π) (m − m_geom)(π̄) = defect(Σ D(π) θ̂_f(π) π̄)`.  That virtual
representation has the same elliptic character as `ellVirtual d η f`, so the two defects agree
(`mem_Rind_iff`, `defect_eq_zero_of_mem_Rind`).  Weighted characters `θ̂_f` and the Plancherel
measure on `𝒳(G,χ)` are not formalized, so the statement is made for `ellVirtual`.
Status: SORRY (the analytic heart of the spectral side). -/
theorem thm_9_1_1_ell (h : HYP ψ d) (η : CentralCharOn d) {f : ↥d.G → ℂ}
    (hf : f ∈ ScuspTestFn d η.inv) :
    distribJ d ψ f - mGeom ψ d (thetaF d f) = defect ψ d (ellVirtual d η f) := by
  sorry

/-! ## 5. The elliptic inner product (Arthur, Acta Math. 171 (1993); BP §2.7; Thesis §3.4)

`⟨Θ, Θ'⟩_ell = Σ_{T} |W(G,T)|⁻¹ ∫_{T(F)/A_G(F)} D^G(t) Θ(t) \overline{Θ'(t)} dt`, the sum over the
`G(F)`-conjugacy classes of elliptic maximal tori, `dt` the probability Haar measure on the compact
group `T(F)/A_G(F)`.  Real definition; only conjugate symmetry and homogeneity are proved
(additivity needs integrability and summability, i.e. Harish-Chandra's bounds on characters).  It
is **not used**
by the two interface statements: they only need the vanishing statements of Arthur's theory
(`arthur_mem_Rind_of_vChar_ell`), so the normalization of the orthogonality relations (the "A93
constant") is never relied on.  `𝒳_ell(G, χ)` (Arthur's elliptic representations, built from
`R`-groups) is not defined: `ellVirtual` replaces the thesis's `Σ_{π ∈ 𝒳_ell} D(π) θ̂_f(π) π̄`. -/

/-- The elliptic maximal tori `T_x = Z_G(x)`, `x ∈ G_ell,reg(F)` (connected by Steinberg, since the
derived group `Spin` is simply connected; `T_x(F)/A_G(F)` is compact by ellipticity). -/
def EllTorus : Type _ :=
  {T : Subgroup ↥d.G // ∃ x ∈ d.ellRegSet, T = Subgroup.centralizer {x}}

/-- `G(F)`-conjugacy of elliptic maximal tori. -/
def EllTorus.Conj (T T' : EllTorus d) : Prop :=
  ∃ g : ↥d.G, T'.1 = T.1.map (MulAut.conj g).toMonoidHom

/-- The `G(F)`-conjugacy classes of elliptic maximal tori. -/
def EllTorusClass : Type _ := Quot (EllTorus.Conj (d := d))

/-- `|W(G,T)| = |N_G(T)(F)/T(F)|`, for any subgroup `T` of `G(F)` (used for elliptic tori here and for
all maximal tori in `gammaIntegral`, `TraceFormula/GammaG.lean`). -/
def weylCardG (T : Subgroup ↥d.G) : ℕ :=
  Nat.card (↥(Subgroup.normalizer (T : Set ↥d.G)) ⧸
    T.subgroupOf (Subgroup.normalizer (T : Set ↥d.G)))

theorem AG_le_ellTorus (T : EllTorus d) : d.AG ≤ T.1 := by
  obtain ⟨x, -, hT⟩ := T.2
  rw [hT]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  rintro y rfl
  exact Subgroup.mem_center_iff.mp (d.AG_le_center ha) y

instance normal_AG_subgroupOf (T : Subgroup ↥d.G) : (d.AG.subgroupOf T).Normal :=
  ⟨fun a ha t => by
    have hc : (t : ↥d.G) * (a : ↥d.G) = (a : ↥d.G) * t :=
      Subgroup.mem_center_iff.mp (d.AG_le_center ha) _
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hc,
      mul_inv_cancel_right]
    exact ha⟩

/-- `T(F)/A_G(F)`. -/
abbrev EllTorusQuot (T : Subgroup ↥d.G) : Type _ := ↥T ⧸ d.AG.subgroupOf T

/-- `∫_{T(F)/A_G(F)} D^G(t) Θ(t) \overline{Θ'(t)} dt` for the probability Haar measure (evaluated on
representatives; for `Θ`, `Θ'` with the same unitary central character the integrand is
`A_G(F)`-invariant). -/
def ellTorusIntegral (Θ Θ' : ↥d.G → ℂ) (T : Subgroup ↥d.G) : ℂ :=
  letI : MeasurableSpace (EllTorusQuot d T) := borel _
  haveI : BorelSpace (EllTorusQuot d T) := ⟨rfl⟩
  ∫ q, ((weylDisc d.lie (((Quotient.out q : ↥T) : ↥d.G) : d.ambientˣ) : ℝ) : ℂ) *
      Θ (Quotient.out q : ↥T) * (starRingEnd ℂ) (Θ' (Quotient.out q : ↥T))
    ∂(probHaar (EllTorusQuot d T))

/-- **The elliptic inner product** `⟨Θ, Θ'⟩_ell` (Arthur 1993, §1–§6; BP §2.7; Thesis §3.4). -/
def ellInner (Θ Θ' : ↥d.G → ℂ) : ℂ :=
  ∑' c : EllTorusClass d, ((weylCardG d (Quot.out c).1 : ℂ))⁻¹ *
    ellTorusIntegral d Θ Θ' (Quot.out c).1

theorem ellTorusIntegral_conj (Θ Θ' : ↥d.G → ℂ) (T : Subgroup ↥d.G) :
    (starRingEnd ℂ) (ellTorusIntegral d Θ Θ' T) = ellTorusIntegral d Θ' Θ T := by
  let _ : MeasurableSpace (EllTorusQuot d T) := borel _
  have _ : BorelSpace (EllTorusQuot d T) := ⟨rfl⟩
  unfold ellTorusIntegral
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [map_mul, Complex.conj_ofReal, RCLike.conj_conj]
  ring

theorem ellTorusIntegral_smul_left (c : ℂ) (Θ Θ' : ↥d.G → ℂ) (T : Subgroup ↥d.G) :
    ellTorusIntegral d (c • Θ) Θ' T = c * ellTorusIntegral d Θ Θ' T := by
  let _ : MeasurableSpace (EllTorusQuot d T) := borel _
  have _ : BorelSpace (EllTorusQuot d T) := ⟨rfl⟩
  unfold ellTorusIntegral
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem ellInner_conj_symm (Θ Θ' : ↥d.G → ℂ) :
    (starRingEnd ℂ) (ellInner d Θ Θ') = ellInner d Θ' Θ := by
  unfold ellInner
  rw [Complex.conj_tsum]
  refine tsum_congr fun c => ?_
  rw [map_mul, map_inv₀, Complex.conj_natCast, ellTorusIntegral_conj]

theorem ellInner_smul_left (c : ℂ) (Θ Θ' : ↥d.G → ℂ) :
    ellInner d (c • Θ) Θ' = c * ellInner d Θ Θ' := by
  unfold ellInner
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [ellTorusIntegral_smul_left]
  ring

/-! ## Interface statements -/

/-- **The spectral expansion in elliptic form** (Thesis Thm 10.2.1 and Prop 7.4.1(ii)).
Assume (HYP).  For
`f ∈ ScuspTestFn d η⁻¹` (so `θ_f` transforms by `η`) there is a virtual tempered representation
`P_f` with central character `η` such that `θ_{P_f} = θ_f` on `G_ell,reg(F)` and
`J(f) − m_geom(θ_f) = m(P_f) − m_geom(P_f)`.

Derivation: `P_f = Σ_{π ∈ 𝒳_ell(G,χ)} D(π) θ̂_f(π) π̄`, a finite sum (BP Lemma 5.4.2(i));
`θ_{P_f} = θ_f` on the elliptic set by BP Prop 5.6.1(ii) and van Dijk's formula; the identity is
Thesis Prop 7.4.1(ii), which rests on Thm 10.2.1 and Prop 7.4.1(i).  Status: **proved** from
`bp_exists_vChar_eq_thetaF_ell` (ASSUME) and `thm_9_1_1_ell` (SORRY). -/
theorem exists_virtual_spectral_ell (h : HYP ψ d) (η : CentralCharOn d) {f : ↥d.G → ℂ}
    (hf : f ∈ ScuspTestFn d η.inv) :
    ∃ P : VirtualTemp d η, (∀ x ∈ d.ellRegSet, vChar d P x = thetaF d f x) ∧
      distribJ d ψ f - mGeom ψ d (thetaF d f) = defect ψ d P :=
  ⟨ellVirtual d η f, ellVirtual_spec d η hf, thm_9_1_1_ell ψ d h η hf⟩

/-- **The defect vanishes on `R_ind(G, χ)`, characterized on the elliptic set** (Thesis
Prop 7.4.1(i); Arthur, Acta Math. 171 (1993); BP §2.7, (2.7.1); van Dijk's
formula, BP (3.4.2)/(3.4.3)).  Assume (HYP).  If `θ_P = 0` on `G_ell,reg(F)`, then
`m(P) = m_geom(P)`.

Derivation: `R_ind(G,χ) = {P : θ_P = 0 on G_ell,reg(F)}` ("⊆" van Dijk, "⊇" linear independence
of the elliptic characters, A93), and the defect vanishes on `R_ind(G,χ)` by Thesis Prop 7.4.1(i)
(Thesis Cor 9.5.1, Thesis Lemma 7.3.1 = Luo Lemma 7.2.2 for GSpin, BP (3.4.3),
BP Prop 4.8.1(i), Zelevinsky 1980 Thm 9.7, and (HYP) for the Levi datum).
Status: **proved** from `arthur_mem_Rind_of_vChar_ell` (ASSUME) and
`defect_eq_zero_of_mem_Rind` (proved here from the sorries of §2). -/
theorem defect_eq_zero_of_vChar_eq_zero_ell (h : HYP ψ d) (η : CentralCharOn d)
    (P : VirtualTemp d η) (hP : ∀ x ∈ d.ellRegSet, vChar d P x = 0) : defect ψ d P = 0 :=
  defect_eq_zero_of_mem_Rind ψ d h η (arthur_mem_Rind_of_vChar_ell d η P hP)

end GSpinGGP
