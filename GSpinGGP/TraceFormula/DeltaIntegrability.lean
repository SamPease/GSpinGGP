/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Interface
import GSpinGGP.TraceFormula.TorusDescent
import GSpinGGP.TraceFormula.ExpCompatT
import GSpinGGP.Foundations.ExpDet
import GSpinGGP.Foundations.GSpinExpAd
import GSpinGGP.Foundations.DetIntegrability
import GSpinGGP.TraceFormula.LuoTorusHyps
import GSpinGGP.GGP.TorusCount

/-!
# Integrability of `Δ^{s−1/2}` on the tori of `Γ(G,H)` (Thesis Prop 12.1.1)

`bp_integrable_deltaGGP_rpow`: for `x ∈ Γ(G,H)` and `s > 0`,
`∫_{T_x(F)/A_{G,H}(F)} 1_{T_♮}(t) Δ(t)^{s−1/2} dt < ∞` (Thesis Prop 12.1.1(i), proof of (12.1.2):
"a straightforward application of" BP Astérisque 418, Lemma B.1.2(i)).

**What is not stated, and why.**  BP Lemma B.1.2(i) says: for a torus `T` over `F` and linearly
independent characters `χ_1, …, χ_n ∈ X^*(T)` (over `F̄`), `t ↦ ∏ |χ_i(t) − 1|^{s−1}` is locally
integrable on `T(F)` for `Re s > 0`.  This development has no algebraic tori or character
lattices, and the statement with continuous homomorphisms in place of algebraic characters is
false (on `F^×`, `χ_1(t) = t` and `χ_2(t) = t^a` on `1 + pℤ_p` with `a ∈ ℤ_p` irrational are
ℤ-independent, but `|t − 1|^{2s−2}` is not locally integrable near `1` for `s ≤ 1/2`).  So
B.1.2(i) itself is not stated; BP states it without proof.

**The proof here.**  `T_x(F)/A_{G,H}(F)` is compact and the `exp` chart of `𝔱⁰(F) = Lie(T_x)`
carries an additive Haar measure to its Haar measure (`exists_expA_chart_torusOf`), so by
`integrable_of_chart` it suffices to bound the integrand near every `q₀ = t₀ A_{G,H}(F)` in the
chart `X ↦ t₀ e^X`.  There `Δ(t₀ e^X) = |det(P(t₀) e^{ad X} − 1)|_{W''_x}|_F`, which is comparable
to `|det(ad X|_K)|_F` with `K = W''_x ∩ ker(P(t₀) − 1)` (`exists_absF_det_mul_expA_sub_one`).  The
Lie-algebra statement, `locallyIntegrable_absF_det_adV_rpow` (local integrability of
`|det(ad X|_K)|^a` on `𝔱⁰(F)` for `a > −1/2`), is proved over `F` from a regular element of `𝔱⁰`
and `locallyIntegrable_absF_det_rpow_of_odd_pow` (`Foundations/DetIntegrability.lean`).
Measurability of the integrand comes from `TraceFormula/TorusDescent.lean`.

Consistency check: at `x = 1` the conclusion is also proved directly
(`TraceFormula/MGeom.lean`, `integrable_delta_rpow_torusOf_one`).
-/

open MeasureTheory Topology Filter

noncomputable section

set_option linter.style.haveILetI false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

/-- An endomorphism commuting with `P(x)` preserves `W''_x = im(P(x) − 1)`. -/
theorem mapsTo_movedSub_of_commute {x : ↥(GSpin d.QW)} {M : Module.End F (Fin d.m → F)}
    (h : Commute (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) M) :
    ∀ u ∈ movedSub x, M u ∈ movedSub x :=
  mapsTo_range_sub_one_of_commute h

/-- For `t₀ ∈ T_x`, the elements of `𝔱⁰ = Lie(T_x)` preserve `W''_x ∩ ker(P(t₀) − 1)`. -/
theorem adV_mapsTo_movedSub_inf_ker {x t₀ : ↥(GSpin d.QW)} (ht₀ : t₀ ∈ d.torusOf x)
    (X : ↥(d.lieTorus (d.torusOf x))) :
    ∀ v ∈ movedSub x ⊓ LinearMap.ker ((specP d.QW t₀ : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) - 1),
      adV d.QW (X : CliffordAlgebra d.QW) v ∈
        movedSub x ⊓ LinearMap.ker ((specP d.QW t₀ : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) - 1) := by
  have hxT : x ∈ d.torusOf x := d.self_mem_torusOf x
  have hXg := X.2.1.1
  rintro v ⟨hv1, hv2⟩
  exact ⟨d.mapsTo_movedSub_of_commute (commute_specP_adV d.QW hXg (X.2.2.1 x hxT)) v hv1,
    mapsTo_ker_sub_one_of_commute (commute_specP_adV d.QW hXg (X.2.2.1 t₀ ht₀)) v hv2⟩

/-- **`𝔱⁰ = Lie(T_x)` is the whole skew moved commutant**, membership form: for `x ∈ Γ(G,H)`, an
element `Y ∈ so(W)` whose `ad Y` commutes with `P(x)` and kills `W'_x` lies in `𝔱⁰`.  (`Y` has the
commutant of some `g ∈ T_x` (`exists_mem_torusOf_commute_iff`), and `T_x` is commutative.) -/
theorem mem_lieTorus_of_commute_specP {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    {Y : CliffordAlgebra d.QW} (hY : Y ∈ soSub d.QW)
    (hYP : (specP d.QW x : Module.End F (Fin d.m → F)) * adV d.QW Y =
      adV d.QW Y * (specP d.QW x : Module.End F (Fin d.m → F)))
    (hY0 : ∀ w ∈ fixedSub x, adV d.QW Y w = 0) : Y ∈ d.lieTorus (d.torusOf x) := by
  have hYg : Y ∈ gspin d.QW := hY.1
  have hxY := (commute_iff_adV d.nondeg x hYg).mpr hYP
  have hkill : ∀ v ∈ fixedSub x, ⁅Y, CliffordAlgebra.ι d.QW v⁆ = 0 := fun v hv => by
    rw [Ring.lie_def, ← ι_adV hYg, hY0 v hv, map_zero]
  obtain ⟨g, hgT, hg, -⟩ := exists_mem_torusOf_commute_iff d hYg hxY hkill
  refine ⟨hY, fun t ht => ?_, fun w hw => hY0 w (by rwa [d.commonFixed_torusOf] at hw)⟩
  have htg : Commute ((t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)
      ((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) :=
    congrArg (fun k : ↥(GSpin d.QW) => ((k : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
      (hx.2.1 t ht g hgT).eq
  exact ((hg _).mp htg).eq

section Lift

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- **Lifting skew maps to `𝔱⁰`**: for `x ∈ Γ(G,H)`, every skew endomorphism `S` of `W` commuting
with `P(x)` and vanishing on `W'_x` is `ad Y` for some `Y ∈ 𝔱⁰ = Lie(T_x)`. -/
theorem exists_mem_lieTorus_adV_eq {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    {S : Module.End F (Fin d.m → F)} (hS : ∀ u w, bform d.QW (S u) w = -bform d.QW u (S w))
    (hSP : (specP d.QW x : Module.End F (Fin d.m → F)) * S =
      S * (specP d.QW x : Module.End F (Fin d.m → F)))
    (hS0 : ∀ w ∈ fixedSub x, S w = 0) :
    ∃ Y ∈ d.lieTorus (d.torusOf x), adV d.QW Y = S := by
  have hlie : d.luoOf.pair S 0 ∈ d.luoOf.lie :=
    ⟨(LinearMap.mem_skewAdjointSubmodule _).2 fun u w => by
        have := hS u w
        rw [← map_neg] at this
        exact this,
      (skewAdjointLieSubalgebra (bform d.luoOf.QV)).zero_mem⟩
  obtain ⟨Z, hZ, hZM⟩ := d.exists_toSOLin_eq hlie
  have hadZ : adV d.QW Z.1 = S := congrArg Prod.fst hZM
  exact ⟨Z.1, d.mem_lieTorus_of_commute_specP hx hZ.1 (by rw [hadZ]; exact hSP)
    (fun w hw => by rw [hadZ]; exact hS0 w hw), hadZ⟩

end Lift

/-- For `x ∈ Γ(G,H)`, the maps `ad X`, `X ∈ 𝔱⁰`, commute (`movedPartAbelian_of_isGammaElt`). -/
theorem commute_adV_of_mem_lieTorus {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    {X X' : CliffordAlgebra d.QW} (hX : X ∈ d.lieTorus (d.torusOf x))
    (hX' : X' ∈ d.lieTorus (d.torusOf x)) : Commute (adV d.QW X) (adV d.QW X') := by
  have hcent : ∀ {Y}, Y ∈ d.lieTorus (d.torusOf x) →
      Y ∈ lieCentralizer (gspin d.QW) ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) :=
    fun hY => mem_lieCentralizer.2 ⟨hY.1.1, hY.2.1 x (d.self_mem_torusOf x)⟩
  have hkill : ∀ {Y}, Y ∈ d.lieTorus (d.torusOf x) →
      ∀ v ∈ fixedSub x, ⁅Y, CliffordAlgebra.ι d.QW v⁆ = 0 := fun hY v hv => by
    rw [Ring.lie_def, ← ι_adV hY.1.1, hY.2.2 v (by rw [d.commonFixed_torusOf]; exact hv), map_zero]
  have h := movedPartAbelian_of_isGammaElt d x hx X (hcent hX) X' (hcent hX') (hkill hX) (hkill hX')
  rw [Ring.lie_def] at h
  have h' := congrArg (adV d.QW) h
  rw [adV_commutator hX.1.1 hX'.1.1] at h'
  have h0 : adV d.QW (0 : CliffordAlgebra d.QW) = 0 := by ext; simp
  rw [h0, sub_eq_zero] at h'
  exact h'

/-- A skew endomorphism has skew odd powers. -/
theorem bform_pow_odd_skew {M : Module.End F (Fin d.m → F)}
    (hM : ∀ u w, bform d.QW (M u) w = -bform d.QW u (M w)) (n : ℕ) (u w : Fin d.m → F) :
    bform d.QW ((M ^ n) u) w = (-1) ^ n * bform d.QW u ((M ^ n) w) := by
  induction n generalizing u w with
  | zero => simp
  | succ n ih =>
    have e1 : (M ^ (n + 1)) u = (M ^ n) (M u) := by rw [pow_succ, Module.End.mul_apply]
    have e2 : (M ^ (n + 1)) w = M ((M ^ n) w) := by rw [pow_succ', Module.End.mul_apply]
    rw [e1, e2, ih, hM, pow_succ]
    ring

-- the elaboration of the many restricted endomorphisms of `K` and the transport to `F^n` is slow
set_option maxHeartbeats 800000 in
/-- **The Lie-algebra estimate at `t₀ ∈ T_x`** (BP Astérisque 418, Lemma B.1.2(ii) for linear
forms, combined with the eigencharacter computation of Thesis Prop 12.1.1(i)): for `x ∈ Γ(G,H)`,
`t₀ ∈ T_x` and `a > −1/2`, the function `X ↦ |det(ad X |_{K})|_F^a` on `𝔱⁰(F) = Lie(T_x)`, where
`K = W''_x ∩ ker(P(t₀) − 1)`, is locally integrable for an additive Haar measure.

Over `F̄`, `W''_x` has a basis `e_i, f_i` (`1 ≤ i ≤ n = dim W''_x/2`) on which `𝔱⁰` acts by
`ad X e_i = μ_i(X) e_i`, `ad X f_i = −μ_i(X) f_i` with `μ_1, …, μ_n` linearly independent, and
`K ⊗ F̄` is spanned by the `e_i, f_i` with `λ_i(t₀) = 1`; so `det(ad X|_K) = ∏_{i ∈ I} (−μ_i(X)²)`
and the claim is B.1.2(ii) for the forms `μ_i`, `i ∈ I`, at `s′ = 2a + 1 > 0` (each `μ_i` counted
twice).  The linear independence of the `μ_i` (maximality of `T_x` in `GSpin(W''_x)`) comes from
the commutativity conjunct of `IsGammaElt`, which is essential: for `W''_x` split of dimension `4`
and `P(x)` with eigenvalues `λ, λ, λ⁻¹, λ⁻¹`, the analogous `𝔱⁰` would be `1`-dimensional and the
integrand `|μ|^{4a}`, not locally integrable for `a ∈ (−1/2, −1/4]`.  The bound `a > −1/2` is sharp
(an anisotropic plane gives `|μ|^{2a}`).

Proof here, over `F` without eigencharacters: there is `Z ∈ 𝔱⁰` with `ker (ad Z) = W'_x` whose
commutant commutes with `P(x)` (`exists_regular_movedCent`, lifted to `𝔱⁰` by
`exists_mem_lieTorus_adV_eq`).  Then `Y = ad Z` is semisimple and injective on `K`; its commutant on
`W''_x = im Y` is commutative (`commClause_iff_squarefree`: `𝔱⁰` is abelian), hence so is its
commutant on `K` (`commute_restrict_of_commute`); every `ad X`, `X ∈ 𝔱⁰`, commutes with `Y`; and
the odd powers `Y^{2k+1}` are skew, commute with `P(x)` and kill `W'_x`, so they are `ad` of
elements of `𝔱⁰`.  `locallyIntegrable_absF_det_rpow_of_odd_pow` applies (after transporting `𝔱⁰`
to `F^n`). -/
theorem locallyIntegrable_absF_det_adV_rpow {x t₀ : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    (ht₀ : t₀ ∈ d.torusOf x) {a : ℝ} (ha : -(1 / 2) < a)
    (μ : Measure ↥(d.lieTorus (d.torusOf x))) [μ.IsAddHaarMeasure] :
    LocallyIntegrable (fun X : ↥(d.lieTorus (d.torusOf x)) =>
      absF (LinearMap.det ((adV d.QW (X : CliffordAlgebra d.QW)).restrict
        (d.adV_mapsTo_movedSub_inf_ker ht₀ X))) ^ a) μ := by
  classical
  set K := movedSub x ⊓ LinearMap.ker ((specP d.QW t₀ : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) - 1)
  set Px : Module.End F (Fin d.m → F) := (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F))
  have hxT : x ∈ (d.torusOf x) := d.self_mem_torusOf x
  -- `W = W'_x ⊕ W''_x`
  have hss : Module.End.IsSemisimple (Px - 1) :=
    Module.End.IsSemisimple.sub_of_commute (Commute.one_right _)
      (isSemisimple_specP_of_isSS d.QW x hx.1) Module.End.isSemisimple_id
  have hcompl : IsCompl (movedSub x) (fixedSub x) := (isCompl_ker_range_of_isSemisimple hss).symm
  -- a regular element `Z ∈ 𝔱⁰`, `Y = ad Z`
  obtain ⟨Z₀, hZ₀g, hZ₀x, hkerZ₀, hreg⟩ := d.exists_regular_movedCent hx
  obtain ⟨Z, hZT, hZad⟩ := d.exists_mem_lieTorus_adV_eq hx (S := adV d.QW Z₀) (bform_adV hZ₀g)
    ((commute_iff_adV d.nondeg x hZ₀g).mp hZ₀x)
    (fun w hw => LinearMap.mem_ker.mp (hkerZ₀ ▸ hw))
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = adV d.QW Z := ⟨_, rfl⟩
  have hZg : Z ∈ gspin d.QW := hZT.1.1
  have hkerY : LinearMap.ker Y = fixedSub x := by rw [hYdef, hZad, hkerZ₀]
  have hYss : Module.End.IsSemisimple Y := hYdef ▸ isSemisimple_adV hZg
    (d.isSS_of_commute_of_isGammaElt hx hZg (hZT.2.1 x hxT)
      (fun v hv => hZT.2.2 v (by rw [d.commonFixed_torusOf]; exact hv)))
  have hYskew : ∀ u w, bform d.QW (Y u) w = -bform d.QW u (Y w) := hYdef ▸ bform_adV hZg
  have hY0 : ∀ w ∈ fixedSub x, Y w = 0 := fun w hw =>
    LinearMap.mem_ker.mp (by rw [hkerY]; exact hw)
  have hregY : ∀ s : Module.End F (Fin d.m → F), Commute s Y → Commute s Px := by
    intro s hs; rw [hYdef, hZad] at hs; exact hreg s hs
  -- the odd powers of `Y` are `ad` of elements of `𝔱⁰`
  have hodd : ∀ k : ℕ, ∃ X ∈ d.lieTorus (d.torusOf x), adV d.QW X = Y ^ (2 * k + 1) := by
    intro k
    refine d.exists_mem_lieTorus_adV_eq hx (fun u w => ?_) ?_ fun w hw => ?_
    · rw [d.bform_pow_odd_skew hYskew, pow_succ, pow_mul]; simp
    · exact ((hregY _ ((Commute.refl Y).pow_left _)).eq).symm
    · rw [pow_succ, Module.End.mul_apply, hY0 w hw, map_zero]
  -- `W''_x = range Y`
  have hYmov : ∀ v ∈ movedSub x, Y v ∈ movedSub x :=
    d.mapsTo_movedSub_of_commute ((hregY Y (Commute.refl Y)).symm)
  have hrange : movedSub x = LinearMap.range Y := by
    have hle : LinearMap.range Y ≤ movedSub x := by
      rintro _ ⟨v, rfl⟩
      obtain ⟨m, f', hmf, -⟩ := Submodule.existsUnique_add_of_isCompl hcompl v
      rw [← hmf, map_add, hY0 f' f'.2, add_zero]
      exact hYmov m m.2
    refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
    have h1 := LinearMap.finrank_range_add_finrank_ker Y
    have h2 := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hkerY] at h1
    omega
  -- the family on `K`
  have hKY : ∀ v ∈ K, Y v ∈ K := hYdef ▸ d.adV_mapsTo_movedSub_inf_ker ht₀ ⟨Z, hZT⟩
  let ρ : ↥(d.lieTorus (d.torusOf x)) →ₗ[F] Module.End F K :=
    { toFun := fun X => (adV d.QW (X : CliffordAlgebra d.QW)).restrict
        (d.adV_mapsTo_movedSub_inf_ker ht₀ X)
      map_add' := fun X X' => LinearMap.ext fun u => Subtype.ext (by simp)
      map_smul' := fun c X => LinearMap.ext fun u => Subtype.ext (by simp) }
  set A := Y.restrict hKY
  have hAss : Module.End.IsSemisimple A := hYss.restrict (fun v hv => hKY v hv)
  have hAinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    have h1 : (v : Fin d.m → F) ∈ LinearMap.ker Y := congrArg Subtype.val hv
    rw [hkerY] at h1
    exact (Submodule.mem_bot F).mpr (Subtype.ext
      ((Submodule.mem_bot F).mp (hcompl.disjoint.le_bot ⟨v.2.1, h1⟩)))
  have hAc : ∀ g g' : Module.End F K, Commute A g → Commute A g' → Commute g g' := by
    have hU : ∀ v ∈ LinearMap.range Y, Y v ∈ LinearMap.range Y :=
      fun v _ => LinearMap.mem_range_self _ v
    have hcl : ∀ Y' ∈ soSub d.QW, Y' * Z = Z * Y' →
        (∀ w ∈ commonFixed (d.torusOf x), adV d.QW Y' w = 0) → Y' ∈ d.lieTorus (d.torusOf x) := by
      intro Y' hY' hY'Z hY'0
      have hc : Commute (adV d.QW Y') Y := by
        have h := adV_commutator hY'.1 hZg
        rw [hY'Z, sub_self, ← hYdef] at h
        have h0 : adV d.QW (0 : CliffordAlgebra d.QW) = 0 := by ext; simp
        rw [h0] at h
        exact sub_eq_zero.mp h.symm
      exact d.mem_lieTorus_of_commute_specP hx hY' (hregY _ hc).eq.symm
        (fun w hw => hY'0 w (by rw [d.commonFixed_torusOf]; exact hw))
    have hsq := (d.commClause_iff_squarefree hx hZT
      (by rw [d.commonFixed_torusOf, ← hYdef]; exact hkerY)).mp hcl
    rw [← hYdef] at hsq
    have hUc : ∀ g g' : Module.End F (LinearMap.range Y), Commute (Y.restrict hU) g →
        Commute (Y.restrict hU) g' → Commute g g' := fun g g' hg hg' =>
      commute_of_squarefree_charpoly hsq hg hg'
    exact fun g g' hg hg' => commute_restrict_of_commute hYss hU hKY
      (fun v hv => hrange ▸ hv.1) hUc hg hg'
  have hρA : ∀ X, Commute A (ρ X) := by
    intro X
    have h := d.commute_adV_of_mem_lieTorus hx hZT X.2
    rw [← hYdef] at h
    refine LinearMap.ext fun u => Subtype.ext ?_
    have := LinearMap.congr_fun h.eq (u : Fin d.m → F)
    simpa [ρ, A, Module.End.mul_apply] using this
  have hρodd : ∀ k : ℕ, A ^ (2 * k + 1) ∈ LinearMap.range ρ := by
    intro k
    obtain ⟨X, hX, hXad⟩ := hodd k
    refine ⟨⟨X, hX⟩, LinearMap.ext fun u => Subtype.ext ?_⟩
    change adV d.QW X u = ((A ^ (2 * k + 1)) u : Fin d.m → F)
    rw [hXad, Module.End.pow_restrict, LinearMap.coe_restrict_apply]
  -- transport to `F^n`
  letI := isTopologicalRing_of_moduleTopology F (CliffordAlgebra d.QW)
  haveI := t2Space_of_moduleTopology F (CliffordAlgebra d.QW)
  haveI := submodule_isTopologicalAddGroup (d.lieTorus (d.torusOf x))
  haveI := submodule_isModuleTopology (d.lieTorus (d.torusOf x))
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  obtain ⟨_, _, _, _, _⟩ := submodule_topology (d.lieTorus (d.torusOf x))
  haveI : T2Space ↥(d.lieTorus (d.torusOf x)) :=
    (IsEmbedding.mk IsInducing.subtypeVal Subtype.val_injective).t2Space
  let e : ↥(d.lieTorus (d.torusOf x)) ≃L[F]
      (Fin (Module.finrank F ↥(d.lieTorus (d.torusOf x))) → F) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have key := locallyIntegrable_absF_det_rpow_of_odd_pow (μ.map e)
    (ρ ∘ₗ e.symm.toLinearMap) hAss hAinj hAc (fun w => hρA _)
    (fun k => by
      obtain ⟨X, hX⟩ := hρodd k
      exact ⟨e X, by simpa using hX⟩) ha
  have := (locallyIntegrable_map_homeomorph e.toHomeomorph).mp key
  simpa [Function.comp_def, ρ] using this

set_option maxHeartbeats 800000 in
/-- **The determinant estimate at `t₀ ∈ T_x`, in the `exp` chart**: for `x ∈ Γ(G,H)`, `t₀ ∈ T_x`
and `X ∈ 𝔱⁰(F)` near `0`, if `h ∈ T_x` has `h = e^X` and `t₀ h ∈ T_♮`, then `Δ(t₀ h)` is bounded
above by a constant and is comparable to `|det(ad X|_K)|_F`, `K = W''_x ∩ ker(P(t₀) − 1)`.
On `W''_x`, `P(t₀ h) − 1 = A e^Y − 1` with `A = P(t₀)|_{W''_x}` semisimple and
`Y = ad X|_{W''_x}` (`P(e^X) = e^{ad X}`), so `exists_absF_det_mul_expA_sub_one` applies. -/
theorem exists_eventually_deltaGGP_bounds {x t₀ : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    (ht₀ : t₀ ∈ d.torusOf x) :
    ∃ c C C' : ℝ, 0 < c ∧ ∀ᶠ X : ↥(d.lieTorus (d.torusOf x)) in 𝓝 0, ∀ h : ↥(GSpin d.QW),
      h ∈ d.torusOf x →
      (((h : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW) = expA F (X : CliffordAlgebra d.QW) →
      d.IsGammaElt (t₀ * h) ∧ d.torusOf (t₀ * h) = d.torusOf x →
      c * absF (LinearMap.det ((adV d.QW (X : CliffordAlgebra d.QW)).restrict
          (d.adV_mapsTo_movedSub_inf_ker ht₀ X))) ≤ deltaGGP d (t₀ * h) ∧
        deltaGGP d (t₀ * h) ≤ C * absF (LinearMap.det ((adV d.QW (X : CliffordAlgebra d.QW)).restrict
          (d.adV_mapsTo_movedSub_inf_ker ht₀ X))) ∧
        deltaGGP d (t₀ * h) ≤ C' := by
  classical
  letI : TopologicalSpace (Module.End F (Fin d.m → F)) := moduleTopology F _
  haveI : IsModuleTopology F (Module.End F (Fin d.m → F)) := ⟨rfl⟩
  let W'' := movedSub x
  letI : TopologicalSpace (Module.End F ↥W'') := moduleTopology F _
  haveI : IsModuleTopology F (Module.End F ↥W'') := ⟨rfl⟩
  haveI : ContinuousAdd (Module.End F (Fin d.m → F)) := IsModuleTopology.toContinuousAdd F _
  haveI : ContinuousAdd (Module.End F ↥W'') := IsModuleTopology.toContinuousAdd F _
  let P : ↥(GSpin d.QW) → Module.End F (Fin d.m → F) :=
    fun g => (specP d.QW g : (Fin d.m → F) →ₗ[F] (Fin d.m → F))
  have hxT : x ∈ (d.torusOf x) := d.self_mem_torusOf x
  have hPmaps : ∀ t : ↥(GSpin d.QW), t ∈ (d.torusOf x) → ∀ u ∈ W'', P t u ∈ W'' := by
    intro t ht
    have hc : Commute x t := (Subgroup.mem_centralizer_singleton_iff.mp ht.1).symm
    exact d.mapsTo_movedSub_of_commute (Steinberg.commute_toLinearMap ((hc.map (specP d.QW)).symm))
  -- `(Fin d.m → F) = W'_x ⊕ W''_x` and the compression `φ : End (Fin d.m → F) → End W''`
  have hss : Module.End.IsSemisimple (P x - 1) :=
    Module.End.IsSemisimple.sub_of_commute (Commute.one_right _)
      (isSemisimple_specP_of_isSS d.QW x hx.1) Module.End.isSemisimple_id
  have hcompl : IsCompl W'' (fixedSub x) := (isCompl_ker_range_of_isSemisimple hss).symm
  obtain ⟨π, hπ⟩ : ∃ π : (Fin d.m → F) →ₗ[F] ↥W'', ∀ w : W'', π w = w :=
    ⟨_, fun w => Submodule.projectionOnto_apply_left hcompl w⟩
  let φ : Module.End F (Fin d.m → F) →ₗ[F] Module.End F ↥W'' :=
    (LinearMap.llcomp F ↥W'' (Fin d.m → F) ↥W'' π).comp (LinearMap.lcomp F (Fin d.m → F) W''.subtype)
  have hφr : ∀ (M : Module.End F (Fin d.m → F)) (h : ∀ v ∈ W'', M v ∈ W''), φ M = M.restrict h :=
    fun M h => comp_comp_subtype_eq_restrict hπ h
  have hφc : Continuous φ := IsModuleTopology.continuous_of_linearMap φ
  have hadc : Continuous (adV d.QW : CliffordAlgebra d.QW → Module.End F (Fin d.m → F)) :=
    IsModuleTopology.continuous_of_linearMap (adV d.QW)
  have hcoe : Tendsto (fun X : ↥(d.lieTorus (d.torusOf x)) => (X : CliffordAlgebra d.QW)) (𝓝 0) (𝓝 0) :=
    continuous_subtype_val.tendsto' 0 0 rfl
  have hadT : Tendsto (fun X : ↥(d.lieTorus (d.torusOf x)) => adV d.QW (X : CliffordAlgebra d.QW))
      (𝓝 0) (𝓝 0) := (hadc.tendsto' 0 0 (map_zero _)).comp hcoe
  have hφT : Tendsto (fun X : ↥(d.lieTorus (d.torusOf x)) => φ (adV d.QW (X : CliffordAlgebra d.QW)))
      (𝓝 0) (𝓝 0) := (hφc.tendsto' 0 0 (map_zero _)).comp hadT
  -- the determinant estimate at `A = P(t₀)|_{W''}`
  have hA : Module.End.IsSemisimple ((P t₀).restrict (hPmaps t₀ ht₀)) :=
    Module.End.IsSemisimple.restrict (hPmaps t₀ ht₀)
      (isSemisimple_specP_of_isSS d.QW t₀ (isSS_of_mem_torusOf d hx ht₀))
  obtain ⟨A, hAdef⟩ : ∃ A : Module.End F ↥W'', A = (P t₀).restrict (hPmaps t₀ ht₀) :=
    ⟨_, rfl⟩
  have hA' : A.IsSemisimple := hAdef ▸ hA
  obtain ⟨c, C, C', hc, hev⟩ := exists_absF_det_mul_expA_sub_one (F := F) (V := ↥W'') hA'
  have hKeq : (LinearMap.ker (A - 1)).map W''.subtype =
      W'' ⊓ LinearMap.ker (P t₀ - 1) := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf, Submodule.subtype_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, ?_⟩
      have := congrArg Subtype.val hw
      simpa [hAdef, LinearMap.coe_restrict_apply] using this
    · rintro ⟨hv1, hv2⟩
      refine ⟨⟨v, hv1⟩, Subtype.ext ?_, rfl⟩
      simpa [hAdef, LinearMap.coe_restrict_apply] using hv2
  have hdK : ∀ (X : ↥(d.lieTorus (d.torusOf x))) (Y : Module.End F ↥W'')
      (hW : ∀ v ∈ W'', adV d.QW (X : CliffordAlgebra d.QW) v ∈ W''),
      Y = (adV d.QW (X : CliffordAlgebra d.QW)).restrict hW →
      ∀ hY : (∀ v ∈ LinearMap.ker (A - 1), Y v ∈ LinearMap.ker (A - 1)),
      absF (LinearMap.det (Y.restrict hY)) = absF (LinearMap.det
        ((adV d.QW (X : CliffordAlgebra d.QW)).restrict (d.adV_mapsTo_movedSub_inf_ker ht₀ X))) := by
    intro X Y hW hYe hY
    subst hYe
    have hK' : ∀ v ∈ (LinearMap.ker (A - 1)).map W''.subtype,
        adV d.QW (X : CliffordAlgebra d.QW) v ∈ (LinearMap.ker (A - 1)).map W''.subtype := by
      rw [hKeq]; exact d.adV_mapsTo_movedSub_inf_ker ht₀ X
    rw [det_restrict_restrict hW hY hK']
    exact congrArg absF (Steinberg.det_restrict_eq rfl hKeq _ _)
  refine ⟨c, C, C', hc, ?_⟩
  have E2 := hcoe.eventually (eventually_specP_eq_expA_adV (F := F) d.QW)
  have E3 := hadT.eventually (eventually_map_expA_of_pow (F := F) (B := Module.End F ↥W'') φ)
  have E4 := hφT.eventually hev
  filter_upwards [E2, E3, E4] with X hX2 hX3 hX4 h hhT hh ht
  have hXg : (X : CliffordAlgebra d.QW) ∈ gspin d.QW := X.2.1.1
  have hW : ∀ v ∈ W'', adV d.QW (X : CliffordAlgebra d.QW) v ∈ W'' :=
    d.mapsTo_movedSub_of_commute (commute_specP_adV d.QW hXg (X.2.2.1 x hxT))
  have hPh : P h = expA F (adV d.QW (X : CliffordAlgebra d.QW)) := hX2 hXg h hh
  have hpow : ∀ n : ℕ, φ (adV d.QW (X : CliffordAlgebra d.QW) ^ n) =
      φ (adV d.QW (X : CliffordAlgebra d.QW)) ^ n := by
    intro n
    rw [hφr _ hW, hφr _ (Module.End.pow_apply_mem_of_forall_mem n hW), Module.End.pow_restrict]
  have hexpY : expA F (φ (adV d.QW (X : CliffordAlgebra d.QW))) =
      (P h).restrict (hPmaps h hhT) := by
    rw [← hX3 hpow, ← hPh, hφr]
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = φ (adV d.QW (X : CliffordAlgebra d.QW)) := ⟨_, rfl⟩
  rw [← hYdef] at hexpY hX4
  have hYr : Y = (adV d.QW (X : CliffordAlgebra d.QW)).restrict hW := hYdef.trans (hφr _ hW)
  have hAY : Commute A Y := by
    rw [hYr, hAdef]
    have hc := commute_specP_adV d.QW hXg (X.2.2.1 t₀ ht₀)
    refine LinearMap.ext fun w => Subtype.ext ?_
    have := LinearMap.congr_fun hc.eq w
    simpa [P, LinearMap.coe_restrict_apply] using this
  have hY := mapsTo_ker_sub_one_of_commute hAY
  obtain ⟨h1, h2, h3⟩ := hX4 hAY hY
  have hm : ∀ u ∈ W'', (P (t₀ * h) - 1) u ∈ W'' := fun u hu =>
    W''.sub_mem (hPmaps _ ((d.torusOf x).mul_mem ht₀ hhT) u hu) hu
  have hΔ := deltaGGP_eq_absF_det_movedSub d hx ht.2 hm
  have heq : (P (t₀ * h) - 1).restrict hm = A * expA F Y - 1 := by
    rw [hexpY]
    refine LinearMap.ext fun w => Subtype.ext ?_
    simp [hAdef, P, LinearMap.coe_restrict_apply, map_mul]
  rw [hdK X Y hW hYr hY] at h1 h2
  rw [hΔ, heq]
  exact ⟨h1, h2, h3⟩

end GGPData

/-- **Integrability of `Δ^{s−1/2}` on `T_x(F)/A_{G,H}(F)`** (BP Astérisque 418, Lemma B.1.2(i),
applied as in Thesis Prop 12.1.1(i), proof of (12.1.2): "a straightforward application of
Lemma B.1.2(i)"; the same step in BP's proof of their Prop 11.2.1).

For `x ∈ Γ(G,H)` with torus `T = T_x`, `T_♮ = {t ∈ T | t ∈ Γ(G,H), T_t = T}` and `s > 0`, the
function `t ↦ 1_{T_♮}(t) Δ(t)^{s−1/2}` on `T(F)` (it is `A_{G,H}(F)`-invariant: `P(ct) = P(t)`),
evaluated on coset representatives, is integrable on the compact group `T(F)/A_{G,H}(F)` for its
probability Haar measure.

The thesis's step: on `T_♮` the eigenvalues of `P(t)` on `W'' = W''_x` are `λ_i(t)^{±1}`,
`1 ≤ i ≤ n = dim W''/2`, with `λ_1, …, λ_n` linearly independent characters of `T` (`T_x` is a
maximal torus of `GSpin(W''_x)`), so `Δ^{s−1/2} = ∏ |λ_i − 1|^{2s−1}`, locally integrable by
B.1.2(i) at `2s`, hence integrable on the compact quotient.  On `T_♮`, `Δ(t)` is computed on
`W''_x` (`deltaGGP_eq_absF_det_movedSub`).

Proof here (B.1.2(i) is not stated, see the module docstring): `integrable_of_chart` with the
`exp` chart `exists_expA_chart_torusOf`; near `t₀`, `Δ(t₀ e^X) ≍ |det(ad X|_K)|_F`,
`K = W''_x ∩ ker(P(t₀) − 1)` (`exists_absF_det_mul_expA_sub_one`), so for `s < 1/2` the integrand
is dominated by `|det(ad X|_K)|^{s−1/2}`, locally integrable by
`locallyIntegrable_absF_det_adV_rpow`; for `s ≥ 1/2` it is locally bounded.
Exact source: arXiv:1506.01452 (BP), App. B.1, Lemma B.1.2(i) (Astérisque 418, p. 281), for `F`
any local field of characteristic `0` other than `ℂ`.

Stated for `Γ`-tori only (`T = T_x`, `x ∈ Γ(G,H)`); for any other subgroup the integrand is `0`
(`TraceFormula/MGeom.lean`, `integrable_delta_rpow`). -/
theorem bp_integrable_deltaGGP_rpow (d : GGPData F) {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    {s : ℝ} (hs : 0 < s) :
    letI : MeasurableSpace (d.TorusQuot (d.torusOf x)) := borel _
    haveI : BorelSpace (d.TorusQuot (d.torusOf x)) := ⟨rfl⟩
    Integrable (fun q : d.TorusQuot (d.torusOf x) =>
      Set.indicator {t : ↥(GSpin d.QW) | d.IsGammaElt t ∧ d.torusOf t = d.torusOf x}
        (fun t => deltaGGP d t ^ (s - 1 / 2))
        ((Quotient.out q : ↥(d.torusOf x)) : ↥(GSpin d.QW)))
      (probHaar (d.TorusQuot (d.torusOf x))) := by
  classical
  obtain ⟨μ, hμ, Φ, U, hUo, hU0, hΦc, hΦn, hΦU, hμS⟩ := d.exists_expA_chart_torusOf hx
  haveI := hμ
  letI : MeasurableSpace (d.TorusQuot (d.torusOf x)) := borel _
  haveI : BorelSpace (d.TorusQuot (d.torusOf x)) := ⟨rfl⟩
  haveI : CompactSpace (d.TorusQuot (d.torusOf x)) := hx.2.2
  set ν := probHaar (d.TorusQuot (d.torusOf x))
  set a : ℝ := s - 1 / 2 with hadef
  set Snat := {t : ↥(GSpin d.QW) | d.IsGammaElt t ∧ d.torusOf t = (d.torusOf x)}
  set f₀ : ↥(d.torusOf x) → ℝ := fun t => Snat.indicator (fun t => deltaGGP d t ^ a) (t : ↥(GSpin d.QW))
  have hf₀0 : ∀ t, 0 ≤ f₀ t := fun t =>
    Set.indicator_nonneg (fun t _ => Real.rpow_nonneg (deltaGGP_nonneg d t) _) _
  -- invariance under the scalars
  have hinv : ∀ t : ↥(d.torusOf x), ∀ n ∈ d.scalarsIn (d.torusOf x), f₀ (t * n) = f₀ t := by
    intro t n hn
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hn
    have e : ((t * n : ↥(d.torusOf x)) : ↥(GSpin d.QW)) = scalarGSpin d.QW c * (t : ↥(GSpin d.QW)) := by
      rw [Subgroup.coe_mul, ← hc, (scalarGSpin_commute d.QW c _).eq]
    simp only [f₀, e, Snat, Set.indicator, Set.mem_ofPred_eq, isGammaElt_scalar_mul_iff,
      torusOf_scalar_mul, deltaGGP_scalar_mul]
  -- the chart
  refine integrable_of_chart ν μ Φ hUo hU0 hΦc hΦn (fun S hS hSm => hμS S hS hSm) ?_ ?_
  · -- measurability
    set fC : ↥(d.torusOf x) → ℂ := fun t => (f₀ t : ℂ)
    have hm := aestronglyMeasurable_comp_out (d.scalarsIn (d.torusOf x)) ν (f := fC)
      (fun t n hn => by simp only [fC, hinv t n hn]) (isOpen_torusNat d (d.torusOf x))
      (fun t ht => by simp only [fC, f₀, Set.indicator_of_notMem (s := Snat) ht, Complex.ofReal_zero])
      ((continuousOn_deltaGGP_rpow d (d.torusOf x) s).congr fun t ht => by
        simp only [fC, f₀, Set.indicator_of_mem (s := Snat) ht, hadef])
    have := Complex.continuous_re.comp_aestronglyMeasurable hm
    simpa [fC] using this
  · intro q₀
    set t₀ : ↥(d.torusOf x) := Quotient.out q₀ with ht₀def
    have hq₀ : q₀ = (t₀ : d.TorusQuot (d.torusOf x)) := (QuotientGroup.out_eq' q₀).symm
    obtain ⟨c, C, C', hc, hev⟩ := d.exists_eventually_deltaGGP_bounds hx t₀.2
    let dK : ↥(d.lieTorus (d.torusOf x)) → ℝ := fun X => absF (LinearMap.det
      ((adV d.QW (X : CliffordAlgebra d.QW)).restrict (d.adV_mapsTo_movedSub_inf_ker t₀.2 X)))
    have key : ∀ᶠ X in 𝓝 (0 : ↥(d.lieTorus (d.torusOf x))), ∃ t : ↥(d.torusOf x),
        ‖f₀ (Quotient.out (q₀ * Φ X))‖ = f₀ t ∧ ((t : ↥(GSpin d.QW)) ∈ Snat →
          c * dK X ≤ deltaGGP d t ∧ deltaGGP d t ≤ C * dK X ∧ deltaGGP d t ≤ C') := by
      filter_upwards [hUo.mem_nhds hU0, hev] with X hXU hX
      obtain ⟨h, hh, hΦh⟩ := hΦU X hXU
      refine ⟨t₀ * h, ?_, fun ht => hX h h.2 hh ht⟩
      rw [hq₀, hΦh, ← QuotientGroup.mk_mul,
        comp_out_mk_of_invariant (d.scalarsIn (d.torusOf x)) hinv, Real.norm_of_nonneg (hf₀0 _)]
    by_cases ha : 0 ≤ a
    · letI := isTopologicalRing_of_moduleTopology F (CliffordAlgebra d.QW)
      haveI := t2Space_of_moduleTopology F (CliffordAlgebra d.QW)
      haveI := submodule_isTopologicalAddGroup (d.lieTorus (d.torusOf x))
      obtain ⟨_, _, _, _, _⟩ := submodule_topology (d.lieTorus (d.torusOf x))
      refine ⟨fun _ => |C'| ^ a, (locallyIntegrable_const _) 0, ?_⟩
      filter_upwards [key] with X ⟨t, hnorm, hb⟩
      rw [hnorm]
      by_cases ht : (t : ↥(GSpin d.QW)) ∈ Snat
      · simp only [f₀, Set.indicator_of_mem ht]
        exact Real.rpow_le_rpow (deltaGGP_nonneg d _) ((hb ht).2.2.trans (le_abs_self _)) ha
      · simp only [f₀, Set.indicator_of_notMem ht]
        positivity
    · push Not at ha
      have hL := d.locallyIntegrable_absF_det_adV_rpow hx t₀.2 (a := a) (by rw [hadef]; linarith) μ
      obtain ⟨V, hV, hint⟩ := hL 0
      refine ⟨fun X => c ^ a * dK X ^ a, ⟨V, hV, hint.const_mul (c ^ a)⟩, ?_⟩
      filter_upwards [key] with X ⟨t, hnorm, hb⟩
      rw [hnorm]
      by_cases ht : (t : ↥(GSpin d.QW)) ∈ Snat
      · simp only [f₀, Set.indicator_of_mem ht]
        obtain ⟨h1, h2, -⟩ := hb ht
        have hΔ0 : 0 < deltaGGP d t := deltaGGP_pos d _ ht.1.1
        have hdK0 : 0 < dK X := by
          by_contra hneg
          have h0 : dK X = 0 := le_antisymm (not_lt.mp hneg) (absF_nonneg _)
          have : C * dK X = 0 := by rw [h0, mul_zero]
          linarith
        rw [← Real.mul_rpow hc.le hdK0.le]
        exact Real.rpow_le_rpow_of_nonpos (by positivity) h1 ha.le
      · simp only [f₀, Set.indicator_of_notMem ht]
        exact mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg (absF_nonneg _) _)

end GSpinGGP
