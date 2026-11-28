/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.W1Untruncated
import GSpinGGP.TraceFormula.LuoTransfer
import GSpinGGP.TraceFormula.ConeTorus
import GSpinGGP.GGP.QuadClassify

/-!
# The geometric expansion near `1` when `W` is a hyperbolic plane

`geomAt_near_hypW`: for `W` a hyperbolic plane, `J(f) = m_geom(θ_f)` for `f ∈ ScuspTestFn d χ`
supported near `A_G(F)`.  The route (the special orthogonal group `SO(V)` alone, on its Lie
algebra):

1. **Descent and dictionary** (`exists_hypW_descent`, SORRY, own work).  With `W` a hyperbolic
   plane, `T_W = GSpin(W) ≅ G_m²` is central and split, `A_G = T_W × Z_V`, and
   `Φ(t, g) = t⁻¹ g` identifies `H(F)\G(F)/A_G(F)` with `U(F)SO(W)(F)\SO(V)(F)` (Hilbert 90).  Near
   `1`, `f` descends to `1_{ω_W} ⊗ φ_ω` on `so(W) ⊕ so(V)` (`χ ∘ exp = 1` on a small `ω_W`;
   Jacobians `≡ 1` on a small `ω`); `φ_ω` is very cuspidal (the proper parabolics of `G` are
   `GSpin(W) × P_V`); `K(f, x) = I(1_{ω_W}, φ_ω, Φ(x))` pointwise for compatible measures, so
   `J(f) = ∫ I(θ, φ_ω, g) dg` and the integrability of `K(f, ·)` (`distribJ_convergent`) passes to
   `I(θ, φ_ω, ·)`; and `m_geom(θ_f) = c_θ(0) c_{θ_{φ_ω}}(0)` (`Γ(G, H)` is the class of `1`;
   `(θ_f)_ω = θ_{φ_ω}` near `0`).
2. **Waldspurger 2010 Thm 7.9 untruncated** (`LuoDatum.integral_Ig_eq_Igeom`, from the axiom
   `waldspurger2010_thm_7_9`): `∫ I(θ, φ, g) dg = I(θ, φ)`.
3. **The geometric side for `W` a plane** (`Igeom_of_isHypPlane`): `𝒯` is `{1}`, so
   `I(θ, φ) = c_θ(0) c_f(0)`.  For `Y ≠ 0`, `T_Y = SO(W)` contains the split torus
   `diag(t, t⁻¹)` and is not compact (`not_compactSpace_torusH`); for `Y = 0`, condition (4) is
   `d_an(V) = 1` (`anisoDim_top_of_isHypPlane`, using that `D ⊕ Z` is nondegenerate,
   `isNondeg_QZ`).
-/

open MeasureTheory Topology Filter

noncomputable section

namespace GSpinGGP

namespace LuoDatum

/-! ## `D ⊕ Z` is nondegenerate, and the Witt index of `V` when `W` is a hyperbolic plane -/

section Witt

variable {K : Type*} [Field K] [Invertible (2 : K)] (L : LuoDatum K)

/-- The index `k − r ∈ [−r, r]` of the `k`-th vector of Luo's basis `z_{-r}, …, z_r`. -/
def zIdx (k : Fin (2 * L.r + 1)) : ℤ := (k : ℤ) - L.r

theorem abs_zIdx_le (k : Fin (2 * L.r + 1)) : |L.zIdx k| ≤ L.r := by
  unfold zIdx
  have := k.2
  rw [abs_le]
  constructor <;> omega

theorem bform_z_neg {i j : ℤ} (hi : |i| ≤ L.r) (hj : |j| ≤ L.r) :
    bform L.QZ (L.z i) (L.z (-j)) = if i = j then (if i = 0 then L.QZ (L.z 0) else 1) else 0 := by
  rw [L.gram i (-j) hi (by rwa [abs_neg])]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (by omega), if_neg h]

/-- Pairing with `z_{-i}` reads off the coefficient of `z_i` (the Gram matrix of Luo's basis is
antidiagonal with nonzero entries). -/
theorem coeff_eq_zero_of_bform_sum (c : Fin (2 * L.r + 1) → K)
    (h : ∀ k, bform L.QZ (∑ j, c j • L.z (L.zIdx j)) (L.z (-L.zIdx k)) = 0)
    (k : Fin (2 * L.r + 1)) : c k = 0 := by
  have hk := h k
  rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single k] at hk
  · rw [map_smul, LinearMap.smul_apply, L.bform_z_neg (L.abs_zIdx_le k) (L.abs_zIdx_le k),
      if_pos rfl, smul_eq_mul] at hk
    split_ifs at hk with h0
    · exact (mul_eq_zero.1 hk).resolve_right L.aniso
    · simpa using hk
  · intro j _ hjk
    rw [map_smul, LinearMap.smul_apply, L.bform_z_neg (L.abs_zIdx_le j) (L.abs_zIdx_le k),
      if_neg, smul_zero]
    intro he
    apply hjk
    unfold zIdx at he
    exact Fin.ext (by omega)
  · simp

/-- Luo's vectors `z_{-r}, …, z_r` are linearly independent. -/
theorem linearIndependent_z : LinearIndependent K (fun k => L.z (L.zIdx k)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  exact L.coeff_eq_zero_of_bform_sum c (fun k => by rw [hc, map_zero, LinearMap.zero_apply]) k

/-- **`D ⊕ Z` is nondegenerate**: Luo's vectors form a basis with invertible Gram matrix. -/
theorem isNondeg_QZ : IsNondeg L.QZ := by
  rw [isNondeg_iff]
  intro x hx
  let b := basisOfLinearIndependentOfCardEqFinrank L.linearIndependent_z (by simp)
  have hb : ∀ k, b k = L.z (L.zIdx k) := fun k => by simp [b]
  have hx' : x = ∑ j, b.repr x j • L.z (L.zIdx j) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [hb]
  have h0 := L.coeff_eq_zero_of_bform_sum (b.repr x) (fun k => by rw [← hx']; exact hx _)
  rw [hx']
  simp [h0]

/-- `V = W ⊕ D ⊕ Z` is nondegenerate. -/
theorem isNondeg_QV : IsNondeg L.QV := isNondeg_prod L.nondeg L.isNondeg_QZ

/-- `Z⁺ = ⟨z_1, …, z_r⟩` is totally isotropic of dimension `r`, so `w(D ⊕ Z) ≥ r`. -/
theorem le_wittIndex_QZ : L.r ≤ wittIndex L.QZ := by
  let φ : Fin L.r → Fin (2 * L.r + 1) := fun j => ⟨j + L.r + 1, by omega⟩
  have hφ : Function.Injective φ := fun a b h => Fin.ext (by
    have := congrArg Fin.val h; simp only [φ] at this; omega)
  have hidx : ∀ j, L.zIdx (φ j) = (j : ℤ) + 1 := fun j => by simp [zIdx, φ]; ring
  have hli := L.linearIndependent_z.comp φ hφ
  have hiso : IsTotallyIsotropic L.QZ
      (Submodule.span K (Set.range ((fun k => L.z (L.zIdx k)) ∘ φ))) := by
    refine isTotallyIsotropic_span_of_polar _ fun i j => ?_
    simp only [Function.comp_apply, hidx]
    rw [polar_eq_two_mul_bform, L.gram _ _ (by rw [abs_le]; constructor <;> omega)
      (by rw [abs_le]; constructor <;> omega), if_neg (by omega), mul_zero]
  have := QuadClassify.le_wittIndex hiso
  rwa [finrank_span_eq_card hli, Fintype.card_fin] at this

/-- **`d_an(V) = 1` when `W` is a hyperbolic plane**: `V = W ⊕ D ⊕ Z` with `W` and `Z`
hyperbolic, so `w(V) = r + 1` and `dim V = 2r + 3`. -/
theorem anisoDim_top_of_isHypPlane {F : Type} [NontriviallyNormedField F] [PAdicField F]
    {L : LuoDatum F} (hW : IsHypPlane L.QW) : L.anisoDim ⊤ = 1 := by
  have hlow : wittIndex L.QW + wittIndex L.QZ ≤ wittIndex L.QV :=
    QuadClassify.wittIndex_prod_ge L.QW L.QZ
  have hup := TauCeti.RegularFormClass.two_mul_wittIndex_le_rank
    (TauCeti.formClass L.QV ((isNondeg_iff_nondegenerate _).1 L.isNondeg_QV))
  rw [TauCeti.rank_formClass, ← wittIndex_eq_regularFormClass_wittIndex] at hup
  have hQZ := L.le_wittIndex_QZ
  have hm := hW.1
  have hw := hW.2.2
  have htop : wittIndex (L.QV.comp (⊤ : Submodule F L.V).subtype) = wittIndex L.QV :=
    QuadClassify.wittIndex_eq_of_isometryEquiv
      { toLinearEquiv := Submodule.topEquiv, map_app' := fun _ => rfl }
  unfold anisoDim
  rw [htop, finrank_top]
  simp only [Module.finrank_prod, Module.finrank_fin_fun] at hup hm ⊢
  omega

end Witt

/-! ## Endomorphisms of a hyperbolic plane -/

section HypTorus

open QuadraticMap

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {f f' : V}

omit [Invertible (2 : K)] in
/-- On a plane with hyperbolic pair `f, f'`, `w = polar(w, f') f + polar(w, f) f'`. -/
theorem eq_polar_smul_add_of_hypPair (hdim : Module.finrank K V = 2) (hf : Q f = 0)
    (hf' : Q f' = 0) (hp : polar Q f f' = 1) (w : V) :
    w = polar Q w f' • f + polar Q w f • f' := by
  obtain ⟨a, b, hw⟩ := exists_eq_smul_add_smul_of_hypPair (Q := Q) (W := ⊤) (w := w)
    (by rwa [finrank_top]) Submodule.mem_top Submodule.mem_top hf hf' hp Submodule.mem_top
  subst hw
  have hff : polar Q f f = 0 := by rw [polar_self, hf, smul_zero]
  have hff' : polar Q f' f' = 0 := by rw [polar_self, hf', smul_zero]
  have hp' : polar Q f' f = 1 := by rw [polar_comm]; exact hp
  simp [polar_add_left, polar_smul_left, hff, hff', hp, hp']

omit [Invertible (2 : K)] in
/-- Two endomorphisms of a plane with hyperbolic pair `f, f'` agreeing on `f` and `f'` are
equal. -/
theorem ext_hypPair (hdim : Module.finrank K V = 2) (hf : Q f = 0) (hf' : Q f' = 0)
    (hp : polar Q f f' = 1) {φ φ' : V →ₗ[K] V} (h1 : φ f = φ' f) (h2 : φ f' = φ' f') :
    φ = φ' :=
  LinearMap.ext fun w => by
    rw [eq_polar_smul_add_of_hypPair hdim hf hf' hp w]
    simp only [map_add, map_smul, h1, h2]

end HypTorus

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {L : LuoDatum F}
  {ψ : NontrivialAddChar F}

/-! ## Only `Y = 0` gives a torus of `𝒯` when `W` is a hyperbolic plane -/

section OnlyZero

open QuadraticMap

/-- A hyperbolic pair of `W` when `W` is a hyperbolic plane. -/
theorem exists_hypPair_W (hW : IsHypPlane L.QW) :
    ∃ f f' : L.W, L.QW f = 0 ∧ L.QW f' = 0 ∧ polar L.QW f f' = 1 := by
  obtain ⟨U, hU, hdim⟩ := exists_wittIndex L.QW
  rw [hW.2.2] at hdim
  obtain ⟨f, hfU, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := U) fun h => by
    rw [h, finrank_bot] at hdim; exact zero_ne_one hdim
  obtain ⟨f', hf', hp⟩ := exists_hyperbolicPair_of_isotropic L.nondeg hf0 (hU f hfU)
  exact ⟨f, f', hU f hfU, hf', hp⟩

/-- `Y ∈ so(W)` is skew for the polar form. -/
theorem polar_asW_skew {Y : L.EndW} (hY : Y ∈ L.soW) (x y : L.W) :
    polar L.QW (L.asW Y x) y = - polar L.QW x (L.asW Y y) := by
  have h : (bform L.QW).IsSkewAdjoint (L.asW Y) := (LinearMap.mem_skewAdjointSubmodule _).1 hY
  rw [polar_eq_two_mul_bform, polar_eq_two_mul_bform, h x y]
  simp

/-- **`T_Y` is not compact for `Y ≠ 0`** when `W` is a hyperbolic plane: `Y` is diagonal
`diag(a, −a)` in a hyperbolic pair, `a ≠ 0`, so `ker Y = 0` and every `diag(t, t⁻¹)` (Tau Ceti's
`hyperbolicPairTorus`) lies in `T_Y = SO(W)`; its coordinate `t` is unbounded. -/
theorem not_compactSpace_torusH (hW : IsHypPlane L.QW) {Y : L.EndW} (hY : Y ∈ L.soW)
    (hY0 : Y ≠ 0) : ¬ CompactSpace ↥(L.torusH Y) := by
  intro hc
  obtain ⟨f, f', hf, hf', hp⟩ := exists_hypPair_W hW
  have hdim : Module.finrank F L.W = 2 := hW.1
  have h2 : (2 : F) ≠ 0 := Invertible.ne_zero 2
  have hp' : polar L.QW f' f = 1 := by rw [polar_comm]; exact hp
  have hskew := polar_asW_skew hY
  set α := polar L.QW (L.asW Y f) f' with hα
  have hYf : L.asW Y f = α • f := by
    have h0 : polar L.QW (L.asW Y f) f = 0 := by
      have h := hskew f f
      rw [polar_comm L.QW f] at h
      exact (mul_eq_zero.1 (by linear_combination h : (2 : F) * _ = 0)).resolve_left h2
    rw [eq_polar_smul_add_of_hypPair hdim hf hf' hp (L.asW Y f), h0, zero_smul, add_zero]
  have hYf' : L.asW Y f' = (-α) • f' := by
    have h0 : polar L.QW (L.asW Y f') f' = 0 := by
      have h := hskew f' f'
      rw [polar_comm L.QW f'] at h
      exact (mul_eq_zero.1 (by linear_combination h : (2 : F) * _ = 0)).resolve_left h2
    have h1 : polar L.QW (L.asW Y f') f = -α := by
      rw [hskew, hYf, polar_smul_right, hp', smul_eq_mul, mul_one]
    rw [eq_polar_smul_add_of_hypPair hdim hf hf' hp (L.asW Y f'), h0, h1, zero_smul, zero_add]
  have hα0 : α ≠ 0 := by
    intro h0
    apply hY0
    have : L.asW Y = 0 := ext_hypPair hdim hf hf' hp (by rw [hYf, h0, zero_smul]; rfl)
      (by rw [hYf', h0, neg_zero, zero_smul]; rfl)
    exact this
  have hker : ∀ w, L.asW Y w = 0 → w = 0 := by
    intro w hw
    have e1 : polar L.QW w f' = 0 := by
      have h := hskew w f'
      rw [hw, polar_zero_left, hYf', polar_smul_right, smul_eq_mul] at h
      have : α * polar L.QW w f' = 0 := by linear_combination -h
      exact (mul_eq_zero.1 this).resolve_left hα0
    have e2 : polar L.QW w f = 0 := by
      have h := hskew w f
      rw [hw, polar_zero_left, hYf, polar_smul_right, smul_eq_mul] at h
      have : α * polar L.QW w f = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_left hα0
    rw [eq_polar_smul_add_of_hypPair hdim hf hf' hp w, e1, e2, zero_smul, zero_smul, add_zero]
  -- Tau Ceti's split torus of the pair `f, f'` (`f ↦ t f`, `f' ↦ t⁻¹ f'`), as units of `End W`
  let g : Fˣ → L.EndWˣ := fun t => (LinearMap.GeneralLinearGroup.generalLinearEquiv F L.W).symm
    (TauCeti.QuadraticMap.hyperbolicPairTorus L.QW hf hf' hp t : L.W ≃ₗ[F] L.W)
  have hg : ∀ t : Fˣ, ∀ x, L.asW ((g t : L.EndWˣ) : L.EndW) x =
      (TauCeti.QuadraticMap.hyperbolicPairTorus L.QW hf hf' hp t : L.W ≃ₗ[F] L.W) x :=
    fun _ _ => rfl
  have hgf : ∀ t : Fˣ, L.asW ((g t : L.EndWˣ) : L.EndW) f = (t : F) • f := fun t => by
    rw [hg]; simp
  have hgf' : ∀ t : Fˣ, L.asW ((g t : L.EndWˣ) : L.EndW) f' = ((t⁻¹ : Fˣ) : F) • f' :=
    fun t => by rw [hg]; simp
  have hmem : ∀ t : Fˣ, g t ∈ L.torusH Y := by
    intro t
    refine ⟨?_, ?_, fun w hw => ?_⟩
    · show (LinearMap.GeneralLinearGroup.generalLinearEquiv F L.W) (g t) ∈ SOGrp L.QW
      rw [MulEquiv.apply_symm_apply, SOGrp_eq_specialOrthogonalGroup]
      exact TauCeti.QuadraticMap.hyperbolicPairTorus_mem_specialOrthogonalGroup _ _ _ t
    · show L.asW ((g t : L.EndWˣ) : L.EndW) * L.asW Y = L.asW Y * L.asW ((g t : L.EndWˣ) : L.EndW)
      refine ext_hypPair hdim hf hf' hp ?_ ?_
      · rw [mul_apply_eq_comp, mul_apply_eq_comp, hYf, map_smul, hgf, map_smul, hYf, smul_comm]
      · rw [mul_apply_eq_comp, mul_apply_eq_comp, hYf', map_smul, hgf', map_smul, hYf',
          smul_comm]
    · rw [hker w hw, map_zero]
  -- the coordinate `g ↦ polar(g f, f')` is continuous and unbounded on `T_Y`
  let ℓ : L.EndW →ₗ[F] F :=
    { toFun := fun g => polar L.QW (L.asW g f) f'
      map_add' := fun a b => polar_add_left _ _ _ _
      map_smul' := fun c a => by
        show polar L.QW (c • L.asW a f) f' = c • polar L.QW (L.asW a f) f'
        rw [polar_smul_left] }
  have hcont : Continuous fun g : ↥(L.torusH Y) => ℓ ((g : L.EndWˣ) : L.EndW) :=
    (IsModuleTopology.continuous_of_linearMap ℓ).comp
      (Units.continuous_val.comp continuous_subtypeVal)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1 (Set.mem_univ _))
  obtain ⟨s, hs⟩ := NormedField.exists_lt_norm F C
  have hs0 : s ≠ 0 := norm_pos_iff.1 (hC0.trans_lt hs)
  have hval := hC ⟨_, hmem (Units.mk0 s hs0)⟩ (Set.mem_univ _)
  have hℓ : ℓ ((g (Units.mk0 s hs0) : L.EndWˣ) : L.EndW) = s := by
    show polar L.QW (L.asW ((g (Units.mk0 s hs0) : L.EndWˣ) : L.EndW) f) f' = s
    rw [hgf, polar_smul_left, hp, Units.val_mk0, smul_eq_mul, mul_one]
  have : ‖s‖ ≤ C := by rw [← hℓ]; exact hval
  linarith

/-- **When `W` is a hyperbolic plane, only `Y = 0` defines a torus of `𝒯`.** -/
theorem eq_zero_of_isW1Elt (hW : IsHypPlane L.QW) {Y : L.EndW} (hY : L.IsW1Elt Y) : Y = 0 := by
  by_contra hY0
  exact not_compactSpace_torusH hW hY.1 hY0 hY.2.2.2.1

end OnlyZero

/-! ## The term of `T = {1}` -/

section TrivialTorus

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- `T_0 = {1}`: an element acting trivially on `ker 0 = W` is `1`. -/
theorem torusH_zero : L.torusH 0 = ⊥ := by
  ext g
  rw [Subgroup.mem_bot]
  refine ⟨fun hg => Units.ext (LinearMap.ext fun w => hg.2.2 w (LinearMap.mem_ker.2 rfl)),
    fun hg => hg ▸ (L.torusH 0).one_mem⟩

theorem fixedW_bot : L.fixedW ⊥ = ⊤ := by
  rw [eq_top_iff]
  intro w _
  rw [fixedW, Submodule.mem_iInf]
  intro t
  rw [Subgroup.mem_bot.1 t.2]
  exact LinearMap.mem_ker.2 (sub_self w)

theorem subsingleton_lieTorusW {T : Subgroup L.EndWˣ} (hT : T = ⊥) :
    Subsingleton ↥(L.lieTorusW T) := by
  subst hT
  refine ⟨fun a b => Subtype.ext ?_⟩
  have h0 : ∀ Y : ↥(L.lieTorusW ⊥), (Y : L.EndW) = 0 := fun Y =>
    LinearMap.ext fun w => Y.2.2.2 w (by rw [fixedW_bot]; exact Submodule.mem_top)
  rw [h0 a, h0 b]

theorem weylW1_bot : L.weylW1 ⊥ = 1 := by
  unfold weylW1
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
  induction a using QuotientGroup.induction_on
  induction b using QuotientGroup.induction_on
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  intro h hh
  have : h = 1 := Subtype.ext (Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 hh))
  rw [this, one_mul, mul_one]

theorem muT_real_univ (I : L.W1Input ψ) (T : L.W1Torus) (hT : T.1 = ⊥) :
    (I.μT T).real Set.univ = 1 := by
  haveI := subsingleton_lieTorusW hT
  have h := I.hμT T
  letI : MeasurableSpace ↥T.1 := borel _
  haveI : BorelSpace ↥T.1 := ⟨rfl⟩
  obtain ⟨-, U, hU, hS⟩ := h
  have hsub : Set.univ ⊆ U := fun y _ => by
    rw [Subsingleton.elim y 0]; exact mem_of_mem_nhds hU
  have hone : ∀ t : ↥T.1, t = 1 := fun t => Subtype.ext (Subgroup.mem_bot.1 (hT ▸ t.2))
  haveI : Subsingleton ↥T.1 := ⟨fun a b => (hone a).trans (hone b).symm⟩
  haveI : Finite ↥T.1 := Finite.of_subsingleton
  have e := hS Set.univ MeasurableSet.univ hsub
  have hset : {t : ↥T.1 | ∃ X ∈ (Set.univ : Set ↥(L.lieTorusW T.1)),
      ((t : L.EndWˣ) : L.EndW) = expA F (X : L.EndW)} = Set.univ := by
    ext t
    simp only [Set.mem_univ, true_and, iff_true]
    refine ⟨0, ?_⟩
    rw [hone t]
    simp [expA, NormedSpace.exp_zero]
  rw [hset] at e
  rw [measureReal_def, e, measure_univ, ENNReal.toReal_one]

theorem subsingleton_range_zero : Subsingleton ↥(LinearMap.range (L.asW 0)) :=
  ⟨fun a b => by
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    exact Subtype.ext (hx.symm.trans hy)⟩

theorem isNatW_zero {T : Subgroup L.EndWˣ} (hT : T = ⊥) : L.IsNatW T 0 := by
  subst hT
  haveI := L.subsingleton_range_zero
  refine ⟨zero_mem _, ?_, ?_⟩
  · rw [fixedW_bot]; exact LinearMap.ker_zero
  · rw [Subsingleton.elim (LinearMap.restrict _ _) 0, LinearMap.charpoly_zero,
      Module.finrank_zero_of_subsingleton, pow_zero]
    exact squarefree_one

theorem deltaW_zero : L.deltaW 0 = 1 := by
  haveI := L.subsingleton_range_zero
  rw [deltaW, LinearMap.det_eq_one_of_subsingleton, absF_one]

/-- `D^H(0) = 1`: `ad 0 = 0`, whose characteristic polynomial `X^n` has trailing coefficient `1`. -/
theorem weylDiscLie_zero_soW : weylDiscLie L.soW 0 = 1 := by
  unfold weylDiscLie
  rw [dif_pos (fun Y _ => by simp)]
  have h : ∀ g : Module.End F ↥L.soW.toSubmodule, g = 0 →
      absF (LinearMap.charpoly g).trailingCoeff = 1 := by
    rintro g rfl
    rw [LinearMap.charpoly_zero, Polynomial.trailingCoeff_X_pow, absF_one]
  apply h
  ext Y
  simp

theorem isW1Elt_zero (hW : IsHypPlane L.QW) : L.IsW1Elt 0 := by
  have hone : ∀ t ∈ L.torusH 0, t = 1 := fun t ht => Subgroup.mem_bot.1 (L.torusH_zero ▸ ht)
  refine ⟨zero_mem _, isSS_zero F, fun a ha b hb => by rw [hone a ha, hone b hb], ?_, ?_⟩
  · haveI : Subsingleton ↥(L.torusH 0) :=
      ⟨fun a b => Subtype.ext ((hone a a.2).trans (hone b b.2).symm)⟩
    haveI : Finite ↥(L.torusH 0) := Finite.of_subsingleton
    infer_instance
  · unfold Cond4
    have hm := hW.1
    simp only [Module.finrank_fin_fun] at hm
    rw [if_neg (by
      simp only [Module.finrank_prod, Module.finrank_fin_fun, hm, Nat.not_even_iff_odd]
      exact ⟨L.r + 1, by ring⟩)]
    have htop : L.V2sub 0 = ⊤ := by
      unfold V2sub
      rw [show LinearMap.ker (L.asW 0) = ⊤ from LinearMap.ker_zero, Submodule.prod_top]
    rw [htop]
    exact anisoDim_top_of_isHypPlane hW

end TrivialTorus

/-- **W1's `I(θ, f)` when `W` is a hyperbolic plane** (W1 §7.3, §7.9, evaluated).
The subtori of `H = SO(W) ≅ G_m` are `{1}` and `SO(W)`; `SO(W)` is split, so `A_T ≠ 1`
(condition (1)): for `Y ≠ 0` in `𝔥 ≅ F`, `T_Y = SO(W)` has non-compact `F`-points.  For `T = {1}`:
`W' = 0`, `W'' = W`, `V'' = V`, `d` is odd, and condition (4) is `d_an(V) = 1`, which holds since
`V = W ⊕ D ⊕ Z` with `W` and `Z` hyperbolic (`isW1Elt_zero`, `eq_zero_of_isW1Elt`).  So `𝒯` is
one class `{1}`.  For `T = {1}`: `|W(H, T)| = 1`, `𝔱 = 0` with `ν(T) dY` the unit point mass
(`IsExpCompatTW`), `0 ∈ 𝔱_♮`, `D^H(0) = 1` (`ad 0 = 0`), `Δ(0) = 1` (determinant on the zero
space).  Hence `I(θ, f) = c_θ(0) c_f(0)`. -/
theorem Igeom_of_isHypPlane (hW : IsHypPlane L.QW) (I : L.W1Input ψ) (θ : ↥L.soW → ℂ)
    (τ : ↥L.soV → ℂ) :
    I.Igeom θ τ = L.cThetaW ψ θ 0 * L.cFW ψ τ 0 := by
  have hbot : ∀ T : L.W1Torus, T.1 = ⊥ := fun T => by
    obtain ⟨Y, hY, hT⟩ := T.2
    rw [← hT, eq_zero_of_isW1Elt hW hY, torusH_zero]
  let T0 : L.W1Torus := ⟨_, 0, isW1Elt_zero hW, rfl⟩
  haveI : Subsingleton L.W1Torus := ⟨fun a b => Subtype.ext ((hbot a).trans (hbot b).symm)⟩
  haveI : Subsingleton L.W1Class := by
    refine ⟨fun a b => ?_⟩
    induction a using Quot.ind
    induction b using Quot.ind
    congr 1
    exact Subsingleton.elim _ _
  unfold W1Input.Igeom Igeom
  rw [tsum_eq_single (L := SummationFilter.unconditional L.W1Class)
    (f := fun c : L.W1Class => ((L.weylW1 (Quot.out c).1 : ℂ))⁻¹ *
      ∫ Y : ↥(L.lieTorusW (Quot.out c).1),
        L.geomIntegrand ψ θ τ (Quot.out c).1 Y ∂I.μT (Quot.out c))
    (Quot.mk _ T0) fun c hc => (hc (Subsingleton.elim _ _)).elim]
  set T := Quot.out (Quot.mk L.W1TorusConj T0)
  haveI := subsingleton_lieTorusW (hbot T)
  have hconst : (fun Y : ↥(L.lieTorusW T.1) => L.geomIntegrand ψ θ τ T.1 Y) =
      fun _ => L.geomIntegrand ψ θ τ T.1 0 :=
    funext fun Y => by rw [Subsingleton.elim Y 0]; rfl
  have hw : L.weylW1 T.1 = 1 := by rw [hbot T]; exact L.weylW1_bot
  rw [hw, Nat.cast_one, inv_one, one_mul, hconst, integral_const,
    muT_real_univ I T (hbot T), one_smul]
  unfold geomIntegrand
  rw [if_pos (isNatW_zero (hbot T)), weylDiscLie_zero_soW, deltaW_zero]
  simp

end LuoDatum

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (ψ : NontrivialAddChar F)
  (d : GGPData F)

open LuoDatum

/-- **Descent near `1` to `(SO(V), SO(W))` when `W` is a hyperbolic plane** (Thesis
Prop 12.4.1(i) and Prop 12.1.1(iv), for this case; own work).  There is an invariant clopen
`Ω ∋ 1` such that for every `f ∈ ScuspTestFn d χ` supported in `Ω` there are data of
Waldspurger 2010 §7.2 for `d.luoOf` (`W1Input`), a quasi-character `θ` on `so(W)(F)` (the
indicator of a small lattice), a very cuspidal `φ` on `so(V)(F)` and its `θ_φ` (`τ`), with
* (i) `J(f) = ∫_{U(F)H(F)\SO(V)(F)} I(θ, φ, g) dg`;
* (ii) if `x ↦ K(f, x)` is integrable on `H(F)\G(F)/A_G(F)`, then `g ↦ I(θ, φ, g)` is
  integrable on `U(F)H(F)\SO(V)(F)`;
* (iii) `m_geom(θ_f) = c_θ(0) c_{θ_φ}(0)`.
Proof plan: `Φ(t, g) = t⁻¹ g` and Hilbert 90 (`quotHG_equiv`); shrink `ω` so that the Jacobians
of `exp` are `1` and `χ ∘ exp = 1` on `ω_W` (`F` is `p`-adic); then choose `ω_V` after `ω_W`, so
small that every `Y ∈ so(W)` with `Y + N ∈ Ad(g) ω_V` for some `N ∈ 𝔲`, `g ∈ SO(V)` lies in `ω_W`
(then `θ = 1_{ω_W}` acts as `1` in the kernel, which is needed to identify `K(f, ·)` with
`I(θ, φ_ω, ·)`); `H ∩ A_G exp(ω) = A_{G,H} exp(ω ∩ 𝔥⁰)` and `χ` is trivial on `A_{G,H}`; the kernel identity `K(f, x) = I(θ, φ_ω, Φ(x))` pointwise for
measures matched through `exp` and the Weil formula (no free constant); strong cuspidality of `f`
gives very cuspidality of `φ_ω`; the descent `(θ_f)_ω = θ_{φ_ω}` near `0` and the collapse of
`Γ(G, H)` to the class of `1` give (iii).  Obligations beyond the descent itself: a `W1Input` for
`d.luoOf` exists (W1 §7.2: a special lattice `R₀` of `V₀` and a lattice `R_Z` with `R₀ ⊕ R_Z`
special can be chosen; the measures exist), unproved here; and the regular germs of quasi-characters
on `so(V)` and `so(W)` are unique (Harish-Chandra 1999 Cor 5.10, as `germLie_unique_SO` for the
product), needed to match `c_θ(0) c_{θ_φ}(0)` with the germ of `θ_f` at `1`.  For `W` a plane,
`Γ(G, H)` is the class of `1`, so `m_geom(θ_f)` is the single regular germ of `θ_f` at `1`;
only its comparison with `c_θ(0) c_{θ_φ}(0)` uses Waldspurger's data.
Status: SORRY. -/
theorem exists_hypW_descent (hW : IsHypPlane d.QW) (χ : CentralCharOn d) :
    ∃ Ω : Set ↥d.G, IsInvariantClopen d Ω ∧ (1 : ↥d.G) ∈ Ω ∧
      ∀ f ∈ ScuspTestFn d χ, Function.support f ⊆ Ω →
        ∃ (I : d.luoOf.W1Input ψ) (θ : ↥d.luoOf.soW → ℂ) (φ τ : ↥d.luoOf.soV → ℂ),
          IsLieQuasiCharacter d.luoOf.SOW d.luoOf.soW d.luoOf.bW ψ θ ∧
          d.luoOf.IsVeryCuspidal φ ∧ d.luoOf.IsThetaFW1 ψ I.μG φ τ ∧
          distribJ d ψ f = ∫ q, I.Ig θ φ (CosetSpace.out d.luoOf.UHbar.subtype q) ∂I.m ∧
          (Integrable (fun q : d.HGQuot => kernelK d ψ f (d.repHG q)) d.weilMeasureHG →
            Integrable (fun q => I.Ig θ φ (CosetSpace.out d.luoOf.UHbar.subtype q)) I.m) ∧
          mGeom ψ d (thetaF d f) = d.luoOf.cThetaW ψ θ 0 * d.luoOf.cFW ψ τ 0 := by
  sorry

/-- **`geomAt_near` when `W` is a hyperbolic plane**, from the descent (`exists_hypW_descent`),
Waldspurger 2010 Thm 7.9 untruncated (`integral_Ig_eq_Igeom`, with the convergence of `J`,
`distribJ_convergent`), and the geometric side for `W` a plane (`Igeom_of_isHypPlane`). -/
theorem geomAt_near_hypW (hW : IsHypPlane d.QW) (χ : CentralCharOn d) :
    ∃ Ω : Set ↥d.G, IsInvariantClopen d Ω ∧ (1 : ↥d.G) ∈ Ω ∧
      ∀ f ∈ ScuspTestFn d χ, Function.support f ⊆ Ω →
        distribJ d ψ f = mGeom ψ d (thetaF d f) := by
  obtain ⟨Ω, hΩ, h1, hdesc⟩ := d.exists_hypW_descent ψ hW χ
  refine ⟨Ω, hΩ, h1, fun f hf hs => ?_⟩
  obtain ⟨I, θ, φ, τ, hθ, hφ, hτ, hJ, hint, hm⟩ := hdesc f hf hs
  have hW' : IsHypPlane d.luoOf.QW := hW
  have hV2 : ¬ IsHypPlane d.luoOf.QV := fun h => by
    have h1 := h.1
    have h2 := hW.1
    simp only [LuoDatum.V, LuoDatum.W, LuoDatum.Zs, Module.finrank_prod, Module.finrank_fin_fun]
      at h1 h2
    have : d.luoOf.m = d.m := rfl
    omega
  rw [hJ, hm,
    integral_Ig_eq_Igeom d.nondeg_QV hV2 I hθ hφ hτ (hint (d.distribJ_convergent χ ψ f hf)),
    Igeom_of_isHypPlane hW' I θ τ]

end GGPData

end GSpinGGP
