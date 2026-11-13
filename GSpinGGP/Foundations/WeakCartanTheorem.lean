/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.WeakCartanFrame
import TauCeti.Analysis.Normed.Module.QuadraticMap

/-!
# The relative Cartan decomposition of `SO(V₀)` with respect to `SO(W)`

Let `b` be an orthogonal basis of anisotropic vectors whose first `l + 1` vectors form a maximal
frame for `ν` (`IsFrame`). For `v₀ = b 0`, `W = v₀^⊥`, `G = SO(Q)` and `H = SO(W) = Stab_G(v₀)`
(`fixer Q b 1`), `relCartan_SO` says: there are compact sets `C_H ⊆ H` and `C ⊆ G` with
`G = C_H · A_H⁻ · A⁻ · C`, where `A` (`multiTorus hb hf 0`) and `A_H` (`multiTorus hb hf 1`)
are the split tori of the frame and `A⁻`, `A_H⁻` their contracting chambers (`InChamber`).
This is the orthogonal analogue of Prop. 11.0.1 in §11 of Beuzart-Plessis's thèse (proved there
for unitary groups), used for the weak Cartan decomposition of Thesis Prop. 8.3.1.

The proof is by downward induction on the level `j` (the group `G_j = fixer Q b j`,
`relCartan_SO_level`), for all frames at once:

* at level `l` the space `span (b l, b (l+1), …)` is anisotropic (`IsFrame.anisotropic`, from
  maximality), so `G_l` is bounded (`exists_bound_fixer_top`);
* `orbit_step`: `G_j = G_{j+1} · a(λ) · C` with `‖λ‖ ≤ 1` (from `orbit_lemma`; directly when
  `span (b j, b (j+1), …)` is a hyperbolic plane);
* the induction hypothesis is applied to the frame `signBasis id b = ((-1)ⁱ b i)`, whose tori are those of `b`
  with inverted parameters, and then inverted; this puts the compact factor of `G_{j+2}` on the
  right, where it commutes with `a(λ)`;
* with at least two pairs, `rotation_lemma` and the norm estimate `norm_param_le` bound `λ` by
  the first coordinate `t₁` of the `G_{j+2}`-torus, `‖λ‖ max(‖t₁‖, ‖t₁‖⁻¹) ≤ C`; after a fixed
  rescaling of `λ` the chamber adjustment `inChamber_cons` applies.

`weakCartan_G0_SO` deduces the weak Cartan decomposition of `SO(W) × SO(V₀)` relative to the
diagonal `SO(W)` (Thesis Prop. 8.3.1 for special orthogonal groups).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Module QuadraticMap

namespace GSpinGGP

namespace WeakCartan

variable {F : Type*} [NontriviallyNormedField F] [CharZero F]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {n : ℕ}
  {b : Module.Basis (Fin n) F V} {Q : QuadraticForm F V}

/-! ## Elementary facts -/

theorem repr_apply_eq_zero_of_mem_fixer (hb : IsOrthoBasis Q b) {j : ℕ} {g : V ≃ₗ[F] V}
    (hg : g ∈ fixer Q b j) {i : Fin n} (hi : i.val < j) {x : V} (hx : b.repr x i = 0) :
    b.repr (g x) i = 0 := by
  rw [hb.repr_eq_polar_div, ← hg.2 i hi,
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (mem_orthogonalGroup_of_mem_fixer hg),
    QuadraticMap.polar_basis_left Q b hb.isOrtho, hx]
  simp

theorem fixer_zero : fixer Q b 0 = TauCeti.QuadraticMap.specialOrthogonalGroup Q := by
  ext g; simp [mem_fixer_iff]

theorem bnd_mul [IsUltrametricDist F] {x y : V ≃ₗ[F] V} {A B : ℝ}
    (hx : basisOpNorm b (x : V →ₗ[F] V) ≤ A) (hy : basisOpNorm b (y : V →ₗ[F] V) ≤ B) :
    basisOpNorm b ((x * y : V ≃ₗ[F] V) : V →ₗ[F] V) ≤ A * B :=
  (basisOpNorm_mul_le x y).trans
    (mul_le_mul hx hy (basisOpNorm_nonneg _) ((basisOpNorm_nonneg _).trans hx))

theorem bnd_inv (hb : IsOrthoBasis Q b) {x : V ≃ₗ[F] V}
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {A : ℝ}
    (hx : basisOpNorm b (x : V →ₗ[F] V) ≤ A) :
    basisOpNorm b ((x⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) ≤ adjBound Q b * A :=
  (hb.basisOpNorm_symm_le hxO).trans
    (mul_le_mul_of_nonneg_left hx (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

/-! ## The anisotropic part at the top level -/

variable {ν : F} {l : ℕ}

/-- The vectors orthogonal to `b 0, …, b (l-1)` form an anisotropic space (maximality of the
frame: a hyperbolic plane represents `(-1)^{l+1} ν`). -/
theorem IsFrame.anisotropic (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l) {x : V}
    (hx : ∀ i : Fin n, i.val < l → b.repr x i = 0) (hQ : Q x = 0) : x = 0 := by
  set il : Fin n := ⟨l, hf.lt⟩
  set c := b.repr x il
  set y := x - c • b il with hy
  have hyl : ∀ i : Fin n, i.val ≤ l → b.repr y i = 0 := by
    intro i hi
    rw [hy, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, b.repr_self]
    rcases lt_or_eq_of_le hi with hi | hi
    · rw [hx i hi, Finsupp.single_apply, ite_eq_right (by simp [il, Fin.ext_iff]; omega)]; simp
    · have : i = il := Fin.ext hi
      subst this; simp [c]
  have hpol : polar Q (b il) y = 0 := by
    rw [QuadraticMap.polar_basis_left Q b hb.isOrtho, hyl il le_rfl, mul_zero]
  have hxy : x = c • b il + y := by rw [hy]; abel
  have hQx : Q x = c * c * Q (b il) + Q y := by
    rw [hxy, QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_left, hpol]; simp
  have hQl : Q (b il) = (-1) ^ l * ν := hf.apply_eq il le_rfl
  by_cases hc : c = 0
  · rw [hc, zero_smul, zero_add] at hxy
    rw [hc] at hQx
    have hQy : Q y = 0 := by rw [← hxy]; exact hQ
    by_contra hx0
    have hy0 : y ≠ 0 := hxy ▸ hx0
    obtain ⟨m, hm⟩ : ∃ m, b.repr y m ≠ 0 := by
      by_contra h; push Not at h
      exact hy0 (b.repr.injective (by ext m; simp [h m]))
    have hml : l < m.val := by
      by_contra h; exact hm (hyl m (by omega))
    have hp : polar Q y (b m) ≠ 0 := by
      rw [polar_comm, QuadraticMap.polar_basis_left Q b hb.isOrtho]
      exact mul_ne_zero (mul_ne_zero two_ne_zero (hb.apply_ne_zero m)) hm
    set α := ((-1) ^ (l + 1) * ν - Q (b m)) / polar Q y (b m)
    refine hf.maximal (α • y + b m) (fun i hi => ?_) ?_
    · rw [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, hyl i hi, b.repr_self,
        Finsupp.single_apply, ite_eq_right (by simp [Fin.ext_iff]; omega)]
      simp
    · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, hQy, polar_smul_left]
      simp only [smul_eq_mul, mul_zero, zero_add, α]
      field_simp
      ring
  · refine absurd ?_ (hf.maximal (c⁻¹ • y) fun i hi => by
      rw [map_smul, Finsupp.smul_apply, hyl i hi, smul_zero])
    rw [QuadraticMap.map_smul, smul_eq_mul]
    have : Q y = -(c * c * Q (b il)) := by linear_combination hQ - hQx
    rw [this, hQl]
    field_simp
    ring

/-- The submodule of coordinate vectors vanishing below `l`. -/
def coordTail (n l : ℕ) : Submodule F (Fin n → F) where
  carrier := {y | ∀ i : Fin n, i.val < l → y i = 0}
  add_mem' hx hy i hi := by simp [hx i hi, hy i hi]
  zero_mem' i _ := rfl
  smul_mem' c x hx i hi := by simp [hx i hi]

variable [IsUltrametricDist F] [LocallyCompactSpace F]

/-- **The top level is bounded**: `G_l` fixes `b 0, …, b (l-1)` and preserves the anisotropic
space they cut out, on which `‖Q‖` is comparable to the squared coordinate norm. -/
theorem exists_bound_fixer_top (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l) :
    ∃ M, ∀ g ∈ fixer Q b l, basisOpNorm b (g : V →ₗ[F] V) ≤ M := by
  have : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let P := coordTail (F := F) n l
  let Q' : QuadraticForm F P := Q.comp (b.equivFun.symm.toLinearMap ∘ₗ P.subtype)
  have hr : ∀ (v : Fin n → F) (i : Fin n), b.repr (b.equivFun.symm v) i = v i := fun v i => by
    rw [← b.equivFun_apply, b.equivFun.apply_symm_apply]
  have hQ' : ∀ y : P, Q' y = ∑ i, (y.1 i) ^ 2 * Q (b i) := fun y => by
    simp only [Q', QuadraticMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearEquiv.coe_coe]
    rw [hb.apply_eq_sum]
    simp only [hr]
  have hcont : Continuous Q' := by
    have : (Q' : P → F) = fun y : P => ∑ i, (y.1 i) ^ 2 * Q (b i) := funext hQ'
    rw [this]
    exact continuous_finsetSum _ fun i _ =>
      (((continuous_apply i).comp continuous_subtype_val).pow 2).mul continuous_const
  have haniso : QuadraticMap.Anisotropic Q' := fun y hy => by
    have h := hf.anisotropic hb (x := b.equivFun.symm y.1) (fun i hi => by
      rw [hr]; exact y.2 i hi) hy
    exact Subtype.ext (b.equivFun.symm.injective (by simpa using h))
  obtain ⟨c, hc, hcle⟩ := QuadraticMap.Anisotropic.exists_pos_mul_norm_sq_le haniso hcont
  refine ⟨max 1 (Real.sqrt (formBound Q b / c)), fun g hg => ?_⟩
  refine (basisOpNorm_le_iff (le_max_of_le_left zero_le_one)).2 fun m => ?_
  rw [LinearEquiv.coe_coe]
  by_cases hm : m.val < l
  · rw [hg.2 m hm, basisNorm_basis]; exact le_max_left _ _
  · refine le_max_of_le_right ?_
    let y : P := ⟨b.equivFun (g (b m)), fun i hi => by
      simpa using repr_apply_eq_zero_of_mem_fixer hb hg hi (x := b m)
        (by rw [b.repr_self, Finsupp.single_apply, ite_eq_right (by simp [Fin.ext_iff]; omega)])⟩
    have h1 := hcle y
    have hQy : Q' y = Q (b m) := by
      simp only [Q', y, QuadraticMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
        (mem_orthogonalGroup_of_mem_fixer hg) _
    have hny : ‖y‖ = basisNorm b (g (b m)) := rfl
    rw [hQy, hny] at h1
    have h2 : c * basisNorm b (g (b m)) ^ 2 ≤ formBound Q b := h1.trans (norm_apply_basis_le m)
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hc]; linarith

/-! ## Compact sets in a level -/

omit [IsUltrametricDist F] [LocallyCompactSpace F] in
theorem isClosed_fixer (j : ℕ) : IsClosed (fixer Q b j : Set (V ≃ₗ[F] V)) := by
  have hev : ∀ i : Fin n, IsClosed {g : V ≃ₗ[F] V | g (b i) = b i} := fun i => by
    let φ : Module.End F V →ₗ[F] (Fin n → F) :=
      b.equivFun.toLinearMap ∘ₗ LinearMap.applyₗ (b i)
    have hφ : Continuous fun g : V ≃ₗ[F] V => φ g :=
      (IsModuleTopology.continuous_of_linearMap φ).comp
        TauCeti.continuous_linearEquiv_toLinearMap
    convert isClosed_eq hφ
      (continuous_const : Continuous fun _ : V ≃ₗ[F] V => b.equivFun (b i)) using 1
    ext g
    simp only [φ, Set.mem_ofPred_eq, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
      LinearEquiv.coe_coe]
    exact b.equivFun.injective.eq_iff.symm
  have : (fixer Q b j : Set (V ≃ₗ[F] V)) =
      (TauCeti.QuadraticMap.specialOrthogonalGroup Q : Set (V ≃ₗ[F] V)) ∩
        ⋂ i : Fin n, ⋂ (_ : i.val < j), {g : V ≃ₗ[F] V | g (b i) = b i} := by
    ext g; simp [mem_fixer_iff]
  rw [this]
  exact (TauCeti.QuadraticMap.isClosed_specialOrthogonalGroup Q).inter
    (isClosed_iInter fun i => isClosed_iInter fun _ => hev i)

/-- The bounded part of a level, a compact set. -/
def fixerBall (Q : QuadraticForm F V) (b : Module.Basis (Fin n) F V) (j : ℕ) (M : ℝ) :
    Set (V ≃ₗ[F] V) :=
  {g | g ∈ fixer Q b j ∧ basisOpNorm b (g : V →ₗ[F] V) ≤ M}

omit [IsUltrametricDist F] in
theorem isCompact_fixerBall (hb : IsOrthoBasis Q b) (j : ℕ) (M : ℝ) :
    IsCompact (fixerBall Q b j M) := by
  convert (isCompact_specialOrthogonal_setOf_basisOpNorm_le hb M).inter_right
    (isClosed_fixer (Q := Q) (b := b) j) using 1
  ext g
  simp only [fixerBall, Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe]
  exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1.1, h2⟩, h1⟩, fun ⟨⟨_, h2⟩, h1⟩ => ⟨h1, h2⟩⟩

/-! ## The orbit step -/

omit [LocallyCompactSpace F] in
/-- **Orbit step.** Every `g ∈ G_j` is `h₀ a(λ) c` with `h₀ ∈ G_{j+1}`, `c ∈ G_j` bounded, and
`‖λ‖ ≤ 1` unless `span (b j, b (j+1), …)` is a hyperbolic plane. -/
theorem orbit_step (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l) {j : ℕ} (hj : j + 1 ≤ l) :
    ∃ M, ∀ g ∈ fixer Q b j, ∃ h₀ ∈ fixer Q b (j + 1), ∃ lam : Fˣ,
      (j + 2 < n → ‖(lam : F)‖ ≤ 1) ∧ ∃ c ∈ fixer Q b j, basisOpNorm b (c : V →ₗ[F] V) ≤ M ∧
        g = h₀ * levelTorus hb hf j lam * c := by
  have hjn : j < n := hf.idx_lt (by omega)
  have hj1n : j + 1 < n := hf.idx_lt hj
  set i₀ : Fin n := ⟨j, hjn⟩
  set i₁ : Fin n := ⟨j + 1, hj1n⟩
  have hne : i₀ ≠ i₁ := idx_ne hjn hj1n
  have h₀ : Q (b i₀) = (-1) ^ j * ν := hf.apply_left hj
  have h₁ : Q (b i₁) = -((-1) ^ j * ν) := hf.apply_right hj
  have hν : (-1) ^ j * ν ≠ 0 := h₀ ▸ hb.apply_ne_zero i₀
  have hA : levelTorus hb hf j = pairTorus hb hne h₀ h₁ := funext fun t =>
    levelTorus_of_le hb hf hj t
  -- the vector `v = g⁻¹ (b j)`
  have hv : ∀ g ∈ fixer Q b j, (∀ k : Fin n, k.val < j → b.repr (g⁻¹ (b i₀)) k = 0) ∧
      Q (g⁻¹ (b i₀)) = (-1) ^ j * ν := fun g hg => by
    refine ⟨fun k hk => repr_apply_eq_zero_of_mem_fixer hb (inv_mem hg) hk ?_, ?_⟩
    · rw [b.repr_self, Finsupp.single_apply, ite_eq_right (by simp [i₀, Fin.ext_iff]; omega)]
    · rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
        (mem_orthogonalGroup_of_mem_fixer (inv_mem hg)), h₀]
  -- assembling `g = h₀ a(λ) c` from `c g⁻¹ (b j) = a(λ)⁻¹ (b j)`
  have hassemble : ∀ g ∈ fixer Q b j, ∀ (lam : Fˣ) (c : V ≃ₗ[F] V), c ∈ fixer Q b j →
      c (g⁻¹ (b i₀)) = (pairTorus hb hne h₀ h₁ lam)⁻¹ (b i₀) →
      g * c⁻¹ * (levelTorus hb hf j lam)⁻¹ ∈ fixer Q b (j + 1) ∧
        g = g * c⁻¹ * (levelTorus hb hf j lam)⁻¹ * levelTorus hb hf j lam * c := by
    intro g hg lam c hc he
    refine ⟨⟨mul_mem (mul_mem hg.1 (inv_mem hc.1)) (inv_mem (levelTorus_mem_fixer hb hf j lam).1),
      fun i hi => ?_⟩, by group⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · exact (mul_mem (mul_mem hg (inv_mem hc)) (inv_mem (levelTorus_mem_fixer hb hf j lam))).2 i hi
    · have : i = i₀ := Fin.ext hi
      subst this
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hA, ← he]
      simp
  by_cases hn : j + 2 < n
  · -- the orbit lemma
    set S' : Finset (Fin n) := Finset.univ.filter fun m => j + 2 ≤ m.val
    have h₀S : i₀ ∉ S' := by simp [S', i₀]
    have h₁S : i₁ ∉ S' := by simp [S', i₁]
    obtain ⟨M, hM⟩ := orbit_lemma hb hne h₀ h₁ h₀S h₁S ⟨⟨j + 2, hn⟩, by simp [S']⟩
    refine ⟨M, fun g hg => ?_⟩
    obtain ⟨hv0, hvQ⟩ := hv g hg
    obtain ⟨c, hcSO, hcM, hcfix, t, ht0, ht1, e⟩ := hM (g⁻¹ (b i₀)) (fun k hk0 hk1 hkS =>
      hv0 k (by simp [S', i₀, i₁, Fin.ext_iff] at hk0 hk1 hkS; omega)) hvQ
    have hc : c ∈ fixer Q b j := ⟨hcSO, fun i hi => hcfix i
      (by simp [i₀, Fin.ext_iff]; omega) (by simp [i₁, Fin.ext_iff]; omega)
      (by simp [S']; omega)⟩
    set lam := Units.mk0 t ht0
    have he : c (g⁻¹ (b i₀)) = (pairTorus hb hne h₀ h₁ lam)⁻¹ (b i₀) := by
      rw [e, pairTorus_inv_apply_left]; rfl
    obtain ⟨hh, hg'⟩ := hassemble g hg lam c hc he
    exact ⟨_, hh, lam, fun _ => ht1, c, hc, hcM, hg'⟩
  · -- a hyperbolic plane
    have hn2 : n = j + 2 := by omega
    refine ⟨1, fun g hg => ?_⟩
    obtain ⟨hv0, hvQ⟩ := hv g hg
    set v := g⁻¹ (b i₀)
    set x := b.repr v i₀
    set y := b.repr v i₁
    have hother : ∀ k : Fin n, k ≠ i₀ → k ≠ i₁ → b.repr v k = 0 := fun k hk0 hk1 =>
      hv0 k (by simp [i₀, i₁, Fin.ext_iff] at hk0 hk1; omega)
    have hQv : x * x - y * y = 1 := by
      have := hb.apply_eq_sum v
      rw [Fintype.sum_eq_add i₀ i₁ hne (fun k ⟨hk0, hk1⟩ => by rw [hother k hk0 hk1]; ring),
        h₀, h₁, hvQ] at this
      have h' : ((-1) ^ j * ν) * (x * x - y * y - 1) = 0 := by linear_combination -this
      have := (mul_eq_zero.1 h').resolve_left hν
      linear_combination this
    have ht0 : x - y ≠ 0 := fun h => by
      have : (x - y) * (x + y) = 1 := by linear_combination hQv
      rw [h, zero_mul] at this; exact zero_ne_one this
    set lam := Units.mk0 (x - y) ht0
    have hinv : (lam : F)⁻¹ = x + y := by
      rw [Units.val_mk0]
      exact inv_eq_of_mul_eq_one_right (by linear_combination hQv)
    have he : (1 : V ≃ₗ[F] V) (g⁻¹ (b i₀)) = (pairTorus hb hne h₀ h₁ lam)⁻¹ (b i₀) := by
      rw [pairTorus_inv_apply_left]
      change v = _
      refine b.repr.injective (Finsupp.ext fun k => ?_)
      simp only [map_add, map_smul, map_sub, Finsupp.add_apply, Finsupp.smul_apply,
        Finsupp.sub_apply, b.repr_self, Finsupp.single_apply, smul_eq_mul]
      rw [mul_inv, hinv]
      by_cases hk0 : k = i₀
      · subst hk0
        simp only [ite_eq_right hne.symm]
        change x = _
        field_simp
        simp only [ite_true]
        rw [show (lam : F) = x - y from rfl]; ring
      by_cases hk1 : k = i₁
      · subst hk1
        simp only [ite_eq_right hne]
        change y = _
        field_simp
        simp only [ite_true]
        rw [show (lam : F) = x - y from rfl]; ring
      rw [hother k hk0 hk1, ite_eq_right (Ne.symm hk0), ite_eq_right (Ne.symm hk1)]; ring
    obtain ⟨hh, hg'⟩ := hassemble g hg lam 1 (one_mem _) he
    refine ⟨_, hh, lam, fun h => absurd h hn, 1, one_mem _, basisOpNorm_id_le, ?_⟩
    simp

/-! ## The norm estimate for the parameter `λ` -/

omit [IsUltrametricDist F] [LocallyCompactSpace F] in
theorem multiTorus_cons_apply_left (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l) {j : ℕ}
    (hj : j + 1 ≤ l) (t : Fˣ) (ts : List Fˣ) :
    multiTorus hb hf j (t :: ts) (b ⟨j, hf.idx_lt (by omega)⟩) =
      (((t : F) + (t : F)⁻¹) / 2) • b ⟨j, hf.idx_lt (by omega)⟩ +
        (((t : F) - (t : F)⁻¹) / 2) • b ⟨j + 1, hf.idx_lt hj⟩ := by
  have hfix := multiTorus_mem_fixer hb hf ts (j + 2)
  rw [multiTorus_cons, LinearEquiv.mul_apply, levelTorus_of_le hb hf hj, pairTorus_apply_left,
    map_add, map_smul, map_smul, hfix.2 _ (by simp), hfix.2 _ (by simp)]

omit [IsUltrametricDist F] [LocallyCompactSpace F] in
theorem multiTorus_cons_apply_pair (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l) {j : ℕ}
    (hj : j + 1 ≤ l) (t : Fˣ) (ts : List Fˣ) :
    multiTorus hb hf j (t :: ts) (b ⟨j, hf.idx_lt (by omega)⟩ + b ⟨j + 1, hf.idx_lt hj⟩) =
      (t : F) • (b ⟨j, hf.idx_lt (by omega)⟩ + b ⟨j + 1, hf.idx_lt hj⟩) := by
  have hfix := multiTorus_mem_fixer hb hf ts (j + 2)
  have e0 := hfix.2 ⟨j, hf.idx_lt (by omega)⟩ (by simp)
  have e1 := hfix.2 ⟨j + 1, hf.idx_lt hj⟩ (by simp)
  rw [multiTorus_cons, LinearEquiv.mul_apply, levelTorus_of_le hb hf hj, map_add,
    pairTorus_apply_left, pairTorus_apply_right]
  simp only [map_add, map_smul, e0, e1]
  have ht : (t : F) ≠ 0 := t.ne_zero
  rw [smul_add]
  module

/-- **The norm estimate.** Let `h = k · a_{j+1}(s, …) · a_{j+2}(t, …) · k'` with `k ∈ G_{j+1}`,
`k' ∈ G_{j+2}` of norm at most `M` and the torus parameters in their chambers, and suppose
`ε ‖λ‖ ‖h‖ ≤ ‖h (b (j+1))‖` (the output of `rotation_lemma`). Then
`‖λ‖ max(‖t‖, ‖t‖⁻¹) ≤ C` with `C` depending only on `M` and `ε`. -/
theorem norm_param_le (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l) {j : ℕ} (hj : j + 3 ≤ l)
    {M ε : ℝ} (hε : 0 < ε) {lam : Fˣ} (hlam : ‖(lam : F)‖ ≤ 1) {k k' : V ≃ₗ[F] V}
    (hk : k ∈ fixer Q b (j + 1)) (hkM : basisOpNorm b (k : V →ₗ[F] V) ≤ M)
    (hk' : k' ∈ fixer Q b (j + 2)) (hk'M : basisOpNorm b (k' : V →ₗ[F] V) ≤ M)
    {s t : Fˣ} {ss ts : List Fˣ} (hs : InChamber n l (j + 1) (s :: ss))
    (hrot : ε * ‖(lam : F)‖ * basisOpNorm b ((k * multiTorus hb hf (j + 1) (s :: ss) *
        multiTorus hb hf (j + 2) (t :: ts) * k' : V ≃ₗ[F] V) : V →ₗ[F] V) ≤
      basisNorm b ((k * multiTorus hb hf (j + 1) (s :: ss) * multiTorus hb hf (j + 2) (t :: ts) *
        k') (b ⟨j + 1, hf.idx_lt (by omega)⟩))) :
    ‖(lam : F)‖ * ‖(t : F)‖ ≤ M * max (adjBound Q b * M * M * ‖(2 : F)‖⁻¹ * ε⁻¹) 1 ∧
      ‖(lam : F)‖ * ‖(t : F)‖⁻¹ ≤ M * max (adjBound Q b * M * M * ‖(2 : F)‖⁻¹ * ε⁻¹) 1 := by
  set w₁ := b ⟨j + 1, hf.idx_lt (by omega)⟩
  set w₂ := b ⟨j + 2, hf.idx_lt (by omega)⟩
  set w₃ := b ⟨j + 3, hf.idx_lt (by omega)⟩
  set aH := multiTorus hb hf (j + 1) (s :: ss)
  set a' := multiTorus hb hf (j + 2) (t :: ts)
  set h := k * aH * a' * k' with hh
  set κ := adjBound Q b
  have hκ : 0 ≤ κ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hM : 0 ≤ M := (basisOpNorm_nonneg _).trans hkM
  have h2 : 0 < ‖(2 : F)‖⁻¹ := inv_pos.2 (norm_pos_iff.2 two_ne_zero)
  have hs0 : 0 < ‖(s : F)‖ := norm_pos_iff.2 s.ne_zero
  have hlam0 : 0 < ‖(lam : F)‖ := norm_pos_iff.2 lam.ne_zero
  have hs1 : ‖(s : F)‖ ≤ 1 := hs.norm_head_le_one hj hf.lt
  have ha'fix := multiTorus_mem_fixer hb hf (t :: ts) (j + 2)
  have ha'1 : a' w₁ = w₁ := ha'fix.2 _ (by simp)
  have hk'1 : k' w₁ = w₁ := hk'.2 _ (by simp)
  -- (i) `‖h w₁‖ ≤ M ‖2‖⁻¹ ‖s‖⁻¹`
  have haHw : aH w₁ = (((s : F) + (s : F)⁻¹) / 2) • w₁ + (((s : F) - (s : F)⁻¹) / 2) • w₂ :=
    multiTorus_cons_apply_left hb hf (j := j + 1) (by omega) s ss
  have hmax : max ‖(s : F)‖ ‖(s : F)‖⁻¹ = ‖(s : F)‖⁻¹ :=
    max_eq_right (hs1.trans (one_le_inv₀ hs0 |>.2 hs1))
  have hnaH : basisNorm b (aH w₁) ≤ ‖(2 : F)‖⁻¹ * ‖(s : F)‖⁻¹ := by
    have hc1 := norm_add_inv_div_two_le s 1 norm_one
    have hc2 := norm_add_inv_div_two_le s (-1) (by simp)
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg, hmax] at hc1 hc2
    rw [haHw]
    refine (basisNorm_add_le _ _).trans (max_le ?_ ?_) <;>
      rw [basisNorm_smul, basisNorm_basis, mul_one] <;> assumption
  have hhw : h w₁ = k (aH w₁) := by
    simp only [hh, LinearEquiv.mul_apply, hk'1, ha'1]
  have hnh1 : basisNorm b (h w₁) ≤ M * (‖(2 : F)‖⁻¹ * ‖(s : F)‖⁻¹) := by
    rw [hhw]
    exact (basisNorm_apply_le _ _).trans (mul_le_mul hkM hnaH (basisNorm_nonneg _) hM)
  -- (iii) the bound on `‖h⁻¹‖`
  have hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    mem_orthogonalGroup_of_mem_fixer (mul_mem (mul_mem (mul_mem (fixer_anti (by omega) hk)
      (multiTorus_mem_fixer hb hf _ (j + 1))) (fixer_anti (by omega) ha'fix))
      (fixer_anti (by omega) hk'))
  have hhinv := hb.basisOpNorm_symm_le hhO
  have hkey : ‖(lam : F)‖ * basisOpNorm b (h : V →ₗ[F] V) ≤
      ε⁻¹ * (M * (‖(2 : F)‖⁻¹ * ‖(s : F)‖⁻¹)) := by
    rw [le_inv_mul_iff₀ hε, ← mul_assoc]; exact hrot.trans hnh1
  -- (ii) `x = k'⁻¹ a'⁻¹ w₂ = s h⁻¹ k (w₁ + w₂) - w₁`
  have hid : h⁻¹ * k * aH = k'⁻¹ * a'⁻¹ := by simp only [hh]; group
  have hpair : aH (w₁ + w₂) = (s : F) • (w₁ + w₂) :=
    multiTorus_cons_apply_pair hb hf (j := j + 1) (by omega) s ss
  have e1 : (k'⁻¹ * a'⁻¹) (w₁ + w₂) = (s : F) • h⁻¹ (k (w₁ + w₂)) := by
    rw [← hid, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hpair, map_smul, map_smul]
  have e2 : (k'⁻¹ * a'⁻¹) w₁ = w₁ := by
    rw [LinearEquiv.mul_apply, (inv_mem ha'fix).2 _ (by simp), (inv_mem hk').2 _ (by simp)]
  set x := (k'⁻¹ * a'⁻¹) w₂
  have hx : x = (s : F) • h⁻¹ (k (w₁ + w₂)) - w₁ := by
    rw [← e1, map_add, e2]; abel
  have hw12 : basisNorm b (w₁ + w₂) ≤ 1 :=
    (basisNorm_add_le _ _).trans (by simp [w₁, w₂])
  set C₀ := max (κ * M * M * ‖(2 : F)‖⁻¹ * ε⁻¹) 1
  have hnx : ‖(lam : F)‖ * basisNorm b x ≤ C₀ := by
    rw [hx]
    have hA : basisNorm b (h⁻¹ (k (w₁ + w₂))) ≤ κ * basisOpNorm b (h : V →ₗ[F] V) * M := by
      refine (basisNorm_apply_le ((h⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) _).trans ?_
      refine mul_le_mul (hhinv.trans le_rfl) ?_ (basisNorm_nonneg _)
        (mul_nonneg hκ (basisOpNorm_nonneg _))
      exact (basisNorm_apply_le _ _).trans ((mul_le_mul_of_nonneg_left hw12
        (basisOpNorm_nonneg _)).trans (by rw [mul_one]; exact hkM))
    refine (mul_le_mul_of_nonneg_left (basisNorm_sub_le _ _) hlam0.le).trans ?_
    rw [mul_max_of_nonneg _ _ hlam0.le, basisNorm_basis, mul_one]
    refine max_le (le_max_of_le_left ?_) (le_max_of_le_right hlam)
    rw [basisNorm_smul]
    calc ‖(lam : F)‖ * (‖(s : F)‖ * basisNorm b (h⁻¹ (k (w₁ + w₂))))
        ≤ ‖(lam : F)‖ * (‖(s : F)‖ * (κ * basisOpNorm b (h : V →ₗ[F] V) * M)) := by gcongr
      _ = ‖(s : F)‖ * κ * M * (‖(lam : F)‖ * basisOpNorm b (h : V →ₗ[F] V)) := by ring
      _ ≤ ‖(s : F)‖ * κ * M * (ε⁻¹ * (M * (‖(2 : F)‖⁻¹ * ‖(s : F)‖⁻¹))) := by gcongr
      _ = κ * M * M * ‖(2 : F)‖⁻¹ * ε⁻¹ := by field_simp
  -- `a'⁻¹ w₂ = k' x`
  have hk'x : a'⁻¹ w₂ = k' x := by
    change _ = k' ((k'⁻¹ * a'⁻¹) w₂)
    rw [← LinearEquiv.mul_apply, mul_inv_cancel_left]
  have hn2 : ‖(lam : F)‖ * basisNorm b (a'⁻¹ w₂) ≤ M * C₀ := by
    rw [hk'x]
    calc ‖(lam : F)‖ * basisNorm b (k' x) ≤ ‖(lam : F)‖ * (M * basisNorm b x) :=
          mul_le_mul_of_nonneg_left ((basisNorm_apply_le _ _).trans
            (mul_le_mul_of_nonneg_right hk'M (basisNorm_nonneg _))) hlam0.le
      _ = M * (‖(lam : F)‖ * basisNorm b x) := by ring
      _ ≤ M * C₀ := mul_le_mul_of_nonneg_left hnx hM
  -- (iv) `max(‖t‖, ‖t‖⁻¹) ≤ ‖a'⁻¹ w₂‖`
  have ha'inv : a'⁻¹ w₂ = (((t : F)⁻¹ + t) / 2) • w₂ + (((t : F)⁻¹ - t) / 2) • w₃ := by
    rw [← multiTorus_map_inv, List.map_cons,
      multiTorus_cons_apply_left hb hf (j := j + 2) (by omega)]
    simp only [Units.val_inv_eq_inv_val, inv_inv]
    rfl
  set c0 : F := ((t : F)⁻¹ + t) / 2
  set c1 : F := ((t : F)⁻¹ - t) / 2
  have hc0 : ‖c0‖ ≤ basisNorm b (a'⁻¹ w₂) := by
    refine le_trans (le_of_eq ?_) (norm_repr_le_basisNorm _ ⟨j + 2, hf.idx_lt (by omega)⟩)
    rw [ha'inv]; simp [w₂, w₃, Fin.ext_iff]
  have hc1 : ‖c1‖ ≤ basisNorm b (a'⁻¹ w₂) := by
    refine le_trans (le_of_eq ?_) (norm_repr_le_basisNorm _ ⟨j + 3, hf.idx_lt (by omega)⟩)
    rw [ha'inv]; simp [w₂, w₃, Fin.ext_iff]
  have ht : ‖(t : F)‖ ≤ basisNorm b (a'⁻¹ w₂) := by
    have : (t : F) = c0 + -c1 := by simp only [c0, c1]; ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hc0 (by rw [norm_neg]; exact hc1))
  have ht' : ‖(t : F)‖⁻¹ ≤ basisNorm b (a'⁻¹ w₂) := by
    have : (t : F)⁻¹ = c0 + c1 := by simp only [c0, c1]; ring
    rw [← norm_inv, this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hc0 hc1)
  exact ⟨(mul_le_mul_of_nonneg_left ht hlam0.le).trans hn2,
    (mul_le_mul_of_nonneg_left ht' hlam0.le).trans hn2⟩

/-! ## The induction -/

omit [IsUltrametricDist F] [LocallyCompactSpace F] in
theorem exists_cons_of_inChamber {n l j : ℕ} {ts : List Fˣ} (h : InChamber n l j ts)
    (hl : j + 1 ≤ l) : ∃ t ts', ts = t :: ts' := by
  cases ts with
  | nil => have := h.1; simp [numPairs] at this; omega
  | cons t ts' => exact ⟨t, ts', rfl⟩

/-- **The relative Cartan decomposition at level `j`, with bounds.** For every frame and every
level `j ≤ l` there is `M` such that every `g ∈ G_j` is `k · a_{j+1}(s) · a_j(t) · c` with
`k ∈ G_{j+1}`, `c ∈ G_j` of norm at most `M` and `s`, `t` in the contracting chambers. -/
theorem relCartan_SO_level_bdd (d : ℕ) :
    ∀ (b : Module.Basis (Fin n) F V) (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l) (j : ℕ),
      j + d = l → ∃ M, ∀ g ∈ fixer Q b j, ∃ k ∈ fixer Q b (j + 1),
        basisOpNorm b (k : V →ₗ[F] V) ≤ M ∧ ∃ s, InChamber n l (j + 1) s ∧
          ∃ t, InChamber n l j t ∧ ∃ c ∈ fixer Q b j, basisOpNorm b (c : V →ₗ[F] V) ≤ M ∧
            g = k * multiTorus hb hf (j + 1) s * multiTorus hb hf j t * c := by
  induction d with
  | zero =>
    intro b hb hf j hjl
    obtain ⟨M, hM⟩ := exists_bound_fixer_top hb hf
    have hjl' : j = l := by omega
    subst hjl'
    refine ⟨max M 1, fun g hg => ⟨1, one_mem _, basisOpNorm_id_le.trans (le_max_right _ _),
      [], inChamber_nil (by omega), [], inChamber_nil le_rfl, g, hg,
      (hM g hg).trans (le_max_left _ _), by simp⟩⟩
  | succ d ih =>
    intro b hb hf j hjl
    have hj : j + 1 ≤ l := by omega
    set κ := adjBound Q b
    have hκ : 0 ≤ κ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    -- the induction hypothesis for the frame with alternating signs, inverted
    obtain ⟨M₂', hM₂'⟩ := ih (signBasis id b) (hb.signBasis id) (hf.signBasis id) (j + 1) (by omega)
    obtain ⟨M₂, hM₂⟩ := exists_basisOpNorm_le_of_isCompact (b := b)
      (isCompact_specialOrthogonal_setOf_basisOpNorm_le (hb.signBasis id) M₂')
    have hdec : ∀ h ∈ fixer Q b (j + 1), ∃ k ∈ fixer Q b (j + 1),
        basisOpNorm b (k : V →ₗ[F] V) ≤ κ * M₂ ∧ ∃ s, InChamber n l (j + 1) s ∧
          ∃ t, InChamber n l (j + 2) t ∧ ∃ k' ∈ fixer Q b (j + 2),
            basisOpNorm b (k' : V →ₗ[F] V) ≤ κ * M₂ ∧
              h = k * multiTorus hb hf (j + 1) s * multiTorus hb hf (j + 2) t * k' := by
      intro h hh
      have hodd : ∀ i k, Odd (id (i + 2 * k) + id (i + 2 * k + 1)) := fun i k =>
        ⟨i + 2 * k, by simp only [id]; ring⟩
      rw [← fixer_signBasis id] at hh
      obtain ⟨k₁, hk₁, hk₁M, s₁, hs₁, s₂, hs₂, c₁, hc₁, hc₁M, he⟩ := hM₂' h⁻¹ (inv_mem hh)
      have hk₁' : k₁ ∈ fixer Q b (j + 2) := by rw [← fixer_signBasis id]; exact hk₁
      have hc₁' : c₁ ∈ fixer Q b (j + 1) := by rw [← fixer_signBasis id]; exact hc₁
      rw [multiTorus_signBasis_of_odd id hb hf _ _ (hodd _),
        multiTorus_signBasis_of_odd id hb hf _ _ (hodd _), multiTorus_map_inv hb hf,
        multiTorus_map_inv hb hf] at he
      refine ⟨c₁⁻¹, inv_mem hc₁', bnd_inv hb (mem_orthogonalGroup_of_mem_fixer hc₁')
        (hM₂ c₁ ⟨hc₁.1, hc₁M⟩), s₂, hs₂, s₁, hs₁, k₁⁻¹, inv_mem hk₁',
        bnd_inv hb (mem_orthogonalGroup_of_mem_fixer hk₁') (hM₂ k₁ ⟨hk₁.1, hk₁M⟩), ?_⟩
      rw [← inv_inv h, he]
      group
    obtain ⟨M₁, hM₁⟩ := orbit_step hb hf hj
    by_cases hl : l ≤ j + 2
    · -- one pair at level `j`
      refine ⟨max (κ * M₂) (κ * M₂ * M₁), fun g hg => ?_⟩
      obtain ⟨h₀, hh₀, lam, hlam, c, hc, hcM, rfl⟩ := hM₁ g hg
      obtain ⟨k, hk, hkM, s, hs, t, ht, k', hk', hk'M, rfl⟩ := hdec h₀ hh₀
      have ht0 : t = [] := List.eq_nil_of_length_eq_zero (by rw [ht.1]; simp [numPairs]; omega)
      subst ht0
      refine ⟨k, hk, hkM.trans (le_max_left _ _), s, hs, [lam], inChamber_single hj hl hlam,
        k' * c, mul_mem (fixer_anti (by omega) hk') hc, (bnd_mul hk'M hcM).trans
          (le_max_right _ _), ?_⟩
      have hcomm := levelTorus_commute hb hf hk' lam
      rw [multiTorus_cons, multiTorus_nil]
      simp only [mul_one, one_mul, mul_assoc]
      rw [← mul_assoc k', hcomm, mul_assoc]
    · -- at least two pairs at level `j`
      have hj3 : j + 3 ≤ l := by omega
      have hjn : j < n := hf.idx_lt (by omega)
      have hj1n : j + 1 < n := hf.idx_lt hj
      set i₀ : Fin n := ⟨j, hjn⟩
      set i₁ : Fin n := ⟨j + 1, hj1n⟩
      have hne : i₀ ≠ i₁ := idx_ne hjn hj1n
      have h₀ : Q (b i₀) = (-1) ^ j * ν := hf.apply_left hj
      have h₁ : Q (b i₁) = -((-1) ^ j * ν) := hf.apply_right hj
      set S' : Finset (Fin n) := Finset.univ.filter fun m => j + 2 ≤ m.val
      have h₀S : i₀ ∉ S' := by simp [S', i₀]
      have hA : ∀ t, levelTorus hb hf j t = pairTorus hb hne h₀ h₁ t := fun t =>
        levelTorus_of_le hb hf hj t
      obtain ⟨ε, hε, hrotl⟩ := rotation_lemma hb hne h₀ h₁ (S' := S') h₀S
      set C := κ * M₂ * max (κ * (κ * M₂) * (κ * M₂) * ‖(2 : F)‖⁻¹ * ε⁻¹) 1
      obtain ⟨π, hπ0, hπ⟩ := NormedField.exists_norm_lt F
        (r := min 1 (|C| + 1)⁻¹) (lt_min one_pos (inv_pos.2 (by positivity)))
      have hπ0' : π ≠ 0 := norm_pos_iff.1 hπ0
      set πu := Units.mk0 π hπ0'
      have hπ1 : ‖π‖ ≤ 1 := (hπ.trans_le (min_le_left _ _)).le
      have hπC : ‖π‖ * C ≤ 1 := by
        have h1 : ‖π‖ * (|C| + 1) < 1 := by
          have := hπ.trans_le (min_le_right _ _)
          have hpos : 0 < |C| + 1 := by positivity
          calc ‖π‖ * (|C| + 1) < (|C| + 1)⁻¹ * (|C| + 1) := mul_lt_mul_of_pos_right this hpos
            _ = 1 := inv_mul_cancel₀ hpos.ne'
        nlinarith [le_abs_self C, norm_nonneg π]
      set B := ‖(2 : F)‖⁻¹ * max ‖((πu⁻¹ : Fˣ) : F)‖ ‖((πu⁻¹ : Fˣ) : F)‖⁻¹
      refine ⟨max (κ * M₂) (B * (κ * M₂) * (κ * ‖(2 : F)‖⁻¹) * M₁), fun g hg => ?_⟩
      obtain ⟨h₀', hh₀, lam, hlam, c, hc, hcM, rfl⟩ := hM₁ g hg
      have hlam1 := hlam (by have := hf.lt; omega)
      have hfixS : ∀ x ∈ fixer Q b (j + 1), ∀ m, m ≠ i₁ → m ∉ S' → x (b m) = b m :=
        fun x hx m hm1 hmS => hx.2 m (by
          simp [S', i₁, Fin.ext_iff] at hm1 hmS; omega)
      obtain ⟨γ, hγSO, hγfix, hγM, -, hγrot⟩ :=
        hrotl h₀' (mem_orthogonalGroup_of_mem_fixer hh₀) (hfixS h₀' hh₀) lam hlam1
      have hγ : γ ∈ fixer Q b (j + 1) := ⟨hγSO, fun m hm => hγfix m
        (by simp [i₁, Fin.ext_iff]; omega) (by simp [S']; omega)⟩
      obtain ⟨k, hk, hkM, s₂, hs₂, s₁, hs₁, k', hk', hk'M, he⟩ :=
        hdec (h₀' * γ) (mul_mem hh₀ hγ)
      obtain ⟨s, ss, rfl⟩ := exists_cons_of_inChamber hs₂ (by omega)
      obtain ⟨t, ts, rfl⟩ := exists_cons_of_inChamber hs₁ (by omega)
      rw [he] at hγrot
      obtain ⟨hC1, hC2⟩ := norm_param_le hb hf hj3 hε hlam1 hk hkM hk' hk'M hs₂ hγrot
      set lam' := πu * lam
      have hlam'n : ‖((lam' : Fˣ) : F)‖ = ‖π‖ * ‖(lam : F)‖ := by
        simp [lam', πu, norm_mul]
      have ht0 : 0 < ‖(t : F)‖ := norm_pos_iff.2 t.ne_zero
      have hlam0 : 0 ≤ ‖(lam : F)‖ := norm_nonneg _
      have hch : InChamber n l j (lam' :: t :: ts) := by
        refine inChamber_cons hj hs₁ ?_ ?_ ?_ <;> rw [hlam'n]
        · nlinarith [norm_nonneg π]
        · have h2 : ‖(lam : F)‖ ≤ C * ‖(t : F)‖ := by
            have := hC2; rw [← div_eq_mul_inv, div_le_iff₀ ht0] at this; exact this
          calc ‖π‖ * ‖(lam : F)‖ ≤ ‖π‖ * (C * ‖(t : F)‖) :=
                mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
            _ = (‖π‖ * C) * ‖(t : F)‖ := by ring
            _ ≤ 1 * ‖(t : F)‖ := mul_le_mul_of_nonneg_right hπC ht0.le
            _ = ‖(t : F)‖ := one_mul _
        · calc ‖π‖ * ‖(lam : F)‖ * ‖(t : F)‖ = ‖π‖ * (‖(lam : F)‖ * ‖(t : F)‖) := by ring
            _ ≤ ‖π‖ * C := mul_le_mul_of_nonneg_left hC1 (norm_nonneg _)
            _ ≤ 1 := hπC
      set A := levelTorus hb hf j lam
      set c₂ := A⁻¹ * γ * A
      have hc₂O : c₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
        mem_orthogonalGroup_of_mem_fixer (mul_mem (mul_mem (inv_mem
          (levelTorus_mem_fixer hb hf j lam)) (fixer_anti (by omega) hγ))
          (levelTorus_mem_fixer hb hf j lam))
      have hc₂M : basisOpNorm b (c₂ : V →ₗ[F] V) ≤ ‖(2 : F)‖⁻¹ := by
        simp only [c₂, A, hA]; exact hγM
      have hBM : basisOpNorm b (levelTorus hb hf j πu⁻¹ : V →ₗ[F] V) ≤ B := by
        rw [hA]; exact basisOpNorm_pairTorus_le hb hne h₀ h₁ _
      refine ⟨k, hk, hkM.trans (le_max_left _ _), s :: ss, hs₂, lam' :: t :: ts, hch,
        levelTorus hb hf j πu⁻¹ * k' * c₂⁻¹ * c,
        mul_mem (mul_mem (mul_mem (levelTorus_mem_fixer hb hf j _)
          (fixer_anti (by omega) hk')) (inv_mem (mul_mem (mul_mem (inv_mem
            (levelTorus_mem_fixer hb hf j lam)) (fixer_anti (by omega) hγ))
            (levelTorus_mem_fixer hb hf j lam)))) hc,
        ((bnd_mul (bnd_mul (bnd_mul hBM hk'M) (bnd_inv hb hc₂O hc₂M)) hcM)).trans
          (le_max_right _ _), ?_⟩
      have hL : levelTorus hb hf j lam' = A * (levelTorus hb hf j πu⁻¹)⁻¹ := by
        rw [← levelTorus_inv, inv_inv, ← levelTorus_mul]
        congr 1
        exact mul_comm _ _
      have hAk : A * k' = k' * A := (levelTorus_commute hb hf hk' lam).symm
      have hh₀' : h₀' = k * multiTorus hb hf (j + 1) (s :: ss) *
          multiTorus hb hf (j + 2) (t :: ts) * k' * γ⁻¹ := by
        rw [← he]; group
      rw [hh₀', multiTorus_cons hb hf j, hL]
      simp only [c₂, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
      rw [← mul_assoc A k', hAk]
      simp only [mul_assoc, mul_inv_cancel_left]

/-- **The relative Cartan decomposition at level `j`.** For a maximal frame and `j ≤ l` there
are compact sets `C_H ⊆ G_{j+1}` and `C ⊆ G_j` with `G_j = C_H · A_{j+1}⁻ · A_j⁻ · C`. -/
theorem relCartan_SO_level (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l) {j : ℕ}
    (hj : j ≤ l) :
    ∃ C_H C : Set (V ≃ₗ[F] V), IsCompact C_H ∧ C_H ⊆ fixer Q b (j + 1) ∧ IsCompact C ∧
      C ⊆ fixer Q b j ∧ ∀ g ∈ fixer Q b j, ∃ k ∈ C_H, ∃ s, InChamber n l (j + 1) s ∧
        ∃ t, InChamber n l j t ∧ ∃ c ∈ C,
          g = k * multiTorus hb hf (j + 1) s * multiTorus hb hf j t * c := by
  obtain ⟨M, hM⟩ := relCartan_SO_level_bdd (l - j) b hb hf j (by omega)
  refine ⟨fixerBall Q b (j + 1) M, fixerBall Q b j M, isCompact_fixerBall hb _ _,
    fun _ h => h.1, isCompact_fixerBall hb _ _, fun _ h => h.1, fun g hg => ?_⟩
  obtain ⟨k, hk, hkM, s, hs, t, ht, c, hc, hcM, he⟩ := hM g hg
  exact ⟨k, ⟨hk, hkM⟩, s, hs, t, ht, c, ⟨hc, hcM⟩, he⟩

/-- **The relative Cartan decomposition of `SO(V₀)` with respect to `SO(W)`** (the orthogonal
analogue of Prop. 11.0.1 in §11 of Beuzart-Plessis's thèse; used for Thesis Prop. 8.3.1).
Let `b` be an orthogonal basis of anisotropic vectors of `(V₀, Q)` whose first `l + 1` vectors
form a maximal frame `w₀ = v₀, w₁, …, w_l` (`Q wᵢ = (-1)ⁱ ν`). Let `H = SO(W)`, `W = v₀^⊥`, be
the stabilizer of `v₀ = b 0` in `G = SO(Q)` (`fixer Q b 1`), and `A` (`multiTorus hb hf 0`),
`A_H` (`multiTorus hb hf 1`) the split tori of `G` and `H` defined by the frame, acting on
`w_{2i} ± w_{2i+1}`, resp. `w_{2i+1} ± w_{2i+2}`, by `tᵢ^{±1}`. There are compact sets
`C_H ⊆ H` and `C ⊆ G` with `G = C_H · A_H⁻ · A⁻ · C`, where `A⁻`, `A_H⁻` are the chambers
contracting the flags `⟨u₁⟩ ⊂ ⟨u₁, u₂⟩ ⊂ ⋯` (`InChamber`). -/
theorem relCartan_SO (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l) :
    ∃ C_H C : Set (V ≃ₗ[F] V), IsCompact C_H ∧ C_H ⊆ fixer Q b 1 ∧ IsCompact C ∧
      C ⊆ TauCeti.QuadraticMap.specialOrthogonalGroup Q ∧
        ∀ g ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q, ∃ k ∈ C_H,
          ∃ s, InChamber n l 1 s ∧ ∃ t, InChamber n l 0 t ∧ ∃ c ∈ C,
            g = k * multiTorus hb hf 1 s * multiTorus hb hf 0 t * c := by
  obtain ⟨C_H, C, h1, h2, h3, h4, h5⟩ := relCartan_SO_level hb hf (Nat.zero_le l)
  rw [fixer_zero] at h4 h5
  exact ⟨C_H, C, h1, h2, h3, h4, h5⟩

/-! ## The weak Cartan decomposition of `SO(W) × SO(V₀)` -/

/-- **The weak Cartan decomposition of `G₀ = SO(W) × SO(V₀)`** (Thesis Prop. 8.3.1 for the
special orthogonal groups, for the pair of minimal parabolics stabilizing the flags of `A_H` and
`A`). Elements of `G₀` are written as pairs `(x, y)` with `x ∈ H = SO(W)` (`fixer Q b 1`) and
`y ∈ SO(V₀)`; `H₀ = SO(W)` is embedded diagonally. With `A₀ = A_H × A` and
`A₀⁺ = (A_H⁻)⁻¹ × (A⁻)⁻¹` (the chamber expanding both flags), there are compact sets
`C_H ⊆ H`, `C ⊆ SO(V₀)` with `(x, y) ∈ (h, h) · A₀⁺ · (C_H × C)`. The proof applies
`relCartan_SO` to the frame with signs `+, −, −, +, +, −, −, …`, which reverses the flag of `A`
and keeps that of `A_H`, to `x⁻¹ y`. -/
theorem weakCartan_G0_SO (hb : IsOrthoBasis Q b) (hf : IsFrame Q b ν l) :
    ∃ C_H C : Set (V ≃ₗ[F] V), IsCompact C_H ∧ C_H ⊆ fixer Q b 1 ∧ IsCompact C ∧
      C ⊆ TauCeti.QuadraticMap.specialOrthogonalGroup Q ∧
        ∀ x ∈ fixer Q b 1, ∀ y ∈ TauCeti.QuadraticMap.specialOrthogonalGroup Q,
          ∃ h ∈ fixer Q b 1, ∃ s, InChamber n l 1 s ∧ ∃ t, InChamber n l 0 t ∧
            ∃ k_H ∈ C_H, ∃ k ∈ C, x = h * (multiTorus hb hf 1 s)⁻¹ * k_H ∧
              y = h * (multiTorus hb hf 0 t)⁻¹ * k := by
  set e : ℕ → ℕ := fun i => (i + 1) / 2
  have hodd : ∀ k, Odd (e (0 + 2 * k) + e (0 + 2 * k + 1)) := fun k =>
    Nat.odd_iff.2 (by simp only [e]; omega)
  have heven : ∀ k, Even (e (1 + 2 * k) + e (1 + 2 * k + 1)) := fun k =>
    Nat.even_iff.2 (by simp only [e]; omega)
  obtain ⟨C_H, C, h1, h2, h3, h4, h5⟩ := relCartan_SO (hb.signBasis e) (hf.signBasis e)
  rw [fixer_signBasis] at h2
  refine ⟨C_H⁻¹, C, h1.inv, fun z hz => by simpa using inv_mem (h2 hz), h3, h4,
    fun x hx y hy => ?_⟩
  obtain ⟨k₁, hk₁, s, hs, t, ht, c, hc, he⟩ :=
    h5 (x⁻¹ * y) (mul_mem (inv_mem hx.1) hy)
  rw [multiTorus_signBasis_of_even e hb hf s 1 heven,
    multiTorus_signBasis_of_odd e hb hf t 0 hodd, multiTorus_map_inv] at he
  refine ⟨x * k₁ * multiTorus hb hf 1 s, mul_mem (mul_mem hx (h2 hk₁))
    (multiTorus_mem_fixer hb hf s 1), s, hs, t, ht, k₁⁻¹, by simpa using hk₁, c, hc,
    by group, ?_⟩
  have : y = x * (x⁻¹ * y) := by group
  rw [this, he]; group

end WeakCartan

end GSpinGGP
