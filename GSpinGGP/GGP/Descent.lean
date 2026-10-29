import GSpinGGP.GGP.Triple
import GSpinGGP.Literature.GSpin
import GSpinGGP.Literature.HarishChandra

/-!
# Descent data: `𝔤⁰`, the special orthogonal quotient, and semisimple descent

Everything here is proved; the only
`sorryAx` reaching these theorems is the one in the definition of `H` (via `flagUnip`),
and the only axioms used are `gspin_specP_surjective_SO` and
`steinberg_centralizer_connected` (`Literature/GSpin`).

* `soSub Q`, `lie0 d`, `lieCenter d`: `so(V)` is the traceless part of `gspin(V)`, and
  `𝔤 = 𝔷 ⊕ 𝔤⁰` with `𝔤⁰ = so(W) ⊕ so(V)` and `𝔷` the Lie algebra of the central `G_m × G_m`
  (`lie_eq_center_sup_lie0`, `disjoint_lieCenter_lie0`; Thesis Prop. 5.1.3.1).
* `conj_eq_of_specP_eq`, `conj_lie0_factors`, `conj_mem_lie0`: conjugation by `G(F)` on the
  ambient algebra (in particular on `𝔤⁰`) factors through `G(F) → SO(W)(F) × SO(V)(F)`.
* `SOGrp`, `Pbar`, `quotHG_equiv`: `H(F)\G(F)/A_G(F) ≃ H̄(F)\Ḡ(F)/Ā_G(F)` (in
  general; `Ā_G = P(A_G)` is nontrivial when `W` or `V` is a hyperbolic plane), and
  `H\G/A_G ≃ H̄\Ḡ` (`quotHG_equiv_SO`) when neither is.
* `fixedSub_inf_movedSub_of_isSS`, `isNondeg_fixedSub_of_isSS`: `W = W'_x ⊕^⊥ W''_x` for semisimple
  `x`.
* `GGPData.restrictFix`, `fixEmbed`, `fixEmbed_H`, `fixEmbed_xi`, `dimG_restrictFix_lt`: the
  smaller GGP datum `(W'_x, V'_x)` and the embedding `(G'_x, H'_x, ξ'_x) → (G, H, ξ)` (Thesis
  §6.5 (6.5.1)).
* `centralizer_eq_map_sup`, `centralizer_diag_eq`, `torusV_eq_map_torusOf`,
  `centralizer_diag_eq_of_isSS`: `Z_G(x) = G'_x · (T_x × T_x)`.
-/

noncomputable section

open CliffordAlgebra Module
open scoped Classical

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

/-! ## 1. `so(V) ⊆ gspin(V)`: the traceless part -/

section SO

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The trace `x ↦ tr(L_x)` of left multiplication on `C(V)`. -/
abbrev cliffTrace [Module.Finite K V] (Q : QuadraticForm K V) (x : CliffordAlgebra Q) : K :=
  LinearMap.trace K _ (LinearMap.mulLeft K x)

omit [Invertible (2 : K)] in
theorem cliffTrace_add [Module.Finite K V] (Q : QuadraticForm K V) (x y : CliffordAlgebra Q) :
    cliffTrace Q (x + y) = cliffTrace Q x + cliffTrace Q y := by
  have e : LinearMap.mulLeft K (x + y) = LinearMap.mulLeft K x + LinearMap.mulLeft K y := by
    ext z; simp [add_mul]
  simp only [cliffTrace, e, map_add]

omit [Invertible (2 : K)] in
theorem cliffTrace_smul [Module.Finite K V] (Q : QuadraticForm K V) (c : K) (x : CliffordAlgebra Q) :
    cliffTrace Q (c • x) = c * cliffTrace Q x := by
  have e : LinearMap.mulLeft K (c • x) = c • LinearMap.mulLeft K x := by
    ext z; simp
  simp only [cliffTrace, e, map_smul, smul_eq_mul]

theorem cliffTrace_one [Module.Finite K V] (Q : QuadraticForm K V) :
    cliffTrace Q 1 = (finrank K (CliffordAlgebra Q) : K) := by
  simp only [cliffTrace, LinearMap.mulLeft_one]
  exact LinearMap.trace_id K _

omit [Invertible (2 : K)] in
theorem cliffTrace_commutator [Module.Finite K V] (Q : QuadraticForm K V) (x y : CliffordAlgebra Q) :
    cliffTrace Q (x * y - y * x) = 0 := by
  rw [sub_eq_add_neg, cliffTrace_add, ← neg_one_smul K (y * x), cliffTrace_smul,
    show cliffTrace Q (x * y) = cliffTrace Q (y * x) from trace_mulLeft_comm Q x y]
  ring

/-- `so(V) ⊆ gspin(V)`: the elements of `gspin(V)` whose left multiplication on `C(V)` is
traceless.  This is the image of `∧²V` (spanned by the commutators `[ι a, ι b]`), i.e. the Lie
algebra of `SO(V)` (Thesis Prop. 5.1.3.1).

NB: it is **not** the span of the products `ι a ι b`: that span is all of `gspin(V)` for `V ≠ 0`,
since `ι v ι v = Q(v)`. -/
def soSub [Module.Finite K V] (Q : QuadraticForm K V) : LieSubalgebra K (CliffordAlgebra Q) where
  carrier := {X | X ∈ gspin Q ∧ cliffTrace Q X = 0}
  add_mem' := fun hX hY => ⟨add_mem hX.1 hY.1, by rw [cliffTrace_add, hX.2, hY.2, add_zero]⟩
  zero_mem' := ⟨zero_mem _, by simp [cliffTrace]⟩
  smul_mem' := fun c _ hX => ⟨(gspin Q).smul_mem c hX.1, by rw [cliffTrace_smul, hX.2, mul_zero]⟩
  lie_mem' := fun {X Y} hX hY => ⟨(gspin Q).lie_mem hX.1 hY.1, by
    rw [Ring.lie_def]; exact cliffTrace_commutator Q X Y⟩

theorem mem_soSub [Module.Finite K V] {Q : QuadraticForm K V} {X : CliffordAlgebra Q} :
    X ∈ soSub Q ↔ X ∈ gspin Q ∧ cliffTrace Q X = 0 := Iff.rfl

/-- The commutators `[ι a, ι b] = ι a ι b − ι b ι a` lie in `so(V)`. -/
theorem commutator_ι_mem_soSub [Module.Finite K V] (Q : QuadraticForm K V) (a b : V) :
    ι Q a * ι Q b - ι Q b * ι Q a ∈ soSub Q :=
  ⟨sub_mem (ι_mul_ι_mem_gspin Q a b) (ι_mul_ι_mem_gspin Q b a), cliffTrace_commutator Q _ _⟩

/-- `gspin(V) = K ⊕ so(V)` (Thesis Prop. 5.1.3.1): every `X` is
`(tr L_X / 2^{dim V}) · 1` plus a traceless element of `gspin(V)`. -/
theorem gspin_eq_span_one_sup_soSub [Module.Finite K V] (Q : QuadraticForm K V) :
    (gspin Q).toSubmodule = Submodule.span K {(1 : CliffordAlgebra Q)} ⊔ (soSub Q).toSubmodule := by
  apply le_antisymm
  · intro X hX
    change X ∈ gspin Q at hX
    set n : K := (finrank K (CliffordAlgebra Q) : K)
    have hn : n ≠ 0 := cast_finrank_cliffordAlgebra_ne_zero Q
    set c : K := cliffTrace Q X / n
    rw [Submodule.mem_sup]
    refine ⟨c • 1, Submodule.smul_mem _ _ (Submodule.subset_span rfl), X - c • 1,
      ⟨sub_mem hX ((gspin Q).smul_mem c (one_mem_gspin Q)), ?_⟩, by abel⟩
    rw [sub_eq_add_neg, cliffTrace_add, ← neg_smul, cliffTrace_smul, cliffTrace_one]
    change cliffTrace Q X + -(cliffTrace Q X / n) * n = 0
    field_simp
    ring
  · refine sup_le ?_ fun X hX => hX.1
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact one_mem_gspin Q

/-- `K · 1 ∩ so(V) = 0`. -/
theorem disjoint_span_one_soSub [Module.Finite K V] (Q : QuadraticForm K V) :
    Disjoint (Submodule.span K {(1 : CliffordAlgebra Q)}) (soSub Q).toSubmodule := by
  rw [Submodule.disjoint_def]
  intro X h1 h2
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp h1
  have h := h2.2
  rw [cliffTrace_smul, cliffTrace_one] at h
  rw [(mul_eq_zero.mp h).resolve_right (cast_finrank_cliffordAlgebra_ne_zero Q), zero_smul]

/-- Conjugation by `g ∈ GSpin(V)` preserves `gspin(V)` and `so(V)` (the adjoint action;
Thesis Prop. 5.1.3.1). -/
theorem conj_mem_soSub [Module.Finite K V] {Q : QuadraticForm K V} (g : GSpin Q)
    {X : CliffordAlgebra Q} (hX : X ∈ soSub Q) :
    ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * X *
      (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ soSub Q := by
  set a : CliffordAlgebra Q := ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  set b : CliffordAlgebra Q := (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) :
    CliffordAlgebra Q)
  have hba : b * a = 1 := Units.inv_mul _
  have hab : a * b = 1 := Units.mul_inv _
  obtain ⟨⟨hX0, hX1⟩, hXt⟩ := hX
  have hb0 : b ∈ even Q := (g⁻¹ : GSpin Q).2.1
  refine ⟨⟨Subalgebra.mul_mem _ (Subalgebra.mul_mem _ g.2.1 hX0) hb0, fun v => ?_⟩, ?_⟩
  · -- `ι v = a ι(u) b` with `u = P(g⁻¹) v`
    set u := specP Q g⁻¹ v
    have hv : ι Q v = a * ι Q u * b := by
      rw [← ι_specP, specP_inv_apply_apply]
    obtain ⟨w, hw⟩ := hX1 u
    rw [Ring.lie_def] at hw
    refine ⟨specP Q g w, ?_⟩
    rw [ι_specP, hw, Ring.lie_def, hv]
    change a * (X * ι Q u - ι Q u * X) * b = a * X * b * (a * ι Q u * b) - a * ι Q u * b * (a * X * b)
    have e1 : a * X * b * (a * ι Q u * b) = a * (X * ι Q u) * b := by
      simp only [mul_assoc]; rw [← mul_assoc b a, hba, one_mul]
    have e2 : a * ι Q u * b * (a * X * b) = a * (ι Q u * X) * b := by
      simp only [mul_assoc]; rw [← mul_assoc b a, hba, one_mul]
    rw [e1, e2, mul_sub, sub_mul]
  · show cliffTrace Q (a * X * b) = 0
    rw [show cliffTrace Q (a * X * b) = cliffTrace Q (b * (a * X)) from trace_mulLeft_comm Q _ _,
      ← mul_assoc, hba, one_mul, hXt]

end SO

/-! ## 2. Functoriality of `P` under `GSpin.map` -/

section MapLemmas

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [Module.Finite K V₁]
  [AddCommGroup V₂] [Module K V₂] {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}

/-- The inverse of `GSpin.map f g` is `C(f)(g⁻¹)`. -/
theorem GSpin.coe_map_inv (f : Q₁ →qᵢ Q₂) (hf : IsNondeg Q₁) (g : GSpin Q₁) :
    ((((GSpin.map f hf g : GSpin Q₂) : (CliffordAlgebra Q₂)ˣ)⁻¹ : (CliffordAlgebra Q₂)ˣ) :
      CliffordAlgebra Q₂) =
      CliffordAlgebra.map f ((((g : (CliffordAlgebra Q₁)ˣ))⁻¹ : (CliffordAlgebra Q₁)ˣ) :
        CliffordAlgebra Q₁) := by
  rw [← Subgroup.coe_inv, ← map_inv]; rfl

/-- `P(C(f) g)(f v) = f(P(g) v)` (`GSpin(W) ⊆ GSpin(V)` compatibly with `P`). -/
theorem specP_map_apply (f : Q₁ →qᵢ Q₂) (hf : IsNondeg Q₁) (g : GSpin Q₁) (v : V₁) :
    specP Q₂ (GSpin.map f hf g) (f v) = f (specP Q₁ g v) := by
  apply ι_injective Q₂
  rw [ι_specP, GSpin.coe_map_inv, GSpin.coe_map, ← CliffordAlgebra.map_apply_ι, ← map_mul,
    ← map_mul, ← ι_specP, CliffordAlgebra.map_apply_ι]

/-- `GSpin(V₁)` acts trivially on `f(V₁)^⊥` (so `GSpin(W)` acts trivially on `W^⊥`). -/
theorem specP_map_apply_of_orth (f : Q₁ →qᵢ Q₂) (hf : IsNondeg Q₁) (g : GSpin Q₁) {u : V₂}
    (hu : ∀ w, QuadraticMap.polar Q₂ (f w) u = 0) :
    specP Q₂ (GSpin.map f hf g) u = u := by
  apply ι_injective Q₂
  have h0 : ((g : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) ∈ evenOdd Q₁ 0 := by
    rw [← even_toSubmodule]; exact g.2.1
  rw [ι_specP, GSpin.coe_map_inv, GSpin.coe_map, map_even_commute_ι f h0 hu, mul_assoc,
    ← map_mul, Units.mul_inv, map_one, mul_one]

/-- `C(f)` maps elements with `g − 1` nilpotent to elements with `C(f) g − 1` nilpotent. -/
theorem isNilpotent_map_sub_one (f : Q₁ →qᵢ Q₂) (hf : IsNondeg Q₁) (g : GSpin Q₁)
    (hg : IsNilpotent (((g : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) - 1)) :
    IsNilpotent ((((GSpin.map f hf g : GSpin Q₂) : (CliffordAlgebra Q₂)ˣ) :
      CliffordAlgebra Q₂) - 1) := by
  rw [GSpin.coe_map, ← map_one (CliffordAlgebra.map f), ← map_sub]
  exact hg.map _

/-- If `y ∈ C(V₂)` commutes with `ι(f v)` for all `v ∈ V₁`, it commutes with `C(f)(C(V₁))`. -/
theorem commute_map_of_commute_ι (f : Q₁ →qᵢ Q₂) {y : CliffordAlgebra Q₂}
    (hy : ∀ v, Commute y (ι Q₂ (f v))) (a : CliffordAlgebra Q₁) :
    Commute y (CliffordAlgebra.map f a) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commute_algebraMap_right _ _
  | ι v => rw [CliffordAlgebra.map_apply_ι]; exact hy v
  | mul a b ha hb => rw [map_mul]; exact ha.mul_right hb
  | add a b ha hb => rw [map_add]; exact ha.add_right hb

/-- `g ∈ GSpin(V)` commutes with `ι v` when `P(g) v = v`. -/
theorem commute_ι_of_specP_eq {Q : QuadraticForm K V₂} (g : GSpin Q) {v : V₂}
    (hv : specP Q g v = v) :
    Commute (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) (ι Q v) := by
  have h := ι_specP g v
  rw [hv] at h
  show _ * _ = _ * _
  conv_rhs => rw [h]
  rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one]

end MapLemmas

/-! ## 3. `SO(V)` and the surjection `P` -/

section SOGroup

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- `SO(V)(K)`: the isometries of `(V, q)` of determinant one. -/
def SOGrp (Q : QuadraticForm K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | (∀ v, Q (g v) = Q v) ∧ LinearMap.det (g : V →ₗ[K] V) = 1}
  one_mem' := ⟨fun _ => rfl, by simp⟩
  mul_mem' := fun {g h} hg hh => ⟨fun v => by
      rw [LinearEquiv.mul_apply, hg.1, hh.1], by
      show LinearMap.det ((g : V →ₗ[K] V) ∘ₗ (h : V →ₗ[K] V)) = 1
      rw [LinearMap.det_comp, hg.2, hh.2, one_mul]⟩
  inv_mem' := fun {g} hg => ⟨fun v => by
      conv_rhs => rw [← LinearEquiv.apply_symm_apply g v]
      rw [hg.1]; rfl, by
      have h := LinearMap.det_comp (g : V →ₗ[K] V) (g.symm : V →ₗ[K] V)
      rw [show (g : V →ₗ[K] V) ∘ₗ (g.symm : V →ₗ[K] V) = LinearMap.id by ext; simp,
        LinearMap.det_id, hg.2, one_mul] at h
      exact h.symm⟩

/-- **Surjectivity of `P`** (Thesis §5.1.2): `P(GSpin(V)(K)) = SO(V)(K)` (Hilbert 90, the axiom
`gspin_specP_surjective_SO`; the inclusion `⊆` is `specP_isometry`, `det_specP`). -/
theorem range_specP_eq_SOGrp [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : IsNondeg Q) :
    (specP Q).range = SOGrp Q := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨specP_isometry x, det_specP x⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨x, hx⟩ := gspin_specP_surjective_SO Q hQ g h1 h2
    exact ⟨x, hx⟩

end SOGroup

/-! ## 4. Nondegeneracy of `W'_x` -/

section Fixed

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- `W'_x = ker(P x − 1)` is nondegenerate iff `W'_x ∩ W''_x = 0` (then `W = W'_x ⊕^⊥ W''_x`).  This holds for semisimple `x`. -/
theorem isNondeg_fixedSub_iff {Q : QuadraticForm K V} (hQ : IsNondeg Q) (x : GSpin Q) :
    IsNondeg (Q.comp (fixedSub x).subtype) ↔ fixedSub x ⊓ movedSub x = ⊥ := by
  have hb : ∀ u v : ↥(fixedSub x), bform (Q.comp (fixedSub x).subtype) u v = bform Q u v :=
    fun u v => by simp [bform, QuadraticMap.associated_comp]
  constructor
  · intro h
    rw [eq_bot_iff]
    rintro u ⟨hu1, hu2⟩
    have := (isNondeg_iff _).mp h ⟨u, hu1⟩ fun y => by
      rw [hb, QuadraticMap.associated_isSymm K Q]
      exact fixedSub_orthogonal_movedSub x y y.2 u hu2
    exact (Submodule.mem_bot K).mpr congr(($this : V))
  · intro h
    -- `W'_x + W''_x = W` by rank–nullity
    have hsup : fixedSub x ⊔ movedSub x = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq (fixedSub x) (movedSub x)
      have h2 := LinearMap.finrank_range_add_finrank_ker
        ((specP Q x : V →ₗ[K] V) - LinearMap.id)
      rw [h, finrank_bot] at h1
      have e1 : finrank K ↥(fixedSub x) =
          finrank K ↥(LinearMap.ker ((specP Q x : V →ₗ[K] V) - LinearMap.id)) := rfl
      have e2 : finrank K ↥(movedSub x) =
          finrank K ↥(LinearMap.range ((specP Q x : V →ₗ[K] V) - LinearMap.id)) := rfl
      omega
    rw [isNondeg_iff]
    intro u hu
    have hu' : ∀ w, bform Q u w = 0 := by
      intro w
      have hw : w ∈ fixedSub x ⊔ movedSub x := hsup ▸ Submodule.mem_top
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hw
      rw [map_add, ← hb u ⟨w₁, hw₁⟩, hu, zero_add]
      exact fixedSub_orthogonal_movedSub x u u.2 w₂ hw₂
    exact Subtype.ext ((isNondeg_iff Q).mp hQ u hu')

end Fixed

/-! ## 5. Centralizers of semisimple elements in `GSpin(V)` -/

section Centralizer

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
variable {V V' : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup V'] [Module F V'] [FiniteDimensional F V']
  {Q : QuadraticForm F V} {Q' : QuadraticForm F V'}

/-- An isometric embedding of a nondegenerate space is injective. -/
theorem isometry_injective (f : Q' →qᵢ Q) (hf : IsNondeg Q') : Function.Injective f := by
  have hk : LinearMap.ker f.toLinearMap = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    refine (Submodule.mem_bot F).mpr ((isNondeg_iff Q').mp hf v fun w => ?_)
    rw [← bform_isometry f]
    change bform Q (f.toLinearMap v) (f w) = 0
    rw [hv, map_zero, LinearMap.zero_apply]
  exact LinearMap.ker_eq_bot.mp hk

/-- **Lifting to the fixed space**: if
`g ∈ GSpin(V)` commutes with the semisimple `y`, and `f : V' ↪ V` identifies `V'` with
`W'_y = ker(P y − 1)`, then `P(g)|_{W'_y}` lifts to `GSpin(V')`.  Inputs: `P(g)` preserves `W'_y`;
`det P(g)|_{W'_y} = 1` (Steinberg, `steinberg_centralizer_connected'`); surjectivity of `P`
(`gspin_specP_surjective_SO`). -/
theorem exists_lift_of_commute (hQ : IsNondeg Q) (f : Q' →qᵢ Q) (hf : IsNondeg Q') {y : GSpin Q}
    (hy : IsSS F ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
    (hrange : ∀ w, w ∈ fixedSub y ↔ ∃ v, f v = w) {g : GSpin Q} (hg : g * y = y * g) :
    ∃ g' : GSpin Q', ∀ v, specP Q g (f v) = f (specP Q' g' v) := by
  have hmem : (g : (CliffordAlgebra Q)ˣ) ∈ grpCentralizer (GSpin Q) (y : (CliffordAlgebra Q)ˣ) :=
    ⟨g.2, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hg)⟩
  obtain ⟨hc, ⟨hmaps, hdet⟩, -⟩ := (steinberg_centralizer_connected' Q hQ y hy g).mp hmem
  have hinj := isometry_injective f hf
  -- `V' ≃ W'_y` via `f`
  let f₀ : V' →ₗ[F] ↥(fixedSub y) :=
    f.toLinearMap.codRestrict (fixedSub y) fun v => (hrange _).mpr ⟨v, rfl⟩
  have hf₀ : Function.Bijective f₀ := ⟨fun a b h => hinj (congrArg Subtype.val h),
    fun w => by obtain ⟨v, hv⟩ := (hrange w).mp w.2; exact ⟨v, Subtype.ext hv⟩⟩
  let e : V' ≃ₗ[F] ↥(fixedSub y) := LinearEquiv.ofBijective f₀ hf₀
  have he : ∀ v, ((e v : ↥(fixedSub y)) : V) = f v := fun _ => rfl
  let R : ↥(fixedSub y) →ₗ[F] ↥(fixedSub y) := (specP Q g : V →ₗ[F] V).restrict hmaps
  let r : V' →ₗ[F] V' := (e.symm : ↥(fixedSub y) →ₗ[F] V') ∘ₗ R ∘ₗ (e : V' →ₗ[F] ↥(fixedSub y))
  have hr : ∀ v, f (r v) = specP Q g (f v) := fun v => by
    rw [← he]; simp [r, R, he]
  have rinj : Function.Injective r := fun a b h => by
    have h' := congrArg f h
    rw [hr, hr] at h'
    exact hinj ((specP Q g).injective h')
  let rE : V' ≃ₗ[F] V' := LinearEquiv.ofInjectiveEndo r rinj
  have hiso : ∀ v, Q' (rE v) = Q' v := fun v => by
    rw [← f.map_app, ← f.map_app]
    change Q (f (r v)) = Q (f v)
    rw [hr, specP_isometry]
  have hdet' : LinearMap.det (rE : V' →ₗ[F] V') = 1 := by
    change LinearMap.det r = 1
    have := LinearMap.det_conj R e.symm
    rw [LinearEquiv.symm_symm] at this
    rw [this, hdet]
  obtain ⟨g', hg'⟩ := gspin_specP_surjective_SO Q' hf rE hiso hdet'
  exact ⟨g', fun v => by rw [hg']; exact (hr v).symm⟩

/-- `g ∈ GSpin(V)` fixing `W'_y` pointwise and `C(f)(GSpin(V'))` commute with `y`. -/
theorem map_commute_of_range (f : Q' →qᵢ Q) (hf : IsNondeg Q') {y : GSpin Q}
    (hrange : ∀ w, w ∈ fixedSub y ↔ ∃ v, f v = w) (g' : GSpin Q') :
    GSpin.map f hf g' * y = y * GSpin.map f hf g' := by
  have hy : ∀ v, specP Q y (f v) = f v := fun v => by
    have := LinearMap.mem_ker.mp ((hrange (f v)).mpr ⟨v, rfl⟩)
    simpa [sub_eq_zero] using this
  apply Subtype.ext; apply Units.ext
  exact (commute_map_of_commute_ι f (fun v => commute_ι_of_specP_eq y (hy v)) _).eq.symm

/-- **Centralizers in `GSpin(V)`** (Thesis §6.5 (6.5.1)): for semisimple
`y ∈ GSpin(V)(F)` and `V' ≅ W'_y = ker(P y − 1)`,
`Z_{GSpin(V)}(y) = GSpin(W'_y) · GSpin(W''_y)_y`, where `GSpin(W''_y)_y` is realized as the
elements commuting with `y` and fixing `W'_y` pointwise. -/
theorem centralizer_eq_map_sup (hQ : IsNondeg Q) (f : Q' →qᵢ Q) (hf : IsNondeg Q') {y : GSpin Q}
    (hy : IsSS F ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
    (hrange : ∀ w, w ∈ fixedSub y ↔ ∃ v, f v = w) :
    Subgroup.centralizer {y} =
      (GSpin.map f hf).range ⊔ (Subgroup.centralizer {y} ⊓ fixerOf Q (fixedSub y)) := by
  apply le_antisymm
  · intro g hg
    have hg' : g * y = y * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    obtain ⟨g', hlift⟩ := exists_lift_of_commute hQ f hf hy hrange hg'
    set a := GSpin.map f hf g'
    have ha : a * y = y * a := map_commute_of_range f hf hrange g'
    have hga : g = a * (a⁻¹ * g) := (mul_inv_cancel_left a g).symm
    rw [hga]
    refine Subgroup.mul_mem_sup ⟨g', rfl⟩ ⟨?_, fun w hw => ?_⟩
    · show a⁻¹ * g ∈ Subgroup.centralizer {y}
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hai : a⁻¹ * y = y * a⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ha, mul_inv_cancel_right]
      rw [mul_assoc, hg', ← mul_assoc, hai, mul_assoc]
    · obtain ⟨v, rfl⟩ := (hrange w).mp hw
      rw [specP_mul_apply, hlift, ← specP_map_apply f hf g', ← specP_mul_apply, inv_mul_cancel,
        map_one]
      rfl
  · refine sup_le ?_ inf_le_left
    rintro _ ⟨g', rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (map_commute_of_range f hf hrange g')

/-- Semisimplicity is preserved by algebra homomorphisms: `p(a) = 0` with `p` squarefree gives
`p(φ a) = 0`.  Used for `x ↦ incl x`, `C(W) → C(V)`. -/
theorem isSS_algHom {A B : Type*} [Ring A] [Algebra F A] [FiniteDimensional F A] [Ring B]
    [Algebra F B] (φ : A →ₐ[F] B) {a : A} (ha : IsSS F a) : IsSS F (φ a) := by
  set p := minpoly F (LinearMap.mulLeft F a)
  have hsq : Squarefree p := Module.End.IsSemisimple.minpoly_squarefree ha
  have h0 : Polynomial.aeval (Algebra.lmul F A a) p = 0 := minpoly.aeval F _
  rw [Polynomial.aeval_algHom_apply] at h0
  have h1 : Polynomial.aeval a p = 0 :=
    Algebra.lmul_injective (R := F) (h0.trans (map_zero _).symm)
  have h3 : Polynomial.aeval (Algebra.lmul F B (φ a)) p = 0 := by
    rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_algHom_apply, h1, map_zero, map_zero]
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq h3

/-- `p(R_x) = R_{p(x)}` for right multiplication. -/
theorem aeval_mulRight {A : Type*} [Ring A] [Algebra F A] (x : A) (p : Polynomial F) :
    Polynomial.aeval (LinearMap.mulRight F x) p = LinearMap.mulRight F (Polynomial.aeval x p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq]
    ext z; simp [mul_add]
  | monomial n a =>
    ext z
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      LinearMap.pow_mulRight, LinearMap.mulRight_apply]
    rw [Algebra.smul_def, ← mul_assoc, ← mul_assoc, Algebra.commutes]

/-- For a semisimple endomorphism `D`, `D² w = 0 ⇒ D w = 0`. -/
theorem apply_eq_zero_of_sq_of_isSemisimple {M : Type*} [AddCommGroup M] [Module F M]
    {D : Module.End F M} (hD : D.IsSemisimple) {w : M} (hw : D (D w) = 0) : D w = 0 := by
  have hp : LinearMap.ker (D * D) ∈ D.invtSubmodule := by
    rw [Module.End.mem_invtSubmodule]
    intro v hv
    simp only [Submodule.mem_comap, LinearMap.mem_ker, Module.End.mul_apply] at hv ⊢
    rw [hv, map_zero]
  have hz := Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨2, ?_⟩ (hD.restrict hp)
  · have := congrArg Subtype.val (LinearMap.congr_fun hz ⟨w, show (D * D) w = 0 from hw⟩)
    exact this
  · ext ⟨v, hv⟩
    change D (D v) = 0
    exact LinearMap.mem_ker.mp hv

/-- **Semisimple elements have nondegenerate fixed spaces** (`W = W'_x ⊕^⊥ W''_x`
for semisimple `x`): `W'_x ∩ W''_x = 0`.  Proof: with `D = L_x − R_x`
(semisimple, as a difference of commuting semisimple endomorphisms of `C(W)`), `u = P(x)v − v`
with `P(x)u = u` gives `D(ι v) = ι(u) x` and `D(ι(u) x) = 0`, so `ι(u) x = 0`. -/
theorem fixedSub_inf_movedSub_of_isSS {Q : QuadraticForm F V} (x : GSpin Q)
    (hss : IsSS F ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) :
    fixedSub x ⊓ movedSub x = ⊥ := by
  set X : CliffordAlgebra Q := ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  set Y : CliffordAlgebra Q := (((x : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) :
    CliffordAlgebra Q)
  have hYX : Y * X = 1 := Units.inv_mul _
  have hXY : X * Y = 1 := Units.mul_inv _
  -- `R_X` is semisimple
  set p := minpoly F (LinearMap.mulLeft F X)
  have hsq : Squarefree p := Module.End.IsSemisimple.minpoly_squarefree hss
  have h0 : Polynomial.aeval (Algebra.lmul F (CliffordAlgebra Q) X) p = 0 := minpoly.aeval F _
  rw [Polynomial.aeval_algHom_apply] at h0
  have h1 : Polynomial.aeval X p = 0 :=
    Algebra.lmul_injective (R := F) (h0.trans (map_zero _).symm)
  have hR : Module.End.IsSemisimple (LinearMap.mulRight F X) :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq (by
      rw [aeval_mulRight, h1]; ext; simp)
  have hD : Module.End.IsSemisimple (LinearMap.mulLeft F X - LinearMap.mulRight F X) :=
    Module.End.IsSemisimple.sub_of_commute (LinearMap.commute_mulLeft_right X X) hss hR
  -- `ι(P x w) X = X ι(w)`
  have key : ∀ w, ι Q (specP Q x w) * X = X * ι Q w := fun w => by
    rw [ι_specP, mul_assoc, hYX, mul_one]
  rw [eq_bot_iff]
  rintro u ⟨hu1, ⟨v, rfl⟩⟩
  have hu1' : specP Q x (specP Q x v - v) = specP Q x v - v := by
    have := LinearMap.mem_ker.mp hu1
    simpa [sub_eq_zero] using this
  set u := specP Q x v - v with hu
  set D := LinearMap.mulLeft F X - LinearMap.mulRight F X
  have hDv : D (ι Q v) = ι Q u * X := by
    simp only [D, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    rw [← key, hu, map_sub, sub_mul]
  have hDu : D (ι Q u * X) = 0 := by
    simp only [D, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    rw [← mul_assoc, ← key, hu1', sub_self]
  have h2 := apply_eq_zero_of_sq_of_isSemisimple hD (show D (D (ι Q v)) = 0 by rw [hDv, hDu])
  rw [hDv] at h2
  have h3 : ι Q u = 0 := by
    have := congrArg (· * Y) h2
    simpa [mul_assoc, hXY] using this
  exact (Submodule.mem_bot F).mpr ((ι_injective Q) (h3.trans (map_zero _).symm))

/-- For semisimple `x`, `W'_x` is nondegenerate, so `restrictFix` applies. -/
theorem isNondeg_fixedSub_of_isSS {Q : QuadraticForm F V} (hQ : IsNondeg Q) (x : GSpin Q)
    (hss : IsSS F ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) :
    IsNondeg (Q.comp (fixedSub x).subtype) :=
  (isNondeg_fixedSub_iff hQ x).mpr (fixedSub_inf_movedSub_of_isSS x hss)

/-- Pointwise form of `centralizer_eq_map_sup`: `g = C(f)(g') · t` with `t` commuting with `y` and
fixing `W'_y`. -/
theorem exists_map_mul_of_commute (hQ : IsNondeg Q) (f : Q' →qᵢ Q) (hf : IsNondeg Q')
    {y : GSpin Q} (hy : IsSS F ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
    (hrange : ∀ w, w ∈ fixedSub y ↔ ∃ v, f v = w) {g : GSpin Q} (hg : g * y = y * g) :
    ∃ g' : GSpin Q', ∃ t ∈ Subgroup.centralizer {y} ⊓ fixerOf Q (fixedSub y),
      g = GSpin.map f hf g' * t := by
  obtain ⟨g', hlift⟩ := exists_lift_of_commute hQ f hf hy hrange hg
  set a := GSpin.map f hf g'
  have ha : a * y = y * a := map_commute_of_range f hf hrange g'
  refine ⟨g', a⁻¹ * g, ⟨?_, fun w hw => ?_⟩, (mul_inv_cancel_left a g).symm⟩
  · show a⁻¹ * g ∈ Subgroup.centralizer {y}
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hai : a⁻¹ * y = y * a⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ha, mul_inv_cancel_right]
    rw [mul_assoc, hg, ← mul_assoc, hai, mul_assoc]
  · obtain ⟨v, rfl⟩ := (hrange w).mp hw
    rw [specP_mul_apply, hlift, ← specP_map_apply f hf g', ← specP_mul_apply, inv_mul_cancel,
      map_one]
    rfl

end Centralizer

/-! ## 6. `𝔤 = 𝔷 ⊕ 𝔤⁰` and the adjoint action -/

namespace GGPData

variable {K : Type*} [Field K] [Invertible (2 : K)] (d : GGPData K)

/-- `𝔤⁰ = so(W) ⊕ so(V)` (Thesis §5.2): the traceless part of
`𝔤 = gspin(W) ⊕ gspin(V)`, the Lie algebra of `Ḡ = SO(W) × SO(V)`.  (It equals `[𝔤, 𝔤]` unless
`dim W = 2` or `dim V = 2`, where `gspin` is abelian.) -/
def lie0 : Submodule K d.ambient :=
  (soSub d.QW).toSubmodule.prod (soSub d.QV).toSubmodule

/-- `𝔷 = K(1,0) ⊕ K(0,1)`, the Lie algebra of the central torus `G_m × G_m` of `G` (the scalars of
both factors).  It equals `Lie(A_G)` unless `W` or `V` is a hyperbolic plane. -/
def lieCenter : Submodule K d.ambient :=
  Submodule.span K {((1 : CliffordAlgebra d.QW), (0 : CliffordAlgebra d.QV)), (0, 1)}

theorem lie0_le_lie : d.lie0 ≤ d.lie.toSubmodule := fun _ hX => ⟨hX.1.1, hX.2.1⟩

/-- `𝔤⁰` is a Lie subalgebra (so it is `[𝔤⁰, 𝔤⁰] ⊆ 𝔤⁰`). -/
theorem lie0_lie_mem {X Y : d.ambient} (hX : X ∈ d.lie0) (hY : Y ∈ d.lie0) :
    X * Y - Y * X ∈ d.lie0 := by
  refine ⟨?_, ?_⟩
  · have := (soSub d.QW).lie_mem hX.1 hY.1
    simpa [Ring.lie_def] using this
  · have := (soSub d.QV).lie_mem hX.2 hY.2
    simpa [Ring.lie_def] using this

/-- `𝔤 = 𝔷 + 𝔤⁰` (Thesis Prop. 5.1.3.1). -/
theorem lie_eq_center_sup_lie0 : d.lie.toSubmodule = d.lieCenter ⊔ d.lie0 := by
  apply le_antisymm
  · rintro ⟨X₁, X₂⟩ ⟨h1, h2⟩
    have e1 := gspin_eq_span_one_sup_soSub d.QW
    have e2 := gspin_eq_span_one_sup_soSub d.QV
    have m1 : X₁ ∈ (gspin d.QW).toSubmodule := h1
    have m2 : X₂ ∈ (gspin d.QV).toSubmodule := h2
    rw [e1, Submodule.mem_sup] at m1
    rw [e2, Submodule.mem_sup] at m2
    obtain ⟨a, ha, b, hb, rfl⟩ := m1
    obtain ⟨a', ha', b', hb', rfl⟩ := m2
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp ha'
    rw [Submodule.mem_sup]
    refine ⟨(c • 1, c' • 1), ?_, (b, b'), ⟨hb, hb'⟩, rfl⟩
    have : ((c • (1 : CliffordAlgebra d.QW), c' • (1 : CliffordAlgebra d.QV)) : d.ambient) =
        c • ((1 : CliffordAlgebra d.QW), (0 : CliffordAlgebra d.QV)) + c' • (0, 1) := by
      ext <;> simp
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · refine sup_le ?_ d.lie0_le_lie
    rw [lieCenter, Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact ⟨one_mem_gspin _, zero_mem _⟩
    · exact ⟨zero_mem _, one_mem_gspin _⟩

/-- The sum `𝔤 = 𝔷 ⊕ 𝔤⁰` is direct. -/
theorem disjoint_lieCenter_lie0 : Disjoint d.lieCenter d.lie0 := by
  rw [Submodule.disjoint_def]
  intro X hX h0
  rw [lieCenter, Submodule.mem_span_pair] at hX
  obtain ⟨a, b, rfl⟩ := hX
  have h1 := (disjoint_span_one_soSub d.QW)
  have h2 := (disjoint_span_one_soSub d.QV)
  rw [Submodule.disjoint_def] at h1 h2
  have ha := h1 (a • 1) (Submodule.smul_mem _ _ (Submodule.subset_span rfl)) (by simpa using h0.1)
  have hb := h2 (b • 1) (Submodule.smul_mem _ _ (Submodule.subset_span rfl)) (by simpa using h0.2)
  ext <;> simp [ha, hb]

/-- The underlying first component of `g ∈ G ⊆ (C(W) × C(V))^×`. -/
theorem val_fst (g : d.G) :
    (((g : d.ambientˣ) : d.ambient)).1 = (((d.fst g : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) :
      CliffordAlgebra d.QW) := rfl

/-- The underlying second component of `g ∈ G ⊆ (C(W) × C(V))^×`. -/
theorem val_snd (g : d.G) :
    (((g : d.ambientˣ) : d.ambient)).2 = (((d.snd g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) :
      CliffordAlgebra d.QV) := rfl

/-- The central scalars `(c₁, c₂) ∈ G_m × G_m ⊆ G`. -/
def scalarPair (c₁ c₂ : Kˣ) : d.G := d.pair (scalarGSpin d.QW c₁, scalarGSpin d.QV c₂)

/-- The scalars `(c₁, c₂)` commute with the whole ambient algebra `C(W) × C(V)`. -/
theorem scalarPair_commute (c₁ c₂ : Kˣ) (X : d.ambient) :
    ((d.scalarPair c₁ c₂ : d.ambientˣ) : d.ambient) * X =
      X * ((d.scalarPair c₁ c₂ : d.ambientˣ) : d.ambient) := by
  refine Prod.ext ?_ ?_
  · show (((scalarGSpin d.QW c₁ : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) *
        X.1 = X.1 * (((scalarGSpin d.QW c₁ : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) :
          CliffordAlgebra d.QW)
    exact Algebra.commutes _ _
  · show (((scalarGSpin d.QV c₂ : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) *
        X.2 = X.2 * (((scalarGSpin d.QV c₂ : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) :
          CliffordAlgebra d.QV)
    exact Algebra.commutes _ _

/-- The kernel of `G(F) → SO(W)(F) × SO(V)(F)` is the central `G_m × G_m`: if `g, g'` have the same images in `SO(W) × SO(V)` then `g = g' · (c₁, c₂)`. -/
theorem exists_scalarPair_of_specP_eq {g g' : d.G}
    (h1 : specP d.QW (d.fst g) = specP d.QW (d.fst g'))
    (h2 : specP d.QV (d.snd g) = specP d.QV (d.snd g')) :
    ∃ c₁ c₂ : Kˣ, g = g' * d.scalarPair c₁ c₂ := by
  obtain ⟨c₁, hc₁⟩ : (d.fst g')⁻¹ * d.fst g ∈ (scalarGSpin d.QW).range := by
    rw [← ker_specP d.nondeg, MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  obtain ⟨c₂, hc₂⟩ : (d.snd g')⁻¹ * d.snd g ∈ (scalarGSpin d.QV).range := by
    rw [← ker_specP d.nondeg_QV, MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
  refine ⟨c₁, c₂, d.G_ext ?_ ?_⟩
  · rw [map_mul, scalarPair, fst_pair]
    show d.fst g = d.fst g' * scalarGSpin d.QW c₁
    rw [hc₁, mul_inv_cancel_left]
  · rw [map_mul, scalarPair, snd_pair]
    show d.snd g = d.snd g' * scalarGSpin d.QV c₂
    rw [hc₂, mul_inv_cancel_left]

/-- The conjugation action of `G(F)` on the ambient
algebra `C(W) × C(V)` (in particular on `𝔤⁰`) depends only on the image of `g` in
`SO(W)(F) × SO(V)(F)`. -/
theorem conj_eq_of_specP_eq {g g' : d.G}
    (h1 : specP d.QW (d.fst g) = specP d.QW (d.fst g'))
    (h2 : specP d.QV (d.snd g) = specP d.QV (d.snd g')) (X : d.ambient) :
    ((g : d.ambientˣ) : d.ambient) * X * (((g : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) =
      ((g' : d.ambientˣ) : d.ambient) * X * (((g' : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) := by
  obtain ⟨c₁, c₂, rfl⟩ := d.exists_scalarPair_of_specP_eq h1 h2
  set a : d.ambientˣ := (d.scalarPair c₁ c₂ : d.ambientˣ)
  have ha : (a : d.ambient) * X = X * a := d.scalarPair_commute c₁ c₂ X
  have e : (((g' * d.scalarPair c₁ c₂ : d.G) : d.ambientˣ)) = (g' : d.ambientˣ) * a := rfl
  rw [e, mul_inv_rev, Units.val_mul, Units.val_mul, mul_assoc (g' : d.ambient), ha]
  simp only [mul_assoc, Units.mul_inv_cancel_left]

/-- The conjugation action of `G(F)` on `𝔤⁰` factors
through `G(F) → SO(W)(F) × SO(V)(F)` (`conj_eq_of_specP_eq` restricted to `𝔤⁰`; together with
`conj_mem_lie0` this is an action of `Ḡ(F)` on `𝔤⁰`). -/
theorem conj_lie0_factors {g g' : d.G}
    (h1 : specP d.QW (d.fst g) = specP d.QW (d.fst g'))
    (h2 : specP d.QV (d.snd g) = specP d.QV (d.snd g')) {X : d.ambient} (_hX : X ∈ d.lie0) :
    ((g : d.ambientˣ) : d.ambient) * X * (((g : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) =
      ((g' : d.ambientˣ) : d.ambient) * X * (((g' : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) :=
  d.conj_eq_of_specP_eq h1 h2 X

/-- Conjugation by `G(F)` preserves `𝔤⁰`: `g (ι a ι b) g⁻¹ = ι(P a) ι(P b)` on each factor,
and conjugation preserves `gspin` and the trace. -/
theorem conj_mem_lie0 (g : d.G) {X : d.ambient} (hX : X ∈ d.lie0) :
    ((g : d.ambientˣ) : d.ambient) * X * (((g : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) ∈
      d.lie0 :=
  ⟨conj_mem_soSub (d.fst g) hX.1, conj_mem_soSub (d.snd g) hX.2⟩

/-! ## 7. The descended GGP datum `(W'_x, V'_x)` -/

section Restrict

variable (x : GSpin d.QW)

/-- `dim W'_x`. -/
abbrev fixDim : ℕ := finrank K ↥(fixedSub x)

/-- A linear isomorphism `K^{dim W'_x} ≃ W'_x` (from a chosen basis). -/
def fixEquiv : (Fin (d.fixDim x) → K) ≃ₗ[K] ↥(fixedSub x) :=
  (Module.finBasis K ↥(fixedSub x)).equivFun.symm

/-- The form of `W'_x`, transported to `K^{dim W'_x}`. -/
def fixQW : QuadraticForm K (Fin (d.fixDim x) → K) :=
  (d.QW.comp (fixedSub x).subtype).comp (d.fixEquiv x).toLinearMap

/-- The isometric embedding `W'_x ↪ W`. -/
def fixIsoW : d.fixQW x →qᵢ d.QW where
  toLinearMap := (fixedSub x).subtype ∘ₗ (d.fixEquiv x).toLinearMap
  map_app' _ := rfl

theorem fixIsoW_apply (w : Fin (d.fixDim x) → K) :
    d.fixIsoW x w = ((d.fixEquiv x w : ↥(fixedSub x)) : Fin d.m → K) := rfl

theorem fixIsoW_mem (w : Fin (d.fixDim x) → K) : d.fixIsoW x w ∈ fixedSub x :=
  (d.fixEquiv x w).2

theorem fixIsoW_injective : Function.Injective (d.fixIsoW x) := fun _ _ h =>
  (d.fixEquiv x).injective (Subtype.ext h)

/-- The range of `W'_x ↪ W` is `W'_x`. -/
theorem fixIsoW_surj {w : Fin d.m → K} (hw : w ∈ fixedSub x) :
    ∃ w', d.fixIsoW x w' = w :=
  ⟨(d.fixEquiv x).symm ⟨w, hw⟩, by simp [fixIsoW_apply]⟩

/-- The form of `W'_x` is nondegenerate when that of `W'_x ⊆ W` is. -/
theorem isNondeg_fixQW (hx : IsNondeg (d.QW.comp (fixedSub x).subtype)) : IsNondeg (d.fixQW x) := by
  rw [isNondeg_iff] at hx ⊢
  intro a ha
  have := hx (d.fixEquiv x a) fun y => by
    obtain ⟨b, rfl⟩ := (d.fixEquiv x).surjective y
    have e1 := bform_isometry (d.fixIsoW x) a b
    have e2 : bform (d.QW.comp (fixedSub x).subtype) (d.fixEquiv x a) (d.fixEquiv x b) =
        bform d.QW (d.fixIsoW x a) (d.fixIsoW x b) := by
      simp [bform, QuadraticMap.associated_comp, fixIsoW_apply]
    rw [e2, e1, ha]
  exact (d.fixEquiv x).injective (this.trans (map_zero _).symm)

/-- **The descended GGP datum** `(W'_x, V'_x = W'_x ⊕^⊥ Z)` (Thesis
§6.5 (6.5.1)): same `Z`, `r`, `ν`, with `W'_x = ker(P(x) − 1)`.
It needs `W'_x` nondegenerate, which holds for semisimple `x` (then `W = W'_x ⊕^⊥ W''_x`;
criterion: `isNondeg_fixedSub_iff`); the hypothesis is explicit because `GGPData` carries a
nondegeneracy proof. -/
abbrev restrictFix (hx : IsNondeg (d.QW.comp (fixedSub x).subtype)) : GGPData K where
  m := d.fixDim x
  QW := d.fixQW x
  nondeg := d.isNondeg_fixQW x hx
  r := d.r
  ν := d.ν

variable {x}
variable (hx : IsNondeg (d.QW.comp (fixedSub x).subtype))

/-- The isometric embedding `V'_x = W'_x ⊕ Z ↪ W ⊕ Z = V`. -/
def fixIsoV : (d.restrictFix x hx).QV →qᵢ d.QV where
  toLinearMap := (d.fixIsoW x).toLinearMap.prodMap LinearMap.id
  map_app' v := by
    exact congrArg (fun t => t + d.QZ v.2) ((d.fixIsoW x).map_app v.1)

@[simp] theorem fixIsoV_apply (v : (d.restrictFix x hx).V) :
    d.fixIsoV hx v = (d.fixIsoW x v.1, v.2) := rfl

theorem fixIsoV_zV (k : ℤ) : d.fixIsoV hx ((d.restrictFix x hx).zV k) = d.zV k := by
  exact Prod.ext (map_zero (d.fixIsoW x)) rfl

/-- `G'_x → G`: `GSpin(W'_x) × GSpin(V'_x) → GSpin(W) × GSpin(V)` induced by the isometric
embeddings. -/
def fixEmbed : (d.restrictFix x hx).G →* d.G :=
  d.pair.comp (((GSpin.map (d.fixIsoW x) (d.restrictFix x hx).nondeg).comp
    (d.restrictFix x hx).fst).prod
    ((GSpin.map (d.fixIsoV hx) (d.restrictFix x hx).nondeg_QV).comp (d.restrictFix x hx).snd))

theorem fst_fixEmbed (g : (d.restrictFix x hx).G) :
    d.fst (d.fixEmbed hx g) = GSpin.map (d.fixIsoW x) (d.restrictFix x hx).nondeg
      ((d.restrictFix x hx).fst g) := rfl

theorem snd_fixEmbed (g : (d.restrictFix x hx).G) :
    d.snd (d.fixEmbed hx g) = GSpin.map (d.fixIsoV hx) (d.restrictFix x hx).nondeg_QV
      ((d.restrictFix x hx).snd g) := rfl

/-- `GSpin(W'_x) → GSpin(W) → GSpin(V)` equals `GSpin(W'_x) → GSpin(V'_x) → GSpin(V)`. -/
theorem incl_map_fixIsoW (a : GSpin (d.restrictFix x hx).QW) :
    d.incl (GSpin.map (d.fixIsoW x) (d.restrictFix x hx).nondeg a) =
      GSpin.map (d.fixIsoV hx) (d.restrictFix x hx).nondeg_QV ((d.restrictFix x hx).incl a) := by
  apply Subtype.ext; apply Units.ext
  have key : (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)).comp
      (CliffordAlgebra.map (d.fixIsoW x)) =
      (CliffordAlgebra.map (d.fixIsoV hx)).comp
        (CliffordAlgebra.map (QuadraticMap.Isometry.inl (d.restrictFix x hx).QW d.QZ)) := by
    refine CliffordAlgebra.hom_ext (LinearMap.ext fun w => ?_)
    show CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
        (CliffordAlgebra.map (d.fixIsoW x) (ι _ w)) = CliffordAlgebra.map (d.fixIsoV hx)
        (CliffordAlgebra.map (QuadraticMap.Isometry.inl (d.restrictFix x hx).QW d.QZ) (ι _ w))
    erw [CliffordAlgebra.map_apply_ι, CliffordAlgebra.map_apply_ι, CliffordAlgebra.map_apply_ι,
      CliffordAlgebra.map_apply_ι]
    rfl
  exact congrArg (fun φ => φ (((a : (CliffordAlgebra (d.restrictFix x hx).QW)ˣ)) :
    CliffordAlgebra (d.restrictFix x hx).QW)) key

theorem nPart_fixEmbed (g : (d.restrictFix x hx).G) :
    d.nPart (d.fixEmbed hx g) =
      GSpin.map (d.fixIsoV hx) (d.restrictFix x hx).nondeg_QV ((d.restrictFix x hx).nPart g) := by
  rw [nPart, nPart, fst_fixEmbed, snd_fixEmbed, incl_map_fixIsoW, map_mul, map_inv]

/-- The flag `Z_•` of `V` is the image of the flag `Z_•` of `V'_x` (both are spanned by the same
`z_k`). -/
theorem flag_sub_eq_map (i : Fin (d.flag.len + 1)) :
    d.flag.sub i = ((d.restrictFix x hx).flag.sub i).map (d.fixIsoV hx).toLinearMap := by
  change Submodule.span K (Set.range fun j : Fin (i : ℕ) => d.zV ((d.r : ℤ) - (j : ℕ))) =
    (Submodule.span K (Set.range fun j : Fin (i : ℕ) =>
      (d.restrictFix x hx).zV ((d.r : ℤ) - (j : ℕ)))).map (d.fixIsoV hx).toLinearMap
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext j
  exact (d.fixIsoV_zV hx _).symm

theorem flag_top_eq_map :
    d.flag.top = (d.restrictFix x hx).flag.top.map (d.fixIsoV hx).toLinearMap :=
  d.flag_sub_eq_map hx (Fin.last _)

/-- `N'_x ↪ N`: the embedding `GSpin(V'_x) → GSpin(V)` carries the unipotent radical `N'` of the
flag `Z_•` of `V'_x` into `N` (`N'_x` is the unipotent factor of `H'_x`). -/
theorem map_mem_N {n : GSpin (d.restrictFix x hx).QV} (hn : n ∈ (d.restrictFix x hx).N) :
    GSpin.map (d.fixIsoV hx) (d.restrictFix x hx).nondeg_QV n ∈ d.N := by
  obtain ⟨hn0, hn1, hn2, hn3⟩ := hn
  set f := d.fixIsoV hx
  set g := GSpin.map f (d.restrictFix x hx).nondeg_QV n
  have hP : ∀ v, specP d.QV g (f v) = f (specP _ n v) := specP_map_apply f _ n
  refine ⟨?_, ?_, ?_, isNilpotent_map_sub_one f _ n hn3⟩
  · rw [mem_flagStab_iff]
    intro i v hv
    rw [d.flag_sub_eq_map hx] at hv ⊢
    obtain ⟨v', hv', rfl⟩ := hv
    exact ⟨_, flagStab_mapsTo hn0 i hv', (hP v').symm⟩
  · intro i v hv
    rw [d.flag_sub_eq_map hx] at hv ⊢
    obtain ⟨v', hv', rfl⟩ := hv
    refine ⟨_, hn1 i v' hv', ?_⟩
    change f (specP _ n v' - v') = specP d.QV g (f v') - f v'
    rw [map_sub, hP]
  · intro v hv
    obtain ⟨w, u, rfl, hu⟩ := exists_orthogonal_decomp f (d.restrictFix x hx).nondeg_QV v
    have hu' : specP d.QV g u = u := specP_map_apply_of_orth f _ n hu
    have hw : w ∈ (bform (d.restrictFix x hx).QV).orthogonal (d.restrictFix x hx).flag.top := by
      intro t ht
      change bform _ t w = 0
      rw [← bform_isometry f]
      have h1 : bform d.QV (f t) (f w + u) = 0 :=
        hv (f t) (by rw [d.flag_top_eq_map hx]; exact ⟨t, ht, rfl⟩)
      have h2 : bform d.QV (f t) u = 0 := by
        have := hu t
        rw [polar_eq_two_mul_bform] at this
        exact (mul_eq_zero.mp this).resolve_left (Invertible.ne_zero 2)
      rwa [map_add, h2, add_zero] at h1
    rw [map_add, hP, hu', d.flag_top_eq_map hx]
    refine ⟨_, hn2 w hw, ?_⟩
    change f (specP _ n w - w) = _
    rw [map_sub]; abel

/-- `H'_x ↪ H`. -/
theorem fixEmbed_H {h : (d.restrictFix x hx).G} (hh : h ∈ (d.restrictFix x hx).H) :
    d.fixEmbed hx h ∈ d.H := by
  show d.nPart _ ∈ d.N
  rw [nPart_fixEmbed]
  exact d.map_mem_N hx hh

/-- The restriction `H'_x → H` of `fixEmbed`. -/
def fixEmbedH : (d.restrictFix x hx).H →* d.H :=
  ((d.fixEmbed hx).comp (d.restrictFix x hx).H.subtype).codRestrict d.H
    fun h => d.fixEmbed_H hx h.2

/-- `λ ∘ fixEmbed = λ'` (`ξ_x` restricts to the character `ξ'_x` of
the GGP triple of `(W'_x, V'_x)`). -/
theorem lam_fixEmbedH (h : (d.restrictFix x hx).H) :
    d.lam (d.fixEmbedH hx h) = (d.restrictFix x hx).lam h := by
  unfold lam
  refine Finset.sum_congr rfl fun i _ => ?_
  change bform d.QV (d.zV _) (specP d.QV (d.nPart (d.fixEmbed hx h)) (d.zV _)) = _
  rw [nPart_fixEmbed, ← d.fixIsoV_zV hx, ← d.fixIsoV_zV hx, specP_map_apply, bform_isometry]

/-- `ξ ∘ fixEmbed = ξ'`. -/
theorem fixEmbed_xi (ψ : AddChar K Circle) (h : (d.restrictFix x hx).H) :
    d.xi ψ (d.fixEmbedH hx h) = (d.restrictFix x hx).xi ψ h := by
  unfold xi
  rw [lam_fixEmbedH]

/-- `x̄ ≠ 1 ⇒ W'_x ≠ W`, so `dim W'_x < dim W`. -/
theorem fixDim_lt (h1 : specP d.QW x ≠ 1) : d.fixDim x < d.m := by
  have hne : fixedSub x ≠ ⊤ := by
    intro htop
    apply h1
    refine LinearEquiv.ext fun w => ?_
    have hw : w ∈ fixedSub x := htop ▸ Submodule.mem_top
    have := LinearMap.mem_ker.mp hw
    simp only [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    exact this
  have := Submodule.finrank_lt hne
  simpa using this

/-- **Induction measure** (Thesis §7.2 (HYP)): for `x̄ = P(x) ≠ 1` the descended
datum has strictly smaller `dim G`.  (The `W`-factor alone need not drop: `dim GSpin(0) =
dim GSpin(1) = 1`; the `V`-factor does, as `dim V'_x ≥ 1`.) -/
theorem dimG_restrictFix_lt (h1 : specP d.QW x ≠ 1) : (d.restrictFix x hx).dimG < d.dimG := by
  have hlt := d.fixDim_lt h1
  have mono : ∀ a b : ℕ, a ≤ b → dimGSpin a ≤ dimGSpin b := fun a b h => by
    unfold dimGSpin
    exact Nat.add_le_add_right (Nat.div_le_div_right (Nat.mul_le_mul h (Nat.sub_le_sub_right h 1))) 1
  have strict : ∀ a b : ℕ, 1 ≤ a → a < b → dimGSpin a < dimGSpin b := fun a b ha h => by
    unfold dimGSpin
    have e : (a + 1) * (a + 1 - 1) = a * (a - 1) + 2 * a := by
      obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring_nf
    have h2 : (a + 1) * (a + 1 - 1) / 2 ≤ b * (b - 1) / 2 :=
      Nat.div_le_div_right (Nat.mul_le_mul h (by omega))
    rw [e, Nat.add_mul_div_left _ _ (by norm_num)] at h2
    omega
  change dimGSpin (d.fixDim x) + dimGSpin (d.fixDim x + 2 * d.r + 1) <
    dimGSpin d.m + dimGSpin (d.m + 2 * d.r + 1)
  exact Nat.add_lt_add_of_le_of_lt (mono _ _ hlt.le) (strict _ _ (by omega) (by omega))

/-- `P(x)` is the identity on `W'_x`. -/
theorem specP_fixIsoW (w : Fin (d.fixDim x) → K) : specP d.QW x (d.fixIsoW x w) = d.fixIsoW x w := by
  have := LinearMap.mem_ker.mp (d.fixIsoW_mem x w)
  simpa [sub_eq_zero] using this

/-- `P(x)` (in `GSpin(V)`) is the identity on `V'_x = W'_x ⊕ Z`. -/
theorem specP_incl_fixIsoV (v : (d.restrictFix x hx).V) :
    specP d.QV (d.incl x) (d.fixIsoV hx v) = d.fixIsoV hx v := by
  rw [fixIsoV_apply, show ((d.fixIsoW x v.1, v.2) : d.V) = (d.fixIsoW x v.1, 0) + (0, v.2) by simp,
    map_add, specP_incl_inl, specP_incl_inr, specP_fixIsoW]

/-- **`⊇` half for `G'_x`**: the image of `G'_x` centralizes `x`
(`GSpin(W'_x)` and `GSpin(V'_x)` commute with `x`).  No semisimplicity needed:
`x` commutes with `ι(W'_x)` and `ι(V'_x)`, hence with the subalgebras they generate. -/
theorem fixEmbed_commute_diag (g : (d.restrictFix x hx).G) :
    Commute (d.fixEmbed hx g) (d.diag x) := by
  apply d.G_ext
  · rw [map_mul, map_mul, fst_fixEmbed]
    change _ * x = x * _
    apply Subtype.ext; apply Units.ext
    exact (commute_map_of_commute_ι (d.fixIsoW x)
      (fun w => commute_ι_of_specP_eq x (d.specP_fixIsoW w)) _).eq.symm
  · rw [map_mul, map_mul, snd_fixEmbed]
    change _ * d.incl x = d.incl x * _
    apply Subtype.ext; apply Units.ext
    exact (commute_map_of_commute_ι (d.fixIsoV hx)
      (fun v => commute_ι_of_specP_eq (d.incl x) (d.specP_incl_fixIsoV hx v)) _).eq.symm

end Restrict

/-! ## 8. `H(F)\G(F)/A_G(F)` and the special orthogonal triple -/

section Quot

/-- `Ḡ(K) = SO(W)(K) × SO(V)(K)`, as a group. -/
abbrev GbarGrp : Type _ := ↥(SOGrp d.QW) × ↥(SOGrp d.QV)

/-- The surjection `G(K) → Ḡ(K)`, `(a, b) ↦ (P a, P b)`, with kernel the central `G_m × G_m`. -/
def Pbar : d.G →* d.GbarGrp :=
  (((specP d.QW).comp d.fst).codRestrict (SOGrp d.QW) fun _ =>
      show _ ∧ _ from ⟨specP_isometry _, det_specP _⟩).prod
    (((specP d.QV).comp d.snd).codRestrict (SOGrp d.QV) fun _ =>
      show _ ∧ _ from ⟨specP_isometry _, det_specP _⟩)

theorem Pbar_fst (g : d.G) : ((d.Pbar g).1 : (Fin d.m → K) ≃ₗ[K] (Fin d.m → K)) =
    specP d.QW (d.fst g) := rfl

theorem Pbar_snd (g : d.G) : ((d.Pbar g).2 : d.V ≃ₗ[K] d.V) = specP d.QV (d.snd g) := rfl

theorem Pbar_surjective : Function.Surjective d.Pbar := by
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rw [← range_specP_eq_SOGrp d.nondeg] at ha
  rw [← range_specP_eq_SOGrp d.nondeg_QV] at hb
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨d.pair (x, y), rfl⟩

theorem scalarPair_mem_AG (c₁ c₂ : Kˣ) : d.scalarPair c₁ c₂ ∈ d.AG :=
  ⟨_, ⟨scalarGSpin_mem_splitCentralGSpin _ c₁, scalarGSpin_mem_splitCentralGSpin _ c₂⟩, rfl⟩

/-- `H̄ = P(H) = SO(W) ⋉ N`. -/
abbrev Hbar : Subgroup d.GbarGrp := d.H.map d.Pbar

/-- `Ā_G = P(A_G)`, the split centre of `Ḡ`.  It is trivial unless `W` or `V` is a hyperbolic
plane, where it is `SO(W) ≅ G_m`, resp. `SO(V) ≅ G_m`. -/
abbrev AGbar : Subgroup d.GbarGrp := d.AG.map d.Pbar

/-- `P` maps `H`-`A_G` double cosets into `H̄`-`Ā_G` double cosets. -/
theorem Pbar_rel (g g' : d.G) (h : DoubleCoset.setoid (d.H : Set d.G) d.AG g g') :
    DoubleCoset.setoid (d.Hbar : Set d.GbarGrp) d.AGbar (d.Pbar g) (d.Pbar g') := by
  obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.rel_iff.mp h
  exact DoubleCoset.rel_iff.mpr ⟨d.Pbar a, ⟨a, ha, rfl⟩, d.Pbar b, ⟨b, hb, rfl⟩,
    (congrArg (· * d.Pbar b) (map_mul d.Pbar a g)).symm.trans (map_mul d.Pbar (a * g) b).symm |>.symm⟩

/-- The map `H\G/A_G → H̄\Ḡ/Ā_G` induced by `P`. -/
def quotHGMap : DoubleCoset.Quotient (d.H : Set d.G) d.AG →
    DoubleCoset.Quotient (d.Hbar : Set d.GbarGrp) d.AGbar :=
  Quotient.map' d.Pbar d.Pbar_rel

theorem quotHGMap_mk (g : d.G) :
    d.quotHGMap (DoubleCoset.mk d.H d.AG g) = DoubleCoset.mk d.Hbar d.AGbar (d.Pbar g) := rfl

theorem quotHGMap_injective : Function.Injective d.quotHGMap := by
  intro q q' hq
  induction q using Quotient.inductionOn' with | h g => ?_
  induction q' using Quotient.inductionOn' with | h g' => ?_
  have hq' : DoubleCoset.mk d.Hbar d.AGbar (d.Pbar g) = DoubleCoset.mk d.Hbar d.AGbar (d.Pbar g') :=
    hq
  obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, he⟩ := DoubleCoset.eq.mp hq'
  have he' : d.Pbar g' = d.Pbar (a * g * b) := he.trans (by rw [map_mul, map_mul])
  obtain ⟨c₁, c₂, hc⟩ := d.exists_scalarPair_of_specP_eq (g := g') (g' := a * g * b)
    (congrArg (fun p : d.GbarGrp => (p.1 : (Fin d.m → K) ≃ₗ[K] (Fin d.m → K))) he')
    (congrArg (fun p : d.GbarGrp => (p.2 : d.V ≃ₗ[K] d.V)) he')
  exact DoubleCoset.eq.mpr ⟨a, ha, b * d.scalarPair c₁ c₂,
    d.AG.mul_mem hb (d.scalarPair_mem_AG _ _), hc.trans (mul_assoc _ _ _)⟩

theorem quotHGMap_surjective : Function.Surjective d.quotHGMap := by
  intro q
  induction q using Quotient.inductionOn' with | h p => ?_
  obtain ⟨g, rfl⟩ := d.Pbar_surjective p
  exact ⟨Quotient.mk'' g, rfl⟩

/-- **The special orthogonal quotient**: `P` induces a bijection
`H(K)\G(K)/A_G(K) ≃ H̄(K)\Ḡ(K)/Ā_G(K)`.  (Injectivity: the kernel `G_m × G_m` of `P` lies in
`A_G`; surjectivity: `gspin_specP_surjective_SO`.)  When `Ā_G = 1`, i.e. neither factor is a
hyperbolic plane, this is `H\G/A_G ≃ H̄\Ḡ` (`quotHG_equiv_SO`). -/
def quotHG_equiv : DoubleCoset.Quotient (d.H : Set d.G) d.AG ≃
    DoubleCoset.Quotient (d.Hbar : Set d.GbarGrp) d.AGbar :=
  Equiv.ofBijective d.quotHGMap ⟨d.quotHGMap_injective, d.quotHGMap_surjective⟩

/-- When neither `W` nor `V` is a hyperbolic plane, `A_G = G_m × G_m` maps to `1` in `Ḡ`. -/
theorem AGbar_eq_bot (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) : d.AGbar = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨g, ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩, rfl⟩
  have ha' : a ∈ (scalarGSpin d.QW).range := by
    unfold splitCentralGSpin at ha; rwa [ite_eq_right_of_eq_false _ _ (eq_false hW)] at ha
  have hb' : b ∈ (scalarGSpin d.QV).range := by
    unfold splitCentralGSpin at hb; rwa [ite_eq_right_of_eq_false _ _ (eq_false hV)] at hb
  obtain ⟨c₁, rfl⟩ := ha'
  obtain ⟨c₂, rfl⟩ := hb'
  refine (Subgroup.mem_bot).mpr (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · exact specP_scalarGSpin_eq_one c₁
  · exact specP_scalarGSpin_eq_one c₂

/-- **The special orthogonal quotient, without `Ā_G`**: if neither `W` nor
`V` is a hyperbolic plane, `H(K)\G(K)/A_G(K) ≃ H̄(K)\Ḡ(K)`.  The hypothesis is needed (e.g.
`dim W = 1`, `r = 0`, `V` hyperbolic: the left side is a point, the right side `SO(V)(K) ≅ K^×`); the
general form is `quotHG_equiv`. -/
def quotHG_equiv_SO (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) :
    DoubleCoset.Quotient (d.H : Set d.G) d.AG ≃ Quotient (QuotientGroup.rightRel d.Hbar) :=
  d.quotHG_equiv.trans (Quotient.congr (Equiv.refl _) fun p q => by
    rw [Equiv.refl_apply, Equiv.refl_apply, QuotientGroup.rightRel_apply,
      show (DoubleCoset.setoid (d.Hbar : Set d.GbarGrp) d.AGbar) p q ↔ _ from DoubleCoset.rel_iff,
      d.AGbar_eq_bot hW hV]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      rw [Subgroup.mem_bot] at hb
      rw [hb, mul_one, mul_inv_cancel_right]; exact ha
    · intro h
      exact ⟨q * p⁻¹, h, 1, Subgroup.one_mem _, by rw [mul_one, inv_mul_cancel_right]⟩)

end Quot

end GGPData

namespace GGPData

/-! ## 9. The centralizer of `x` in `G` -/

section CentralizerG

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)
variable {x : GSpin d.QW} (hx : IsNondeg (d.QW.comp (fixedSub x).subtype))

/-- `W'_x` is the range of `W'_x ↪ W`. -/
theorem fixIsoW_range (w : Fin d.m → F) : w ∈ fixedSub x ↔ ∃ v, d.fixIsoW x v = w :=
  ⟨fun hw => d.fixIsoW_surj x hw, fun ⟨v, hv⟩ => hv ▸ d.fixIsoW_mem x v⟩

/-- `V'_x = W'_x ⊕ Z = ker(P(x) − 1) ⊆ V` is the range of `V'_x ↪ V`. -/
theorem fixIsoV_range (w : d.V) : w ∈ fixedSub (d.incl x) ↔ ∃ v, d.fixIsoV hx v = w := by
  obtain ⟨w₁, z⟩ := w
  have e : specP d.QV (d.incl x) (w₁, z) = (specP d.QW x w₁, z) := by
    rw [show ((w₁, z) : d.V) = (w₁, 0) + (0, z) by simp, map_add, specP_incl_inl,
      specP_incl_inr]
    simp
  have hmem : (w₁, z) ∈ fixedSub (d.incl x) ↔ w₁ ∈ fixedSub x := by
    simp only [fixedSub, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    change specP d.QV (d.incl x) (w₁, z) = (w₁, z) ↔ specP d.QW x w₁ = w₁
    rw [e, Prod.mk.injEq]
    simp
  rw [hmem, d.fixIsoW_range]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨(v, z), rfl⟩
  · rintro ⟨v, hv⟩
    exact ⟨v.1, congrArg Prod.fst hv⟩

/-- The second torus factor of `G''_x`: `GSpin(W''_x)_x` inside `GSpin(V)`, i.e. the elements of
`GSpin(V)` commuting with `x` and fixing `V'_x` pointwise. -/
def torusV (x : GSpin d.QW) : Subgroup (GSpin d.QV) :=
  Subgroup.centralizer {d.incl x} ⊓ fixerOf d.QV (fixedSub (d.incl x))

/-- **The centralizer of `x` in `G`** (Thesis §6.5 (6.5.1)): for semisimple
`x ∈ GSpin(W)(F)` (embedded diagonally),
`Z_G(x) = G'_x · (T_x × 1) · (1 × T'_x)`, where `G'_x = GSpin(W'_x) × GSpin(V'_x)` is embedded by
`fixEmbed`, `T_x = torusOf x ⊆ GSpin(W)` and `T'_x = torusV x ⊆ GSpin(V)` are the two copies of
`GSpin(W''_x)_x`.  Uses Steinberg (`steinberg_centralizer_connected'`) on both factors, hence the
semisimplicity of `x` in `C(W)` and of its image in `C(V)` (the latter is not derived from the
former here). -/
theorem centralizer_diag_eq
    (hss : IsSS F ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
    (hss' : IsSS F ((d.incl x : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) :
    Subgroup.centralizer {d.diag x} =
      (d.fixEmbed hx).range ⊔ (d.torusOf x).map (d.pair.comp (MonoidHom.inl _ _)) ⊔
        (d.torusV x).map d.inr := by
  apply le_antisymm
  · intro g hg
    have hg' : g * d.diag x = d.diag x * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have h1 : d.fst g * x = x * d.fst g := by
      have := congrArg d.fst hg'
      rwa [map_mul, map_mul] at this
    have h2 : d.snd g * d.incl x = d.incl x * d.snd g := by
      have := congrArg d.snd hg'
      rwa [map_mul, map_mul] at this
    obtain ⟨a', t₁, ht₁, ha⟩ := exists_map_mul_of_commute d.nondeg (d.fixIsoW x)
      (d.restrictFix x hx).nondeg hss (d.fixIsoW_range) h1
    obtain ⟨b', t₂, ht₂, hb⟩ := exists_map_mul_of_commute d.nondeg_QV (d.fixIsoV hx)
      (d.restrictFix x hx).nondeg_QV hss' (d.fixIsoV_range hx) h2
    have e : g = d.fixEmbed hx ((d.restrictFix x hx).pair (a', b')) * d.pair (t₁, 1) *
        d.inr t₂ := by
      apply d.G_ext
      · simp only [map_mul]
        change d.fst g = GSpin.map (d.fixIsoW x) (d.restrictFix x hx).nondeg a' * t₁ * 1
        rw [mul_one, ha]
      · simp only [map_mul]
        change d.snd g = GSpin.map (d.fixIsoV hx) (d.restrictFix x hx).nondeg_QV b' * 1 * t₂
        rw [mul_one, hb]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨_, rfl⟩))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨t₁, ht₁, rfl⟩)))
      (Subgroup.mem_sup_right ⟨t₂, ht₂, rfl⟩)
  · refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨g, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (d.fixEmbed_commute_diag hx g)
    · rintro _ ⟨t, ht, rfl⟩
      have ht' : t * x = x * t := Subgroup.mem_centralizer_singleton_iff.mp ht.1
      refine Subgroup.mem_centralizer_singleton_iff.mpr (d.G_ext ?_ ?_)
      · simp only [map_mul]
        exact ht'
      · simp only [map_mul]
        change 1 * d.incl x = d.incl x * 1
        rw [one_mul, mul_one]
    · rintro _ ⟨t, ht, rfl⟩
      have ht' : t * d.incl x = d.incl x * t := Subgroup.mem_centralizer_singleton_iff.mp ht.1
      refine Subgroup.mem_centralizer_singleton_iff.mpr (d.G_ext ?_ ?_)
      · simp only [map_mul]
        change 1 * x = x * 1
        rw [one_mul, mul_one]
      · simp only [map_mul]
        exact ht'

/-- `GSpin(W) → GSpin(V)` is injective (its kernel would be scalars acting trivially). -/
theorem incl_injective : Function.Injective d.incl := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro k hk
  rw [MonoidHom.mem_ker] at hk
  have hP : specP d.QW k = 1 := LinearEquiv.ext fun w => by
    have h := d.specP_incl_inl k w
    rw [hk, map_one] at h
    exact (congrArg Prod.fst h).symm
  obtain ⟨c, rfl⟩ : k ∈ (scalarGSpin d.QW).range := by rw [← ker_specP d.nondeg]; exact hP
  rw [incl_scalarGSpin] at hk
  have hc : (c : F) = 1 := by
    have := congrArg (fun g : GSpin d.QV => ((g : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV))
      hk
    simp only [scalarGSpin, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, OneMemClass.coe_one, Units.val_one] at this
    exact (algebraMap F (CliffordAlgebra d.QV)).injective (this.trans (map_one _).symm)
  rw [Subgroup.mem_bot, show c = 1 from Units.ext hc, map_one]

/-- `P(incl a)(w, z) = (P(a) w, z)`. -/
theorem specP_incl_apply (a : GSpin d.QW) (w : Fin d.m → F) (z : d.Z) :
    specP d.QV (d.incl a) (w, z) = (specP d.QW a w, z) := by
  rw [show ((w, z) : d.V) = (w, 0) + (0, z) by simp, map_add, specP_incl_inl, specP_incl_inr]
  simp

/-- `V'_x = W'_x ⊕ Z`: `(w, z)` is fixed by `x` iff `w` is. -/
theorem mem_fixedSub_incl_iff (a : GSpin d.QW) (w : Fin d.m → F) (z : d.Z) :
    ((w, z) : d.V) ∈ fixedSub (d.incl a) ↔ w ∈ fixedSub a := by
  simp only [fixedSub, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  change specP d.QV (d.incl a) (w, z) = (w, z) ↔ specP d.QW a w = w
  rw [specP_incl_apply, Prod.mk.injEq]
  simp

/-- `P(s)` preserves `W = Z^⊥` when it fixes `Z` pointwise. -/
theorem specP_snd_eq_zero_of_fix_Z {s : GSpin d.QV} (hZ : ∀ z : d.Z, specP d.QV s (0, z) = (0, z))
    (w : Fin d.m → F) : (specP d.QV s (w, 0)).2 = 0 := by
  refine (isNondeg_iff d.QZ).mp (isNondeg_splitOddForm d.r d.ν.ne_zero) _ fun z => ?_
  have h := bform_specP s (w, 0) (0, z)
  rw [hZ, bform_prod, bform_prod] at h
  have h0 : bform d.QW (specP d.QV s (w, 0)).1 0 = 0 := by simp
  have h1 : bform d.QW w 0 + bform d.QZ 0 z = 0 := by simp
  rw [h0, zero_add, h1] at h
  exact h

/-- An element of `GSpin(V)` fixing `Z = W^⊥` pointwise comes from `GSpin(W)` (uses
`gspin_specP_surjective_SO` on `W` and `ker P = G_m`). -/
theorem exists_incl_eq_of_fix_Z {s : GSpin d.QV}
    (hZ : ∀ z : d.Z, specP d.QV s (0, z) = (0, z)) : ∃ u, d.incl u = s := by
  let r : (Fin d.m → F) →ₗ[F] (Fin d.m → F) :=
    LinearMap.fst F _ _ ∘ₗ (specP d.QV s : d.V →ₗ[F] d.V) ∘ₗ LinearMap.inl F _ _
  have hr : ∀ w, specP d.QV s (w, 0) = (r w, 0) := fun w =>
    Prod.ext rfl (d.specP_snd_eq_zero_of_fix_Z hZ w)
  have hsplit : ∀ w z, specP d.QV s (w, z) = (r w, z) := fun w z => by
    rw [show ((w, z) : d.V) = (w, 0) + (0, z) by simp, map_add, hr, hZ]
    simp
  have hprod : (specP d.QV s : d.V →ₗ[F] d.V) = r.prodMap LinearMap.id :=
    LinearMap.ext fun v => hsplit v.1 v.2
  have hdet : LinearMap.det r = 1 := by
    have h := det_specP s
    rw [hprod, LinearMap.det_prodMap, LinearMap.det_id, mul_one] at h
    exact h
  have rinj : Function.Injective r := fun a b hab => by
    have h : specP d.QV s (a, 0) = specP d.QV s (b, 0) := by rw [hr, hr, hab]
    exact congrArg Prod.fst ((specP d.QV s).injective h)
  let rE := LinearEquiv.ofInjectiveEndo r rinj
  have hiso : ∀ w, d.QW (rE w) = d.QW w := fun w => by
    have h := specP_isometry s (w, 0)
    rw [hr] at h
    change d.QW (r w) + d.QZ 0 = d.QW w + d.QZ 0 at h
    exact add_right_cancel h
  obtain ⟨u₀, hu₀⟩ := gspin_specP_surjective_SO d.QW d.nondeg rE hiso hdet
  have hPu₀ : specP d.QV (d.incl u₀) = specP d.QV s := LinearEquiv.ext fun v => by
    rw [specP_incl_apply, hsplit, hu₀]
    rfl
  obtain ⟨c, hc⟩ : (d.incl u₀)⁻¹ * s ∈ (scalarGSpin d.QV).range := by
    rw [← ker_specP d.nondeg_QV, MonoidHom.mem_ker, map_mul, map_inv, hPu₀, inv_mul_cancel]
  refine ⟨u₀ * scalarGSpin d.QW c, ?_⟩
  rw [map_mul, incl_scalarGSpin, hc, mul_inv_cancel_left]

/-- **The two torus factors agree** (`GSpin(W''_x)_x` sits in both
`GSpin(W)` and `GSpin(V)`): `torusV x = incl(T_x)`.  So `centralizer_diag_eq` is
`Z_G(x) = G'_x · G''_x` with `G''_x = T_x × T_x`. -/
theorem torusV_eq_map_torusOf (x : GSpin d.QW) : d.torusV x = (d.torusOf x).map d.incl := by
  apply le_antisymm
  · rintro s ⟨hs1, hs2⟩
    have hsx : s * d.incl x = d.incl x * s := Subgroup.mem_centralizer_singleton_iff.mp hs1
    have hZ : ∀ z : d.Z, specP d.QV s (0, z) = (0, z) := fun z =>
      hs2 _ ((d.mem_fixedSub_incl_iff x 0 z).mpr (zero_mem _))
    obtain ⟨u, hu⟩ := d.exists_incl_eq_of_fix_Z hZ
    refine ⟨u, ⟨?_, fun w hw => ?_⟩, hu⟩
    · show u ∈ Subgroup.centralizer {x}
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply d.incl_injective
      rw [map_mul, map_mul, hu, hsx]
    · have h := hs2 _ ((d.mem_fixedSub_incl_iff x w 0).mpr hw)
      rw [← hu, specP_incl_apply] at h
      exact congrArg Prod.fst h
  · rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
    refine ⟨?_, fun v hv => ?_⟩
    · have ht : t * x = x * t := Subgroup.mem_centralizer_singleton_iff.mp ht1
      show d.incl t ∈ Subgroup.centralizer {d.incl x}
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, ht]
    · obtain ⟨w, z⟩ := v
      rw [specP_incl_apply, ht2 w ((d.mem_fixedSub_incl_iff x w z).mp hv)]

/-- **The centralizer of `x`, product form**: `Z_G(x)` is generated by
`G'_x = GSpin(W'_x) × GSpin(V'_x)` and `G''_x = T_x × T_x`, `T_x = GSpin(W''_x)_x = torusOf x`
(first copy in `GSpin(W)`, second in `GSpin(V)` via `incl`). -/
theorem centralizer_diag_eq'
    (hss : IsSS F ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
    (hss' : IsSS F ((d.incl x : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) :
    Subgroup.centralizer {d.diag x} =
      (d.fixEmbed hx).range ⊔ (d.torusOf x).map (d.pair.comp (MonoidHom.inl _ _)) ⊔
        ((d.torusOf x).map d.incl).map d.inr := by
  rw [← d.torusV_eq_map_torusOf]
  exact d.centralizer_diag_eq hx hss hss'

/-- `x` semisimple in `C(W)` ⇒ `x` semisimple in `C(V)`. -/
theorem isSS_incl (hss : IsSS F ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) :
    IsSS F ((d.incl x : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) :=
  isSS_algHom (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)) hss

/-- **The centralizer of `x`, final form**: for semisimple `x ∈ GSpin(W)(F)` with
`W'_x` nondegenerate, `Z_G(x) = G'_x · (T_x × T_x)`. -/
theorem centralizer_diag_eq_of_isSS
    (hss : IsSS F ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) :
    Subgroup.centralizer {d.diag x} =
      (d.fixEmbed hx).range ⊔ (d.torusOf x).map (d.pair.comp (MonoidHom.inl _ _)) ⊔
        ((d.torusOf x).map d.incl).map d.inr :=
  d.centralizer_diag_eq' hx hss (d.isSS_incl hss)

end CentralizerG

end GGPData

end GSpinGGP
