/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.SubgroupTransport
import GSpinGGP.TraceFormula.SOLie

/-!
# Facts about Luo's subgroup `H̄ = SO(W) ⋉ N` and its tori

Elementary facts about the objects of `TraceFormula/SOLie.lean` (Luo, arXiv:2009.13947v1, §2.1,
§7.1).

## Main results
* `LuoDatum.NsetSub`: the unipotent radical `N` is a subgroup of `GL(V)`.
* `LuoDatum.extU_conj_mem_Nset`: `SO(W)` (acting by `g ⊕ 1`) normalizes `N`.
* `LuoDatum.mem_HbarU_iff`: **normal form**, every element of `H̄` is `(g, (g ⊕ 1) n)` with
  `g ∈ SO(W)`, `n ∈ N` (`H̄ = SO(W) ⋉ N`, Luo §2.1); `g` and `n` are unique
  (`diagU_mul_inrU_inj`).
* `LuoDatum.diagU_mul_inrU_conj_diagU_eq_iff`, `LuoDatum.commute_diagU_mul_inrU_diagU_iff`:
  `(g, (g ⊕ 1) n)` conjugates `(t, t ⊕ 1)` to `(s, s ⊕ 1)` iff `g t g⁻¹ = s` and `n` commutes with
  `t ⊕ 1`; in particular `H̄_t = SO(W)_t ⋉ N_t` (Luo §7.1, (7.1.1)).
* `LuoDatum.torusConj_equivalence`: `H̄(F)`-conjugacy of tori is an equivalence relation.
* `LuoDatum.weylCardOf_map_conj`, `LuoDatum.weylCardOf_eq_of_torusConj`: `|W(H̄, T)|` is invariant
  under `H̄(F)`-conjugation.
-/

noncomputable section


namespace GSpinGGP

namespace LuoDatum

section Basic

variable {K : Type*} [Field K] [Invertible (2 : K)] (L : LuoDatum K)

/-! ## Components of `diagU` and `inrU` -/

@[simp] theorem unitFst_diagU (g : (Module.End K L.W)ˣ) : L.unitFst (L.diagU g) = g :=
  Units.ext rfl

@[simp] theorem unitSnd_diagU (g : (Module.End K L.W)ˣ) :
    L.unitSnd (L.diagU g) = Units.map L.extGrp g :=
  Units.ext rfl

@[simp] theorem unitFst_inrU (n : (Module.End K L.V)ˣ) : L.unitFst (L.inrU n) = 1 :=
  Units.ext rfl

@[simp] theorem unitSnd_inrU (n : (Module.End K L.V)ˣ) : L.unitSnd (L.inrU n) = n :=
  Units.ext rfl

theorem val_diagU (g : (Module.End K L.W)ˣ) :
    ((L.diagU g : L.Ambˣ) : L.Amb) = ((g : Module.End K L.W), L.extGrp g) := rfl

theorem val_inrU (n : (Module.End K L.V)ˣ) :
    ((L.inrU n : L.Ambˣ) : L.Amb) = ((1 : Module.End K L.W), (n : Module.End K L.V)) := rfl

theorem extGrp_apply (f : Module.End K L.W) (v : L.V) : L.extGrp f v = (f v.1, v.2) := rfl

/-! ## The flag and `g ⊕ 1` -/

/-- The vectors of `Z_k` have zero `W`-component. -/
theorem fst_eq_zero_of_mem_flagSub {k : ℕ} {v : L.V} (hv : v ∈ L.flagSub k) : v.1 = 0 := by
  have : L.flagSub k ≤ LinearMap.ker (LinearMap.fst K L.W L.Zs) := by
    rw [flagSub, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rfl
  exact this hv

/-- `g ⊕ 1` fixes `Z_k` pointwise. -/
theorem extGrp_apply_of_mem_flagSub (f : Module.End K L.W) {k : ℕ} {v : L.V}
    (hv : v ∈ L.flagSub k) : L.extGrp f v = v := by
  rw [extGrp_apply, L.fst_eq_zero_of_mem_flagSub hv, map_zero]
  exact Prod.ext (L.fst_eq_zero_of_mem_flagSub hv).symm rfl

/-- `g ⊕ 1` preserves `Z_k^⊥`. -/
theorem extGrp_apply_mem_orthogonal (f : Module.End K L.W) {k : ℕ} {v : L.V}
    (hv : v ∈ (bform L.QV).orthogonal (L.flagSub k)) :
    L.extGrp f v ∈ (bform L.QV).orthogonal (L.flagSub k) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
  intro u hu
  have h := hv u hu
  rw [bform_prod] at h ⊢
  rw [L.fst_eq_zero_of_mem_flagSub hu, map_zero, LinearMap.zero_apply] at h ⊢
  exact h

/-- The flag is increasing: `Z_k ⊆ Z_{k+1}`. -/
theorem flagSub_le_succ (k : ℕ) : L.flagSub k ≤ L.flagSub (k + 1) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩
  exact ⟨Fin.castSucc j, rfl⟩

/-- `SO(W) ⊆ SO(V)`, `g ↦ g ⊕ 1`. -/
theorem extU_mem_SOu {g : (Module.End K L.W)ˣ} (hg : g ∈ SOu L.QW) :
    Units.map L.extGrp g ∈ SOu L.QV := by
  obtain ⟨hQ, hdet⟩ := hg
  refine ⟨fun v => ?_, ?_⟩
  · change L.QV (L.extGrp g v) = L.QV v
    rw [extGrp_apply]
    simp only [QuadraticMap.prod_apply]
    rw [show L.QW ((g : Module.End K L.W) v.1) = L.QW v.1 from hQ v.1]
  · change LinearMap.det (L.extGrp (g : Module.End K L.W)) = 1
    rw [show L.extGrp (g : Module.End K L.W) = LinearMap.prodMap (g : Module.End K L.W) 1 from
      rfl, LinearMap.det_prodMap, map_one, mul_one]
    exact hdet

/-! ## `N` is a subgroup normalized by `SO(W)` -/

/-- An element of `N` maps `Z_k` (`k ≤ r`) into itself. -/
theorem apply_mem_flagSub_of_mem_Nset {n : (Module.End K L.V)ˣ} (hn : n ∈ L.Nset) {k : ℕ}
    (hk : k ≤ L.r) {v : L.V} (hv : v ∈ L.flagSub k) : (n : Module.End K L.V) v ∈ L.flagSub k := by
  cases k with
  | zero =>
    have : L.flagSub 0 = ⊥ := by
      rw [flagSub, Set.range_eq_empty, Submodule.span_empty]
    rw [this, Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]
  | succ k =>
    have h := hn.2.1 k (by omega) v hv
    rw [show (n : Module.End K L.V) v = v + ((n : Module.End K L.V) v - v) by abel]
    exact add_mem hv (L.flagSub_le_succ k h)

/-- The inverse of an element of `N` maps `Z_k` (`k ≤ r`) into itself (`n` restricts to an
injective, hence bijective, endomorphism of the finite-dimensional `Z_k`). -/
theorem inv_apply_mem_flagSub_of_mem_Nset {n : (Module.End K L.V)ˣ} (hn : n ∈ L.Nset) {k : ℕ}
    (hk : k ≤ L.r) {v : L.V} (hv : v ∈ L.flagSub k) :
    ((n⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V) v ∈ L.flagSub k := by
  let f : L.flagSub k →ₗ[K] L.flagSub k :=
    (n : Module.End K L.V).restrict fun _ hw => L.apply_mem_flagSub_of_mem_Nset hn hk hw
  have hinj : Function.Injective f := by
    intro a b hab
    have h : (n : Module.End K L.V) a = (n : Module.End K L.V) b := congrArg Subtype.val hab
    exact Subtype.ext (((Module.End.isUnit_iff _).1 n.isUnit).1 h)
  obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨v, hv⟩
  have hw' : (n : Module.End K L.V) w = v := congrArg Subtype.val hw
  rw [← hw', ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
  exact w.2

/-- `N` is a subgroup of `GL(V)`. -/
def NsetSub : Subgroup (Module.End K L.V)ˣ where
  carrier := L.Nset
  one_mem' := ⟨(SOu L.QV).one_mem, fun _ _ v _ => by simp, fun v _ => by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨(SOu L.QV).mul_mem ha.1 hb.1,
    fun k hk v hv => by
      rw [Units.val_mul, Module.End.mul_apply,
        show (a : Module.End K L.V) ((b : Module.End K L.V) v) - v =
          (a : Module.End K L.V) ((b : Module.End K L.V) v - v) +
            ((a : Module.End K L.V) v - v) by rw [map_sub]; abel]
      exact add_mem (L.apply_mem_flagSub_of_mem_Nset ha (by omega) (hb.2.1 k hk v hv))
        (ha.2.1 k hk v hv),
    fun v hv => by
      rw [Units.val_mul, Module.End.mul_apply,
        show (a : Module.End K L.V) ((b : Module.End K L.V) v) - v =
          (a : Module.End K L.V) ((b : Module.End K L.V) v - v) +
            ((a : Module.End K L.V) v - v) by rw [map_sub]; abel]
      exact add_mem (L.apply_mem_flagSub_of_mem_Nset ha le_rfl (hb.2.2 v hv)) (ha.2.2 v hv)⟩
  inv_mem' := fun {a} ha => by
    have key : ∀ v : L.V, ((a⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V) v - v =
        -((a⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V) ((a : Module.End K L.V) v - v) := by
      intro v
      rw [map_sub, ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
      abel
    refine ⟨(SOu L.QV).inv_mem ha.1, fun k hk v hv => ?_, fun v hv => ?_⟩
    · rw [key]
      exact neg_mem (L.inv_apply_mem_flagSub_of_mem_Nset ha (by omega) (ha.2.1 k hk v hv))
    · rw [key]
      exact neg_mem (L.inv_apply_mem_flagSub_of_mem_Nset ha le_rfl (ha.2.2 v hv))

@[simp] theorem mem_NsetSub {n : (Module.End K L.V)ˣ} : n ∈ L.NsetSub ↔ n ∈ L.Nset := Iff.rfl

/-- **`SO(W)` normalizes `N`** (Luo §2.1): for `g ∈ SO(W)` and `n ∈ N`,
`(g ⊕ 1) n (g ⊕ 1)⁻¹ ∈ N`. -/
theorem extU_conj_mem_Nset {g : (Module.End K L.W)ˣ} (hg : g ∈ SOu L.QW)
    {n : (Module.End K L.V)ˣ} (hn : n ∈ L.Nset) :
    Units.map L.extGrp g * n * (Units.map L.extGrp g)⁻¹ ∈ L.Nset := by
  have he := L.extU_mem_SOu hg
  set e := Units.map L.extGrp g with he_def
  -- `e n e⁻¹ v - v = e (n u - u)` with `u = e⁻¹ v`.
  have key : ∀ v : L.V, ((e * n * e⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V) v - v =
      (e : Module.End K L.V) ((n : Module.End K L.V)
          (((e⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V) v) -
        ((e⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V) v) := by
    intro v
    rw [map_sub, ← Module.End.mul_apply (e : Module.End K L.V)
      ((e⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V), Units.mul_inv, Module.End.one_apply]
    rfl
  have he_val : (e : Module.End K L.V) = L.extGrp (g : Module.End K L.W) := rfl
  have heinv_val : ((e⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V) =
      L.extGrp ((g⁻¹ : (Module.End K L.W)ˣ) : Module.End K L.W) := by
    rw [he_def, ← map_inv]; rfl
  refine ⟨(SOu L.QV).mul_mem ((SOu L.QV).mul_mem he hn.1) ((SOu L.QV).inv_mem he),
    fun k hk v hv => ?_, fun v hv => ?_⟩
  · rw [key, heinv_val, L.extGrp_apply_of_mem_flagSub _ hv, he_val]
    have h := hn.2.1 k hk v hv
    rw [L.extGrp_apply_of_mem_flagSub _ h]
    exact h
  · rw [key, heinv_val, he_val]
    have h := hn.2.2 _
      (L.extGrp_apply_mem_orthogonal ((g⁻¹ : (Module.End K L.W)ˣ) : Module.End K L.W) hv)
    rw [L.extGrp_apply_of_mem_flagSub _ h]
    exact h

/-! ## The normal form `H̄ = SO(W) ⋉ N` -/

/-- Moving `(1, n)` past `(g, g ⊕ 1)`: `(1, n) (g, g ⊕ 1) = (g, g ⊕ 1) (1, (g ⊕ 1)⁻¹ n (g ⊕ 1))`. -/
theorem inrU_mul_diagU (g : (Module.End K L.W)ˣ) (n : (Module.End K L.V)ˣ) :
    L.inrU n * L.diagU g =
      L.diagU g * L.inrU ((Units.map L.extGrp g)⁻¹ * n * Units.map L.extGrp g) := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change (1 : Module.End K L.W) * (g : Module.End K L.W) = (g : Module.End K L.W) * 1
    rw [one_mul, mul_one]
  · set e := Units.map L.extGrp g
    change (n : Module.End K L.V) * (e : Module.End K L.V) = (e : Module.End K L.V) *
      (((e⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V) * (n : Module.End K L.V) *
        (e : Module.End K L.V))
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]

/-- **Normal form for `H̄ = SO(W) ⋉ N`** (Luo §2.1): the elements of `H̄` are exactly the
products `(g, g ⊕ 1)(1, n) = (g, (g ⊕ 1) n)` with `g ∈ SO(W)` and `n ∈ N`. -/
theorem mem_HbarU_iff {u : L.Ambˣ} :
    u ∈ L.HbarU ↔ ∃ g ∈ SOu L.QW, ∃ n ∈ L.Nset, u = L.diagU g * L.inrU n := by
  constructor
  · intro hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨g, hg, rfl⟩ | ⟨n, hn, rfl⟩
      · exact ⟨g, hg, 1, L.NsetSub.one_mem, by simp⟩
      · exact ⟨1, (SOu L.QW).one_mem, n, hn, by simp⟩
    | one => exact ⟨1, (SOu L.QW).one_mem, 1, L.NsetSub.one_mem, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨g, hg, n, hn, rfl⟩ := hx
      obtain ⟨g', hg', n', hn', rfl⟩ := hy
      refine ⟨g * g', (SOu L.QW).mul_mem hg hg',
        (Units.map L.extGrp g')⁻¹ * n * Units.map L.extGrp g' * n', ?_, ?_⟩
      · refine L.NsetSub.mul_mem ?_ hn'
        have := L.extU_conj_mem_Nset ((SOu L.QW).inv_mem hg') hn
        simpa [map_inv] using this
      · rw [mul_assoc, ← mul_assoc (L.inrU n), inrU_mul_diagU]
        simp only [map_mul, mul_assoc]
    | inv x _ hx =>
      obtain ⟨g, hg, n, hn, rfl⟩ := hx
      refine ⟨g⁻¹, (SOu L.QW).inv_mem hg,
        (Units.map L.extGrp g⁻¹)⁻¹ * n⁻¹ * Units.map L.extGrp g⁻¹, ?_, ?_⟩
      · have := L.extU_conj_mem_Nset hg (L.NsetSub.inv_mem hn)
        simpa [map_inv] using this
      · rw [mul_inv_rev, ← map_inv, ← map_inv, inrU_mul_diagU]
  · rintro ⟨g, hg, n, hn, rfl⟩
    exact L.HbarU.mul_mem (Subgroup.subset_closure (Or.inl ⟨g, hg, rfl⟩))
      (Subgroup.subset_closure (Or.inr ⟨n, hn, rfl⟩))

/-- In the normal form `(g, (g ⊕ 1) n)`, `g` is the `GL(W)`-component. -/
theorem unitFst_diagU_mul_inrU (g : (Module.End K L.W)ˣ) (n : (Module.End K L.V)ˣ) :
    L.unitFst (L.diagU g * L.inrU n) = g := by simp

/-- In the normal form `(g, (g ⊕ 1) n)`, the `GL(V)`-component is `(g ⊕ 1) n`. -/
theorem unitSnd_diagU_mul_inrU (g : (Module.End K L.W)ˣ) (n : (Module.End K L.V)ˣ) :
    L.unitSnd (L.diagU g * L.inrU n) = Units.map L.extGrp g * n := by simp

/-- **Uniqueness of the normal form**: `(g, (g ⊕ 1) n)` determines `g` and `n`. -/
theorem diagU_mul_inrU_inj {g g' : (Module.End K L.W)ˣ} {n n' : (Module.End K L.V)ˣ} :
    L.diagU g * L.inrU n = L.diagU g' * L.inrU n' ↔ g = g' ∧ n = n' := by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => h₁ ▸ h₂ ▸ rfl⟩
  have h₁ := congrArg L.unitFst h
  have h₂ := congrArg L.unitSnd h
  rw [unitFst_diagU_mul_inrU, unitFst_diagU_mul_inrU] at h₁
  rw [unitSnd_diagU_mul_inrU, unitSnd_diagU_mul_inrU, h₁] at h₂
  exact ⟨h₁, mul_left_cancel h₂⟩

/-- **Conjugating the diagonal torus** (Luo §7.1): `(g, (g ⊕ 1) n)` conjugates `(t, t ⊕ 1)` to
`(s, s ⊕ 1)` iff `g t g⁻¹ = s` and `n` commutes with `t ⊕ 1`. -/
theorem diagU_mul_inrU_conj_diagU_eq_iff (g t s : (Module.End K L.W)ˣ)
    (n : (Module.End K L.V)ˣ) :
    (L.diagU g * L.inrU n) * L.diagU t * (L.diagU g * L.inrU n)⁻¹ = L.diagU s ↔
      g * t * g⁻¹ = s ∧ n * Units.map L.extGrp t = Units.map L.extGrp t * n := by
  constructor
  · intro h
    have h₁ := congrArg L.unitFst h
    have h₂ := congrArg L.unitSnd h
    simp only [map_mul, map_inv, unitFst_diagU, unitSnd_diagU, unitFst_inrU, unitSnd_inrU,
      mul_one] at h₁ h₂
    subst h₁
    refine ⟨rfl, ?_⟩
    rw [← mul_inv_eq_iff_eq_mul]
    apply (MulAut.conj (Units.map L.extGrp g)).injective
    rw [map_mul, map_mul, map_inv] at h₂
    set e := Units.map L.extGrp g
    set τ := Units.map L.extGrp t
    have h3 : n * τ * n⁻¹ = τ := (MulAut.conj e).injective (by
      simp only [MulAut.conj_apply]
      rw [← h₂]
      group)
    simp only [MulAut.conj_apply]
    rw [h3]
  · rintro ⟨rfl, hc⟩
    have hn : (Units.map L.extGrp t)⁻¹ * n * Units.map L.extGrp t = n := by
      rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
    calc (L.diagU g * L.inrU n) * L.diagU t * (L.diagU g * L.inrU n)⁻¹
        = L.diagU g * (L.inrU n * L.diagU t) * (L.inrU n)⁻¹ * (L.diagU g)⁻¹ := by group
      _ = L.diagU g * L.diagU t * (L.diagU g)⁻¹ := by rw [inrU_mul_diagU, hn]; group
      _ = L.diagU (g * t * g⁻¹) := by simp only [map_mul, map_inv]

/-- **`H̄_t = SO(W)_t ⋉ N_t`** (Luo §7.1, (7.1.1)): `(g, (g ⊕ 1) n)` commutes with
`(t, t ⊕ 1)` iff `g` commutes with `t` and `n` with `t ⊕ 1`. -/
theorem commute_diagU_mul_inrU_diagU_iff (g t : (Module.End K L.W)ˣ)
    (n : (Module.End K L.V)ˣ) :
    Commute (L.diagU g * L.inrU n) (L.diagU t) ↔
      Commute g t ∧ Commute n (Units.map L.extGrp t) := by
  rw [Commute, SemiconjBy, Commute, SemiconjBy, Commute, SemiconjBy,
    ← mul_inv_eq_iff_eq_mul, diagU_mul_inrU_conj_diagU_eq_iff, mul_inv_eq_iff_eq_mul]

/-- **`n` centralizes the torus** (Luo §7.1): if `(g, (g ⊕ 1) n)` conjugates every element of
`H''_X` (embedded diagonally) to a diagonal element `(s, s ⊕ 1)` (e.g. if it normalizes the
torus), then `n` commutes with `t ⊕ 1` for every `t ∈ H''_X`. -/
theorem commute_extU_of_conj_torusOf {g : (Module.End K L.W)ˣ} {n : (Module.End K L.V)ˣ}
    {X : Module.End K L.W}
    (h : ∀ a ∈ L.torusOf X, ∃ s : (Module.End K L.W)ˣ,
      (L.diagU g * L.inrU n) * a * (L.diagU g * L.inrU n)⁻¹ = L.diagU s)
    {t : (Module.End K L.W)ˣ} (ht : t ∈ L.torusW X) : Commute n (Units.map L.extGrp t) := by
  obtain ⟨s, hs⟩ := h (L.diagU t) ⟨t, ht, rfl⟩
  exact ((L.diagU_mul_inrU_conj_diagU_eq_iff g t s n).1 hs).2

/-! ## Conjugacy of tori and `|W(H̄, T)|` -/


/-- **`|W(H̄, T)|` is invariant under `H̄(F)`-conjugation**: for `h ∈ H̄`,
`|W(H̄, hTh⁻¹)| = |W(H̄, T)|`. -/
theorem weylCardOf_map_conj {h : L.Ambˣ} (hh : h ∈ L.HbarU) (T : Subgroup L.Ambˣ) :
    L.weylCardOf (T.map (MulAut.conj h).toMonoidHom) = L.weylCardOf T := by
  let e : ↥L.HbarU ≃* ↥L.HbarU := MulAut.conj ⟨h, hh⟩
  have hS : (T.map (MulAut.conj h).toMonoidHom).subgroupOf L.HbarU =
      (T.subgroupOf L.HbarU).map e.toMonoidHom := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, e]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyH : y ∈ L.HbarU := by
        have : y = h⁻¹ * (x : L.Ambˣ) * h := by rw [← hyx]; group
        rw [this]
        exact L.HbarU.mul_mem (L.HbarU.mul_mem (L.HbarU.inv_mem hh) x.2) hh
      exact ⟨⟨y, hyH⟩, hy, Subtype.ext hyx⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  unfold weylCardOf
  rw [hS]
  exact Subgroup.relIndex_centralizer_normalizer_map_equiv _ e

end Basic

section Gamma

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (L : LuoDatum F)

/-- `H̄(F)`-conjugacy of the tori of `𝒯` is an equivalence relation. -/
theorem torusConj_equivalence : Equivalence L.TorusConj := by
  refine ⟨fun T => ⟨1, L.HbarU.one_mem, ?_⟩,
    fun {T T'} ⟨h, hh, hT⟩ => ⟨h⁻¹, L.HbarU.inv_mem hh, ?_⟩,
    fun {T T' T''} ⟨h, hh, hT⟩ ⟨h', hh', hT'⟩ => ⟨h' * h, L.HbarU.mul_mem hh' hh, ?_⟩⟩
  · ext t; simp
  · rw [hT, Subgroup.map_map]
    ext t; simp [MulAut.conj_apply, mul_assoc]
  · rw [hT', hT, Subgroup.map_map]
    congr 1

/-- `|W(H̄, T)|` is constant on `H̄(F)`-conjugacy classes of tori. -/
theorem weylCardOf_eq_of_torusConj {T T' : L.GammaTorus} (h : L.TorusConj T T') :
    L.weylCardOf T'.1 = L.weylCardOf T.1 := by
  obtain ⟨g, hg, hT⟩ := h
  rw [hT]
  exact L.weylCardOf_map_conj hg T.1

end Gamma

end LuoDatum

end GSpinGGP
