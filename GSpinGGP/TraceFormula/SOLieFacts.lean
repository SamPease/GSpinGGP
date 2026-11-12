/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.SubgroupTransport
import GSpinGGP.TraceFormula.SOLie
import GSpinGGP.Foundations.BilinFormAdjoint

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
* `LuoDatum.conj_mem_lieH_of_mem_HbarU`: `H̄` normalizes `𝔥 = so(W) ⊕ 𝔫` and fixes `λ`
  (Luo §2.1; generators `diagU_conj_mem_lieH`, `inrU_conj_mem_lieH`, with `bform_conj_lieN`).
* `LuoDatum.weylCardOf_map_diagU`: for `S ⊆ SO(W)`, `|W(H̄, (S, S ⊕ 1))| = |N_{SO(W)}(S) : Z_{SO(W)}(S)|`.
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

/-- The `GL(W)`-component of an element of `H̄` lies in `SO(W)` (`mem_HbarU_iff`). -/
theorem unitFst_mem_SOu_of_mem_HbarU {u : L.Ambˣ} (hu : u ∈ L.HbarU) :
    L.unitFst u ∈ SOu L.QW := by
  obtain ⟨g, hg, n, -, rfl⟩ := L.mem_HbarU_iff.mp hu
  rw [unitFst_diagU_mul_inrU]
  exact hg

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

/-- **`|W(H̄, T')|` for a diagonal torus** (Luo §7.1): for a subgroup `S` of `SO(W)`, with
`T' = {(s, s ⊕ 1) : s ∈ S}`, `|N_{H̄}(T')/Z_{H̄}(T')| = |N_{SO(W)}(S)/Z_{SO(W)}(S)|`.  The map
`(g, (g ⊕ 1) n) ↦ g` sends `N_{H̄}(T')` onto `N_{SO(W)}(S)` (with section `g ↦ (g, g ⊕ 1)`), and an
element of `N_{H̄}(T')` centralizes `T'` iff its image centralizes `S`, since its `N`-part already
commutes with every `s ⊕ 1` (`diagU_mul_inrU_conj_diagU_eq_iff`). -/
theorem weylCardOf_map_diagU (S : Subgroup ↥(SOu L.QW)) :
    L.weylCardOf (S.map (L.diagU.comp (SOu L.QW).subtype)) =
      (Subgroup.centralizer (S : Set ↥(SOu L.QW))).relIndex
        (Subgroup.normalizer (S : Set ↥(SOu L.QW))) := by
  set ι := L.diagU.comp (SOu L.QW).subtype with hι
  set T := S.map ι with hT
  have hιapp : ∀ s : ↥(SOu L.QW), ι s = L.diagU s := fun _ => rfl
  have hdiagH : ∀ g ∈ SOu L.QW, L.diagU g ∈ L.HbarU := fun g hg =>
    L.mem_HbarU_iff.mpr ⟨g, hg, 1, L.NsetSub.one_mem, by simp⟩
  have hφmem : ∀ u : ↥L.HbarU, L.unitFst u ∈ SOu L.QW := fun u =>
    L.unitFst_mem_SOu_of_mem_HbarU u.2
  let φ : ↥L.HbarU →* ↥(SOu L.QW) :=
    (L.unitFst.comp L.HbarU.subtype).codRestrict _ hφmem
  have hφ : ∀ u : ↥L.HbarU, ((φ u : ↥(SOu L.QW)) : (Module.End K L.W)ˣ) = L.unitFst u :=
    fun _ => rfl
  have hφι : ∀ g : ↥(SOu L.QW), φ ⟨ι g, hdiagH g g.2⟩ = g := fun g =>
    Subtype.ext (by rw [hφ]; exact L.unitFst_diagU _)
  have hmemT : ∀ a : L.Ambˣ, a ∈ T ↔ ∃ s ∈ S, ι s = a := fun a => Subgroup.mem_map
  -- an element of `N_{H̄}(T')`: its `SO(W)`-part normalizes `S`, its `N`-part centralizes `T'`
  have key : ∀ u : ↥L.HbarU,
      u ∈ Subgroup.normalizer ((T.subgroupOf L.HbarU : Subgroup ↥L.HbarU) : Set ↥L.HbarU) →
      ∀ s ∈ S, φ u * s * (φ u)⁻¹ ∈ S ∧
        ∀ g n, (u : L.Ambˣ) = L.diagU g * L.inrU n →
          n * Units.map L.extGrp (s : (Module.End K L.W)ˣ) =
            Units.map L.extGrp (s : (Module.End K L.W)ˣ) * n := by
    intro u hu s hs
    have h1 : (⟨ι s, hdiagH s s.2⟩ : ↥L.HbarU) ∈ T.subgroupOf L.HbarU :=
      Subgroup.mem_subgroupOf.mpr ((hmemT _).mpr ⟨s, hs, rfl⟩)
    have h2 := (Subgroup.mem_normalizer_iff.mp hu _).mp h1
    obtain ⟨s', hs', he⟩ := (hmemT _).mp (Subgroup.mem_subgroupOf.mp h2)
    obtain ⟨g, -, n, -, hu'⟩ := L.mem_HbarU_iff.mp u.2
    have he' : (L.diagU g * L.inrU n) * L.diagU (s : (Module.End K L.W)ˣ) *
        (L.diagU g * L.inrU n)⁻¹ = L.diagU (s' : (Module.End K L.W)ˣ) := by
      rw [← hu', ← hιapp, ← hιapp, he]; rfl
    have hgs := (L.diagU_mul_inrU_conj_diagU_eq_iff g _ _ n).mp he'
    have hg : (φ u : (Module.End K L.W)ˣ) = g := by
      rw [hφ, hu', unitFst_diagU_mul_inrU]
    refine ⟨?_, fun g' n' hu'' => ?_⟩
    · have : φ u * s * (φ u)⁻¹ = s' := Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hg]
        exact hgs.1)
      rw [this]; exact hs'
    · obtain ⟨rfl, rfl⟩ := (L.diagU_mul_inrU_inj).mp (hu'.symm.trans hu'')
      exact hgs.2
  unfold weylCardOf
  refine Subgroup.relIndex_eq_of_map_eq_of_comap_inf_eq (f := φ) ?_ ?_
  · -- `φ(N_{H̄}(T')) = N_{SO(W)}(S)`
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      refine Subgroup.mem_normalizer_iff.mpr fun s => ⟨fun hs => (key u hu s hs).1, fun hs => ?_⟩
      have := (key u⁻¹ (Subgroup.inv_mem _ hu) _ hs).1
      simpa [map_inv, mul_assoc] using this
    · intro g hg
      refine ⟨⟨ι g, hdiagH g g.2⟩, ?_, hφι g⟩
      refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      constructor
      · intro hh
        obtain ⟨s, hs, hse⟩ := (hmemT _).mp hh
        refine (hmemT _).mpr ⟨g * s * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg s).mp hs, ?_⟩
        rw [map_mul, map_mul, map_inv, hse]
      · intro hh
        obtain ⟨s, hs, hse⟩ := (hmemT _).mp hh
        refine (hmemT _).mpr ⟨g⁻¹ * s * g, (Subgroup.mem_normalizer_iff''.mp hg s).mp hs, ?_⟩
        rw [map_mul, map_mul, map_inv, hse]
        group
  · -- `N_{H̄}(T') ∩ φ⁻¹(Z_{SO(W)}(S)) = Z_{H̄}(T')`
    apply le_antisymm
    · rintro u ⟨hz, hn⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨s, hs, hse⟩ := (hmemT _).mp (Subgroup.mem_subgroupOf.mp hh)
      obtain ⟨g, -, n, -, hu'⟩ := L.mem_HbarU_iff.mp u.2
      have hg : (φ u : (Module.End K L.W)ˣ) = g := by
        rw [hφ, hu', unitFst_diagU_mul_inrU]
      have hgs : Commute g (s : (Module.End K L.W)ˣ) := by
        have := Subgroup.mem_centralizer_iff.mp hz s hs
        rw [← hg]
        exact (congrArg Subtype.val this).symm
      have hc := (L.commute_diagU_mul_inrU_diagU_iff g s n).mpr
        ⟨hgs, (key u hn s hs).2 g n hu'⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hse, hιapp, hu']
      exact hc.eq.symm
    · intro u hu
      refine ⟨?_, Subgroup.centralizer_le_normalizer _ hu⟩
      change φ u ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have h1 : (⟨ι s, hdiagH s s.2⟩ : ↥L.HbarU) ∈ T.subgroupOf L.HbarU :=
        Subgroup.mem_subgroupOf.mpr ((hmemT _).mpr ⟨s, hs, rfl⟩)
      have h2 := congrArg φ (Subgroup.mem_centralizer_iff.mp hu _ h1)
      rwa [map_mul, map_mul, hφι] at h2

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

/-! ## `H̄` normalizes `𝔥` and fixes `λ` (Luo §2.1) -/

section HConj

variable {K : Type*} [Field K] [Invertible (2 : K)]

theorem isOrthogonal_of_mem_SOu {U : Type*} [AddCommGroup U] [Module K U]
    {Q : QuadraticForm K U} {u : (Module.End K U)ˣ} (hu : u ∈ SOu Q) :
    (bform Q).IsOrthogonal (u : Module.End K U) := fun x y => by
  have h : ∀ v, Q ((u : Module.End K U) v) = Q v := fun v => hu.1 v
  simp only [bform, QuadraticMap.associated_apply]
  rw [← map_add, h, h, h]

/-- Conjugation by an element of `SO(Q)` preserves `so(Q)`. -/
theorem conj_mem_skewAdjoint {U : Type*} [AddCommGroup U] [Module K U]
    {Q : QuadraticForm K U} {u : (Module.End K U)ˣ} (hu : u ∈ SOu Q) {M : Module.End K U}
    (hM : M ∈ skewAdjointLieSubalgebra (bform Q)) :
    ((u⁻¹ : (Module.End K U)ˣ) : Module.End K U) * M * (u : Module.End K U) ∈
      skewAdjointLieSubalgebra (bform Q) :=
  (LinearMap.mem_skewAdjointSubmodule _).2
    ((LinearMap.mem_skewAdjointSubmodule _).1 hM |>.conj_units (isOrthogonal_of_mem_SOu hu))

variable (L : LuoDatum K)

/-- `Z_r^⊥` is preserved by an isometry preserving `Z_r`. -/
theorem apply_mem_orthogonal_of_mem_SOu {u : (Module.End K L.V)ˣ} (hu : u ∈ SOu L.QV)
    (hinv : ∀ z ∈ L.flagSub L.r, ((u⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V) z ∈
      L.flagSub L.r) {v : L.V} (hv : v ∈ (bform L.QV).orthogonal (L.flagSub L.r)) :
    (u : Module.End K L.V) v ∈ (bform L.QV).orthogonal (L.flagSub L.r) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
  intro z hz
  have := hv _ (hinv z hz)
  rwa [(isOrthogonal_of_mem_SOu hu).isAdjointPair_inv] at this

/-- **Conjugation by an isometry preserving the flag preserves `𝔫`.** -/
theorem conj_mem_lieN {u : (Module.End K L.V)ˣ} (hu : u ∈ SOu L.QV)
    (h1 : ∀ k ≤ L.r, ∀ v ∈ L.flagSub k, (u : Module.End K L.V) v ∈ L.flagSub k)
    (h2 : ∀ k ≤ L.r, ∀ v ∈ L.flagSub k,
      ((u⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V) v ∈ L.flagSub k)
    {M : Module.End K L.V} (hM : M ∈ L.lieN) :
    ((u⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V) * M * (u : Module.End K L.V) ∈ L.lieN := by
  refine ⟨conj_mem_skewAdjoint hu hM.1, fun k hk v hv => ?_, fun v hv => ?_⟩
  · simp only [Module.End.mul_apply]
    exact h2 k hk.le _ (hM.2.1 k hk _ (h1 (k + 1) hk _ hv))
  · simp only [Module.End.mul_apply]
    exact h2 _ le_rfl _ (hM.2.2 _ (L.apply_mem_orthogonal_of_mem_SOu hu (h2 _ le_rfl) hv))

theorem extLie_apply (A : Module.End K L.W) (v : L.V) : L.extLie A v = (A v.1, 0) := rfl

theorem fst_zV (i : ℤ) : (L.zV i).1 = 0 := rfl

theorem bform_zV_zV {i j : ℤ} (hi : |i| ≤ L.r) (hj : |j| ≤ L.r) (hij : i + j ≠ 0) :
    bform L.QV (L.zV i) (L.zV j) = 0 := by
  rw [bform_prod]
  change bform L.QW 0 0 + bform L.QZ (L.z i) (L.z j) = 0
  rw [L.gram i j hi hj]
  simp [hij]

/-- `z_i ∈ Z_{r-i+1}` for `i ≤ r`. -/
theorem zV_mem_flagSub {i : ℕ} (hir : i ≤ L.r) :
    L.zV (i : ℤ) ∈ L.flagSub (L.r - i + 1) :=
  Submodule.subset_span ⟨⟨L.r - i, by omega⟩, by
    simp only
    congr 1
    omega⟩

/-- `z_0 ∈ Z_r^⊥`. -/
theorem zV_zero_mem_orthogonal : L.zV 0 ∈ (bform L.QV).orthogonal (L.flagSub L.r) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro v hv
  have hle : L.flagSub L.r ≤ LinearMap.ker ((bform L.QV).flip (L.zV 0)) := by
    rw [flagSub, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    change bform L.QV (L.zV ((L.r : ℤ) - (j : ℕ))) (L.zV 0) = 0
    exact L.bform_zV_zV (by rw [abs_le]; constructor <;> omega) (by simp) (by omega)
  exact hle hv

/-- `q(z_{-i-1}, Z_{r-i-1}) = 0` (`Z_{r-i-1} = ⟨z_r, …, z_{i+2}⟩`). -/
theorem bform_zV_neg_of_mem_flagSub {i : ℕ} (hi : i < L.r) {v : L.V}
    (hv : v ∈ L.flagSub (L.r - i - 1)) : bform L.QV (L.zV (-(i : ℤ) - 1)) v = 0 := by
  have hle : L.flagSub (L.r - i - 1) ≤ LinearMap.ker (bform L.QV (L.zV (-(i : ℤ) - 1))) := by
    rw [flagSub, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj := j.2
    exact L.bform_zV_zV (by rw [abs_le]; constructor <;> omega)
      (by rw [abs_le]; constructor <;> omega) (by omega)
  exact hle hv

/-- For `n ∈ N` and `i < r`, `n z_i − z_i ∈ Z_{r-i}`. -/
theorem apply_zV_sub_mem_flagSub {n : Module.End K L.V}
    (h1 : ∀ k < L.r, ∀ v ∈ L.flagSub (k + 1), n v ∈ L.flagSub k)
    (h2 : ∀ v ∈ (bform L.QV).orthogonal (L.flagSub L.r), n v ∈ L.flagSub L.r)
    {i : ℕ} (hi : i < L.r) : n (L.zV (i : ℤ)) ∈ L.flagSub (L.r - i) := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simpa using h2 _ L.zV_zero_mem_orthogonal
  · have := L.zV_mem_flagSub hi.le
    rw [show L.r - i + 1 = (L.r - i) + 1 from rfl] at this
    exact h1 (L.r - i) (by omega) _ this

theorem extLie_apply_of_fst_eq_zero (A : Module.End K L.W) {v : L.V} (hv : v.1 = 0) :
    L.extLie A v = 0 := by
  rw [extLie_apply, hv, map_zero]; rfl

/-- `ad X ⊕ 0` is skew when `X` is. -/
theorem extLie_mem_skewAdjoint {A : Module.End K L.W}
    (hA : A ∈ skewAdjointLieSubalgebra (bform L.QW)) :
    L.extLie A ∈ skewAdjointLieSubalgebra (bform L.QV) := by
  have hA' := (LinearMap.mem_skewAdjointSubmodule (B := bform L.QW) A).1 hA
  change _ ∈ (bform L.QV).skewAdjointSubmodule
  rw [LinearMap.mem_skewAdjointSubmodule]
  intro x y
  rw [Pi.neg_apply, map_neg, bform_prod, bform_prod, extLie_apply, extLie_apply, hA' x.1 y.1,
    Pi.neg_apply, map_neg, map_zero, LinearMap.zero_apply, map_zero]
  simp

/-- `λ` only sees `X_V`. -/
theorem lam_eq_of_sndA_eq {X Y : L.Amb} (h : L.sndA X = L.sndA Y) : L.lam X = L.lam Y := by
  unfold lam; rw [h]

/-- **`λ` is `N`-invariant on `𝔫`**: `q(z_{-i-1}, n⁻¹ M n z_i) = q(z_{-i-1}, M z_i)`. -/
theorem bform_conj_lieN {n : (Module.End K L.V)ˣ} (hn : n ∈ L.Nset) {M : Module.End K L.V}
    (hM : M ∈ L.lieN) {i : ℕ} (hi : i < L.r) :
    bform L.QV (L.zV (-(i : ℤ) - 1))
        ((((n⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V) * M * (n : Module.End K L.V))
          (L.zV i)) =
      bform L.QV (L.zV (-(i : ℤ) - 1)) (M (L.zV i)) := by
  have hn' : n⁻¹ ∈ L.Nset := L.NsetSub.inv_mem hn
  set z := L.zV (i : ℤ)
  set ni := ((n⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V)
  have hk : L.r - i = (L.r - i - 1) + 1 := by omega
  have hd : (n : Module.End K L.V) z - z ∈ L.flagSub (L.r - i) :=
    L.apply_zV_sub_mem_flagSub (n := (n : Module.End K L.V) - 1)
      (fun k hk v hv => hn.2.1 k hk v hv) (fun v hv => hn.2.2 v hv) hi
  have hMz : M z ∈ L.flagSub (L.r - i) :=
    L.apply_zV_sub_mem_flagSub (n := M) hM.2.1 hM.2.2 hi
  rw [hk] at hd hMz
  have e : (ni * M * (n : Module.End K L.V)) z =
      ni (M ((n : Module.End K L.V) z - z)) + (ni (M z) - M z) + M z := by
    simp only [Module.End.mul_apply, map_sub]; abel
  rw [e, map_add, map_add, L.bform_zV_neg_of_mem_flagSub hi
      (L.inv_apply_mem_flagSub_of_mem_Nset hn (by omega) (hM.2.1 _ (by omega) _ hd)),
    L.bform_zV_neg_of_mem_flagSub hi (hn'.2.1 _ (by omega) _ hMz), zero_add, zero_add]

theorem extGrp_zV (f : Module.End K L.W) (i : ℤ) : L.extGrp f (L.zV i) = L.zV i := by
  rw [extGrp_apply, fst_zV, map_zero]; rfl

theorem extLie_conj (a b c : Module.End K L.W) :
    L.extLie (a * b * c) = L.extGrp a * L.extLie b * L.extGrp c := by
  ext v <;> simp [extLie_apply, extGrp_apply]

/-- `n⁻¹ (A ⊕ 0) n − (A ⊕ 0) ∈ 𝔫` for `n ∈ N` and `A ∈ so(W)`. -/
theorem conj_extLie_sub_mem_lieN {n : (Module.End K L.V)ˣ} (hn : n ∈ L.Nset)
    {A : Module.End K L.W} (hA : A ∈ skewAdjointLieSubalgebra (bform L.QW)) :
    ((n⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V) * L.extLie A * (n : Module.End K L.V) -
      L.extLie A ∈ L.lieN := by
  have hn' : n⁻¹ ∈ L.Nset := L.NsetSub.inv_mem hn
  refine ⟨sub_mem (conj_mem_skewAdjoint hn.1 (L.extLie_mem_skewAdjoint hA))
    (L.extLie_mem_skewAdjoint hA), fun k hk v hv => ?_, fun v hv => ?_⟩
  · have h1 : L.extLie A ((n : Module.End K L.V) v) = 0 :=
      L.extLie_apply_of_fst_eq_zero A (L.fst_eq_zero_of_mem_flagSub
        (L.apply_mem_flagSub_of_mem_Nset hn hk hv))
    have h2 : L.extLie A v = 0 := L.extLie_apply_of_fst_eq_zero A (L.fst_eq_zero_of_mem_flagSub hv)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, h1, h2, map_zero, sub_zero]
    exact zero_mem _
  · have hd : (n : Module.End K L.V) v - v ∈ L.flagSub L.r := hn.2.2 v hv
    have h1 : L.extLie A ((n : Module.End K L.V) v) = L.extLie A v := by
      rw [show (n : Module.End K L.V) v = v + ((n : Module.End K L.V) v - v) by abel, map_add,
        L.extLie_apply_of_fst_eq_zero A (L.fst_eq_zero_of_mem_flagSub hd), add_zero]
    have hw : L.extLie A v ∈ (bform L.QV).orthogonal (L.flagSub L.r) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro z hz
      rw [bform_prod, extLie_apply, L.fst_eq_zero_of_mem_flagSub hz]
      simp
    simp only [LinearMap.sub_apply, Module.End.mul_apply, h1]
    exact hn'.2.2 _ hw

/-- **`(g, g ⊕ 1)` normalizes `𝔥` and fixes `λ`** (`g ∈ SO(W)`). -/
theorem diagU_conj_mem_lieH {g : (Module.End K L.W)ˣ} (hg : g ∈ SOu L.QW) {Y : L.Amb}
    (hY : Y ∈ L.lieH) :
    (((L.diagU g)⁻¹ : L.Ambˣ) : L.Amb) * Y * ((L.diagU g : L.Ambˣ) : L.Amb) ∈ L.lieH ∧
      L.lam ((((L.diagU g)⁻¹ : L.Ambˣ) : L.Amb) * Y * ((L.diagU g : L.Ambˣ) : L.Amb)) =
        L.lam Y := by
  set E : (Module.End K L.V)ˣ := Units.map L.extGrp g
  have hE : E ∈ SOu L.QV := L.extU_mem_SOu hg
  have hEi : ((E⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V) = L.extGrp ↑g⁻¹ := by
    rw [← map_inv]; rfl
  have hfst : L.fstA ((((L.diagU g)⁻¹ : L.Ambˣ) : L.Amb) * Y * ((L.diagU g : L.Ambˣ) : L.Amb)) =
      ((g⁻¹ : (Module.End K L.W)ˣ) : Module.End K L.W) * L.fstA Y * (g : Module.End K L.W) := by
    rw [← map_inv, map_mul, map_mul]; rfl
  have hsnd : L.sndA ((((L.diagU g)⁻¹ : L.Ambˣ) : L.Amb) * Y * ((L.diagU g : L.Ambˣ) : L.Amb)) =
      ((E⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V) * L.sndA Y * (E : Module.End K L.V) := by
    rw [← map_inv, map_mul, map_mul, hEi]; rfl
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [hfst]; exact conj_mem_skewAdjoint hg hY.1.1
  · rw [hsnd]; exact conj_mem_skewAdjoint hE hY.1.2
  · rw [hfst, hsnd, L.extLie_conj, ← hEi]
    have e : ((E⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V) * L.sndA Y *
          (E : Module.End K L.V) -
        ((E⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V) * L.extLie (L.fstA Y) *
          L.extGrp (g : Module.End K L.W) =
        ((E⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V) *
          (L.sndA Y - L.extLie (L.fstA Y)) * (E : Module.End K L.V) := by
      rw [mul_sub, sub_mul]; rfl
    rw [e]
    refine L.conj_mem_lieN hE (fun k _ v hv => ?_) (fun k _ v hv => ?_) hY.2
    · change L.extGrp _ v ∈ _
      rwa [L.extGrp_apply_of_mem_flagSub _ hv]
    · rw [hEi, L.extGrp_apply_of_mem_flagSub _ hv]; exact hv
  · unfold lam
    rw [hsnd]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, show (E : Module.End K L.V) (L.zV (i : ℕ)) =
      L.zV (i : ℕ) from L.extGrp_zV _ _, ← (isOrthogonal_of_mem_SOu hE).isAdjointPair]
    change bform L.QV (L.extGrp _ _) _ = _
    rw [L.extGrp_zV]

/-- **`(1, n)` normalizes `𝔥` and fixes `λ`** (`n ∈ N`). -/
theorem inrU_conj_mem_lieH {n : (Module.End K L.V)ˣ} (hn : n ∈ L.Nset) {Y : L.Amb}
    (hY : Y ∈ L.lieH) :
    (((L.inrU n)⁻¹ : L.Ambˣ) : L.Amb) * Y * ((L.inrU n : L.Ambˣ) : L.Amb) ∈ L.lieH ∧
      L.lam ((((L.inrU n)⁻¹ : L.Ambˣ) : L.Amb) * Y * ((L.inrU n : L.Ambˣ) : L.Amb)) =
        L.lam Y := by
  set ni := ((n⁻¹ : (Module.End K L.V)ˣ) : Module.End K L.V)
  have hfst : L.fstA ((((L.inrU n)⁻¹ : L.Ambˣ) : L.Amb) * Y * ((L.inrU n : L.Ambˣ) : L.Amb)) =
      L.fstA Y := by
    rw [← map_inv, map_mul, map_mul]
    change 1 * L.fstA Y * 1 = _
    rw [one_mul, mul_one]
  have hsnd : L.sndA ((((L.inrU n)⁻¹ : L.Ambˣ) : L.Amb) * Y * ((L.inrU n : L.Ambˣ) : L.Amb)) =
      ni * L.sndA Y * (n : Module.End K L.V) := by
    rw [← map_inv, map_mul, map_mul]; rfl
  set M := L.sndA Y - L.extLie (L.fstA Y)
  have hM : M ∈ L.lieN := hY.2
  have hYV : L.sndA Y = M + L.extLie (L.fstA Y) := by simp [M]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [hfst]; exact hY.1.1
  · rw [hsnd]; exact conj_mem_skewAdjoint hn.1 hY.1.2
  · rw [hfst, hsnd]
    have e : ni * L.sndA Y * (n : Module.End K L.V) - L.extLie (L.fstA Y) =
        ni * M * (n : Module.End K L.V) +
          (ni * L.extLie (L.fstA Y) * (n : Module.End K L.V) - L.extLie (L.fstA Y)) := by
      rw [hYV, mul_add, add_mul]; abel
    rw [e]
    exact add_mem (L.conj_mem_lieN hn.1 (fun k hk v hv => L.apply_mem_flagSub_of_mem_Nset hn hk hv)
      (fun k hk v hv => L.inv_apply_mem_flagSub_of_mem_Nset hn hk hv) hM)
      (L.conj_extLie_sub_mem_lieN hn hY.1.1)
  · unfold lam
    rw [hsnd]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (i : ℕ) < L.r := i.2
    have hd : (n : Module.End K L.V) (L.zV (i : ℕ)) - L.zV (i : ℕ) ∈ L.flagSub (L.r - i) :=
      L.apply_zV_sub_mem_flagSub (n := (n : Module.End K L.V) - 1)
        (fun k hk v hv => hn.2.1 k hk v hv) (fun v hv => hn.2.2 v hv) hi
    have hnz : (((n : Module.End K L.V) (L.zV (i : ℕ))).1) = 0 := by
      have := L.fst_eq_zero_of_mem_flagSub hd
      rw [Prod.fst_sub, fst_zV, sub_zero] at this
      exact this
    have e1 : (ni * L.sndA Y * (n : Module.End K L.V)) (L.zV (i : ℕ)) =
        (ni * M * (n : Module.End K L.V)) (L.zV (i : ℕ)) := by
      rw [hYV, mul_add, add_mul, LinearMap.add_apply]
      simp only [Module.End.mul_apply, L.extLie_apply_of_fst_eq_zero _ hnz, map_zero, add_zero]
    have e2 : L.sndA Y (L.zV (i : ℕ)) = M (L.zV (i : ℕ)) := by
      rw [hYV, LinearMap.add_apply, L.extLie_apply_of_fst_eq_zero _ (L.fst_zV _), add_zero]
    rw [e1, L.bform_conj_lieN hn hM hi, e2]

/-- **`H̄` normalizes `𝔥` and fixes `λ`**: write `u = (g, g ⊕ 1)(1, n)` (`mem_HbarU_iff`). -/
theorem conj_mem_lieH_of_mem_HbarU {u : L.Ambˣ} (hu : u ∈ L.HbarU) {Y : L.Amb}
    (hY : Y ∈ L.lieH) :
    ((u⁻¹ : L.Ambˣ) : L.Amb) * Y * (u : L.Amb) ∈ L.lieH ∧
      L.lam (((u⁻¹ : L.Ambˣ) : L.Amb) * Y * (u : L.Amb)) = L.lam Y := by
  obtain ⟨g, hg, n, hn, rfl⟩ := L.mem_HbarU_iff.1 hu
  have e : (((L.diagU g * L.inrU n)⁻¹ : L.Ambˣ) : L.Amb) * Y *
      ((L.diagU g * L.inrU n : L.Ambˣ) : L.Amb) =
      (((L.inrU n)⁻¹ : L.Ambˣ) : L.Amb) *
        ((((L.diagU g)⁻¹ : L.Ambˣ) : L.Amb) * Y * ((L.diagU g : L.Ambˣ) : L.Amb)) *
        ((L.inrU n : L.Ambˣ) : L.Amb) := by
    simp only [mul_inv_rev, Units.val_mul, mul_assoc]
  obtain ⟨h1, h2⟩ := L.diagU_conj_mem_lieH hg hY
  obtain ⟨h3, h4⟩ := L.inrU_conj_mem_lieH hn h1
  rw [e]
  exact ⟨h3, h4.trans h2⟩

end HConj

end LuoDatum

end GSpinGGP
