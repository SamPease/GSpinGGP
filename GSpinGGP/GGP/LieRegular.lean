/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.JointRankDescent
import GSpinGGP.GGP.RegularNilpotent
import GSpinGGP.GGP.Descent
import GSpinGGP.Foundations.JordanAlgebra
import GSpinGGP.Foundations.RankSemicontinuity

/-!
# Regular semisimple elements of `𝔤_g`

Let `g ∈ GSpin(V)` be semisimple and `Y ∈ gspin(V)_g` with `L_Y` semisimple on `C(V)`. Then
`adV Y` is a semisimple skew map commuting with `P(g)` (`isSemisimple_adV`), and
`jointClauses_of_charZero` for the pair `(P(g), adV Y)` gives, for the centralizer
`gspin(V)_{g,Y}` (of dimension `1 + dim (so(V)_{P(g)} ⊓ so(V)_{adV Y})`):

* `le_finrank_lieCentralizer_gspin_of_isSemisimple`: `⌊dim V/2⌋ + 1 ≤ dim gspin(V)_{g,Y}`;
* `finrank_lieCentralizer_gspin_eq_iff_isLieAbelian`: equality iff `gspin(V)_{g,Y}` is abelian;
* `eq_zero_of_isNilpotent_of_finrank_eq`: in case of equality, its only nilpotent element is `0`.

For `𝔤 = gspin(W) × gspin(V)` and semisimple `g ∈ G(F)` the same holds for `𝔤_{g,Z}` with
`ℓ = (⌊dim W/2⌋ + 1) + (⌊dim V/2⌋ + 1)` (`lieClauses`). With the Jordan decomposition in `𝔤_g` and
upper semicontinuity of `dim ker (ad Z)^D`, this shows that the regular semisimple set of `𝔤_g` is
open (`isOpen_setOf_isRegularSS_lieCentralizer`).
-/

noncomputable section

open Module CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

/-! ## Kernels of powers -/

section Kernel

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- If `n` is nilpotent and commutes with `s`, then `s + n` is nilpotent on `ker s`:
`ker s ≤ ker (s + n)^(dim M)`. -/
theorem ker_le_ker_pow_add [FiniteDimensional K M] {s n : Module.End K M} (hc : Commute s n)
    (hn : IsNilpotent n) : LinearMap.ker s ≤ LinearMap.ker ((s + n) ^ finrank K M) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have key : ∀ k : ℕ, ((s + n) ^ k) x = (n ^ k) x := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, LinearMap.add_apply, ← Module.End.mul_apply,
        (hc.pow_right k).eq, Module.End.mul_apply, hx, map_zero, zero_add, ← Module.End.mul_apply,
        ← pow_succ']
  have hD : n ^ finrank K M = 0 := by
    have h := LinearMap.aeval_self_charpoly n
    rwa [hn.charpoly_eq_X_pow_finrank, Polynomial.aeval_X_pow] at h
  rw [key, hD, LinearMap.zero_apply]

/-- For `f` semisimple, `ker f^k = ker f` (`k > 0`). -/
theorem ker_pow_eq_ker_of_isSemisimple {f : Module.End K M} (hf : f.IsSemisimple) {k : ℕ}
    (hk : 0 < k) : LinearMap.ker (f ^ k) = LinearMap.ker f := by
  have h := hf.isFinitelySemisimple.genEigenspace_eq_eigenspace 0 (k := k) (by exact_mod_cast hk)
  rw [Module.End.genEigenspace_nat, Module.End.eigenspace_def, zero_smul, sub_zero] at h
  simpa using h

end Kernel

/-! ## `adV` of semisimple and nilpotent elements -/

section AdV

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- `ι((adV Y)^k v) = (ad Y)^k (ι v)` for `Y ∈ gspin(V)`. -/
theorem ι_adV_pow {Q : QuadraticForm K V} {Y : CliffordAlgebra Q} (hY : Y ∈ gspin Q) (k : ℕ)
    (v : V) : ι Q ((adV Q Y ^ k) v) = (LieAlgebra.ad K _ Y ^ k) (ι Q v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ι_adV hY, ih, pow_succ', Module.End.mul_apply,
      LieAlgebra.ad_apply, Ring.lie_def]

/-- `adV Y` is nilpotent for nilpotent `Y ∈ gspin(V)`. -/
theorem isNilpotent_adV {Q : QuadraticForm K V} {Y : CliffordAlgebra Q} (hY : Y ∈ gspin Q)
    (hn : IsNilpotent Y) : IsNilpotent (adV Q Y) := by
  obtain ⟨k, hk⟩ := LieAlgebra.ad_nilpotent_of_nilpotent (R := K) hn
  refine ⟨k, LinearMap.ext fun v => ι_injective Q ?_⟩
  rw [ι_adV_pow hY, hk, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

/-- `adV Y` is semisimple for `Y ∈ gspin(V)` with `L_Y` semisimple on `C(V)` (`adV Y` is the
restriction of `ad Y` to `ι V`). -/
theorem isSemisimple_adV [PerfectField K] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {Y : CliffordAlgebra Q} (hY : Y ∈ gspin Q)
    (hs : Module.End.IsSemisimple (LinearMap.mulLeft K Y)) : (adV Q Y).IsSemisimple := by
  have hR : Set.MapsTo (LieAlgebra.ad K _ Y) (LinearMap.range (ι Q)) (LinearMap.range (ι Q)) := by
    rintro _ ⟨v, rfl⟩
    exact hY.2 v
  have hss := (LieAlgebra.ad_isSemisimple_of_isSemisimple_mulLeft hs).restrict
    ((Module.End.mem_invtSubmodule _).2 hR)
  let e : V ≃ₗ[K] LinearMap.range (ι Q) := LinearEquiv.ofInjective (ι Q) (ι_injective Q)
  refine (LinearEquiv.isSemisimple_iff _ _ e (LinearMap.ext fun v => Subtype.ext ?_)).2 hss
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e,
    LinearEquiv.ofInjective_apply]
  exact ι_adV hY v

end AdV

/-! ## The centralizer `gspin(V)_{g,Y}` -/

section Lift

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {Q : QuadraticForm K V} (hQ : IsNondeg Q) (g : GSpin Q) {Y : CliffordAlgebra Q}

include hQ in
/-- `adV` maps `gspin(V)_{g,Y}` into `so(V)_{P(g)} ⊓ so(V)_{adV Y}`. -/
theorem adV_mem_soCent_inf (hYg : Y ∈ gspin Q) {Z : CliffordAlgebra Q}
    (hZ : Z ∈ lieCentralizer (lieCentralizer (gspin Q)
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) Y) :
    adV Q Z ∈ soCent Q (specP Q g : Module.End K V) ⊓ soCent Q (adV Q Y) := by
  obtain ⟨hZ', hYZ⟩ := mem_lieCentralizer.mp hZ
  obtain ⟨hZg, hxZ⟩ := mem_lieCentralizer.mp hZ'
  have hc := adV_commutator hZg hYg
  rw [← hYZ, sub_self, map_zero, eq_comm, sub_eq_zero] at hc
  exact Submodule.mem_inf.mpr
    ⟨mem_soCent.2 ⟨bform_adV hZg, ((commute_iff_adV hQ g hZg).mp hxZ).symm⟩,
    mem_soCent.2 ⟨bform_adV hZg, hc⟩⟩

include hQ in
/-- Every element of `so(V)_{P(g)} ⊓ so(V)_{adV Y}` is `adV Z` for some `Z ∈ gspin(V)_{g,Y}`. -/
theorem exists_mem_lieCentralizer_lieCentralizer_adV_eq (hYg : Y ∈ gspin Q) {M : Module.End K V}
    (hM : M ∈ soCent Q (specP Q g : Module.End K V) ⊓ soCent Q (adV Q Y)) :
    ∃ Z ∈ lieCentralizer (lieCentralizer (gspin Q)
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) Y, adV Q Z = M := by
  obtain ⟨hMg, hMN⟩ := Submodule.mem_inf.mp hM
  obtain ⟨hMs, hMgc⟩ := mem_soCent.mp hMg
  obtain ⟨-, hMNc⟩ := mem_soCent.mp hMN
  obtain ⟨Z, hZg, rfl⟩ := exists_mem_gspin_adV_eq hQ M hMs
  have hZY : Z * Y = Y * Z := commute_of_adV_commute hQ hZg hYg hMNc
  have hxZ := (commute_iff_adV hQ g hZg).mpr hMgc.symm
  exact ⟨Z, mem_lieCentralizer.mpr ⟨mem_lieCentralizer.mpr ⟨hZg, hxZ⟩, hZY.symm⟩, rfl⟩

include hQ in
/-- `gspin(V)_{g,Y}` is abelian iff `so(V)_{P(g)} ⊓ so(V)_{adV Y}` is. -/
theorem isLieAbelian_lieCentralizer_gspin_iff (hYg : Y ∈ gspin Q) :
    IsLieAbelian (lieCentralizer (lieCentralizer (gspin Q)
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) Y) ↔
    ∀ M₁ ∈ soCent Q (specP Q g : Module.End K V) ⊓ soCent Q (adV Q Y),
      ∀ M₂ ∈ soCent Q (specP Q g : Module.End K V) ⊓ soCent Q (adV Q Y), Commute M₁ M₂ := by
  constructor
  · intro hab M₁ h₁ M₂ h₂
    obtain ⟨Z₁, hZ₁, rfl⟩ := exists_mem_lieCentralizer_lieCentralizer_adV_eq hQ g hYg h₁
    obtain ⟨Z₂, hZ₂, rfl⟩ := exists_mem_lieCentralizer_lieCentralizer_adV_eq hQ g hYg h₂
    have h0 := congrArg Subtype.val (hab.trivial ⟨Z₁, hZ₁⟩ ⟨Z₂, hZ₂⟩)
    rw [LieSubalgebra.coe_bracket, Ring.lie_def, ZeroMemClass.coe_zero] at h0
    have := adV_commutator (mem_lieCentralizer.mp (mem_lieCentralizer.mp hZ₁).1).1
      (mem_lieCentralizer.mp (mem_lieCentralizer.mp hZ₂).1).1
    rw [h0, map_zero, eq_comm, sub_eq_zero] at this
    exact this
  · intro hab
    refine ⟨fun Z₁ Z₂ => Subtype.ext ?_⟩
    rw [LieSubalgebra.coe_bracket, Ring.lie_def, ZeroMemClass.coe_zero, sub_eq_zero]
    exact commute_of_adV_commute hQ (mem_lieCentralizer.mp (mem_lieCentralizer.mp Z₁.2).1).1
      (mem_lieCentralizer.mp (mem_lieCentralizer.mp Z₂.2).1).1
      (hab _ (adV_mem_soCent_inf hQ g hYg Z₁.2) _ (adV_mem_soCent_inf hQ g hYg Z₂.2)).eq

end Lift

/-! ## The centralizer `gspin(V)_{g,Y}` -/

section Factor

variable {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

variable {Q : QuadraticForm K V} (hQ : IsNondeg Q) (g : GSpin Q)
  (hg : Module.End.IsSemisimple
    (LinearMap.mulLeft K ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))
  {Y : CliffordAlgebra Q}
  (hY : Y ∈ lieCentralizer (gspin Q) ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
  (hs : Module.End.IsSemisimple (LinearMap.mulLeft K Y))
include hQ hg hY hs

/-- The four clauses for `(P(g), adV Y)`. -/
theorem jointClauses_specP_adV :
    JointClauses Q (specP Q g : Module.End K V) (adV Q Y) (finrank K V / 2) := by
  obtain ⟨hYg, hYx⟩ := mem_lieCentralizer.mp hY
  exact jointClauses_of_charZero hQ (fun u v => bform_specP g u v)
    (isSemisimple_specP_of_isSS Q g hg)
    (fun u v => bform_adV hYg u v) (isSemisimple_adV hYg hs)
    ((commute_iff_adV hQ g hYg).mp hYx).symm (det_specP g)

/-- **`⌊dim V/2⌋ + 1 ≤ dim gspin(V)_{g,Y}`**, for `g` and `Y` semisimple. -/
theorem le_finrank_lieCentralizer_gspin_of_isSemisimple :
    finrank K V / 2 + 1 ≤ finrank K (lieCentralizer (lieCentralizer (gspin Q)
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) Y) := by
  rw [finrank_lieCentralizer_lieCentralizer_gspin hQ g (mem_lieCentralizer.mp hY).1]
  exact Nat.add_le_add_right (jointClauses_specP_adV hQ g hg hY hs).1 1

/-- **`dim gspin(V)_{g,Y} = ⌊dim V/2⌋ + 1` iff `gspin(V)_{g,Y}` is abelian**, for `g` and `Y`
semisimple. -/
theorem finrank_lieCentralizer_gspin_eq_iff_isLieAbelian :
    finrank K (lieCentralizer (lieCentralizer (gspin Q)
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) Y) = finrank K V / 2 + 1 ↔
    IsLieAbelian (lieCentralizer (lieCentralizer (gspin Q)
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) Y) := by
  rw [finrank_lieCentralizer_lieCentralizer_gspin hQ g (mem_lieCentralizer.mp hY).1,
    isLieAbelian_lieCentralizer_gspin_iff hQ g (mem_lieCentralizer.mp hY).1,
    Nat.add_right_cancel_iff]
  exact (jointClauses_specP_adV hQ g hg hY hs).2.1

/-- **If `dim gspin(V)_{g,Y} = ⌊dim V/2⌋ + 1`, its only nilpotent element is `0`**, for `g` and `Y`
semisimple. -/
theorem eq_zero_of_isNilpotent_of_finrank_eq
    (he : finrank K (lieCentralizer (lieCentralizer (gspin Q)
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) Y) = finrank K V / 2 + 1)
    {Z : CliffordAlgebra Q}
    (hZ : Z ∈ lieCentralizer (lieCentralizer (gspin Q)
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) Y) (hn : IsNilpotent Z) : Z = 0 := by
  have hYg := (mem_lieCentralizer.mp hY).1
  have hZg := (mem_lieCentralizer.mp (mem_lieCentralizer.mp hZ).1).1
  rw [finrank_lieCentralizer_lieCentralizer_gspin hQ g hYg, Nat.add_right_cancel_iff] at he
  have h0 := (jointClauses_specP_adV hQ g hg hY hs).2.2.1 he _ (adV_mem_soCent_inf hQ g hYg hZ)
    (isNilpotent_adV hZg hn)
  obtain ⟨r, rfl⟩ := eq_algebraMap_of_adV_eq_zero hQ hZg h0
  obtain ⟨k, hk⟩ := hn
  rw [← map_pow] at hk
  have hr : IsNilpotent r :=
    ⟨k, (algebraMap K (CliffordAlgebra Q)).injective (hk.trans (map_zero _).symm)⟩
  rw [hr.eq_zero, map_zero]

end Factor

/-! ## The centralizer `𝔤_{g,Z}` in `𝔤 = gspin(W) × gspin(V)` -/

section Pair

/-- A Lie subalgebra of an associative algebra is abelian iff its elements commute. -/
theorem isLieAbelian_iff_forall_commute {K A : Type*} [Field K] [Ring A] [Algebra K A]
    {L : LieSubalgebra K A} : IsLieAbelian L ↔ ∀ X₁ ∈ L, ∀ X₂ ∈ L, X₁ * X₂ = X₂ * X₁ :=
  ⟨fun h X₁ h₁ X₂ h₂ => by
    have := congrArg Subtype.val (h.trivial ⟨X₁, h₁⟩ ⟨X₂, h₂⟩)
    rwa [LieSubalgebra.coe_bracket, Ring.lie_def, ZeroMemClass.coe_zero, sub_eq_zero] at this,
   fun h => ⟨fun X₁ X₂ => Subtype.ext (by
    rw [LieSubalgebra.coe_bracket, Ring.lie_def, ZeroMemClass.coe_zero, sub_eq_zero]
    exact h _ X₁.2 _ X₂.2)⟩⟩

/-- `L_Y = L ∩ ker (ad Y)`. -/
theorem lieCentralizer_toSubmodule_eq {K A : Type*} [Field K] [Ring A] [Algebra K A]
    (L : LieSubalgebra K A) (Y : A) :
    (lieCentralizer L Y).toSubmodule = L.toSubmodule ⊓ LinearMap.ker (LieAlgebra.ad K A Y) := by
  ext X
  rw [LieSubalgebra.mem_toSubmodule, mem_lieCentralizer, Submodule.mem_inf, LinearMap.mem_ker,
    LieAlgebra.ad_apply, Ring.lie_def, sub_eq_zero, LieSubalgebra.mem_toSubmodule]

variable {K : Type*} [Field K] [Invertible (2 : K)] (d : GGPData K)

/-- `𝔤_{a,Y} = gspin(W)_{a₁,Y₁} × gspin(V)_{a₂,Y₂}`. -/
theorem mem_lieCentralizer_lieCentralizer_lie {a Y X : d.ambient} :
    X ∈ lieCentralizer (lieCentralizer d.lie a) Y ↔
      X.1 ∈ lieCentralizer (lieCentralizer (gspin d.QW) a.1) Y.1 ∧
        X.2 ∈ lieCentralizer (lieCentralizer (gspin d.QV) a.2) Y.2 := by
  have hl : ∀ Z : d.ambient, Z ∈ d.lie ↔ Z.1 ∈ gspin d.QW ∧ Z.2 ∈ gspin d.QV := fun Z => Iff.rfl
  simp only [mem_lieCentralizer, hl, Prod.ext_iff, Prod.fst_mul, Prod.snd_mul]
  tauto

/-- `𝔤_{a,Y}` is abelian iff both factors are. -/
theorem isLieAbelian_lieCentralizer_lieCentralizer_lie_iff {a Y : d.ambient} :
    IsLieAbelian (lieCentralizer (lieCentralizer d.lie a) Y) ↔
      IsLieAbelian (lieCentralizer (lieCentralizer (gspin d.QW) a.1) Y.1) ∧
        IsLieAbelian (lieCentralizer (lieCentralizer (gspin d.QV) a.2) Y.2) := by
  rw [isLieAbelian_iff_forall_commute, isLieAbelian_iff_forall_commute,
    isLieAbelian_iff_forall_commute]
  have h0W : (0 : CliffordAlgebra d.QW) ∈ lieCentralizer (lieCentralizer (gspin d.QW) a.1) Y.1 :=
    zero_mem _
  have h0V : (0 : CliffordAlgebra d.QV) ∈ lieCentralizer (lieCentralizer (gspin d.QV) a.2) Y.2 :=
    zero_mem _
  constructor
  · intro h
    refine ⟨fun X₁ h₁ X₂ h₂ => ?_, fun X₁ h₁ X₂ h₂ => ?_⟩
    · have := h (X₁, 0) ((mem_lieCentralizer_lieCentralizer_lie d).2 ⟨h₁, h0V⟩) (X₂, 0)
        ((mem_lieCentralizer_lieCentralizer_lie d).2 ⟨h₂, h0V⟩)
      exact congrArg Prod.fst this
    · have := h (0, X₁) ((mem_lieCentralizer_lieCentralizer_lie d).2 ⟨h0W, h₁⟩) (0, X₂)
        ((mem_lieCentralizer_lieCentralizer_lie d).2 ⟨h0W, h₂⟩)
      exact congrArg Prod.snd this
  · rintro ⟨hW, hV⟩ X₁ h₁ X₂ h₂
    rw [mem_lieCentralizer_lieCentralizer_lie] at h₁ h₂
    exact Prod.ext (hW _ h₁.1 _ h₂.1) (hV _ h₁.2 _ h₂.2)

end Pair

section Assembly

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

/-- The rank `ℓ = (⌊dim W/2⌋ + 1) + (⌊dim V/2⌋ + 1)` of `𝔤 = gspin(W) × gspin(V)`. -/
def lieRankNat : ℕ := (finrank F (Fin d.m → F) / 2 + 1) + (finrank F d.V / 2 + 1)

variable (g : ↥d.G) (hg : IsSS F ((g : d.ambientˣ) : d.ambient))
include hg

/-- **The clauses for `𝔤_{g,Z}`**, `g ∈ G(F)` and `Z ∈ 𝔤_g` semisimple: `ℓ ≤ dim 𝔤_{g,Z}`; equality
iff `𝔤_{g,Z}` is abelian; and then `0` is its only nilpotent element. -/
theorem lieClauses {Z : d.ambient}
    (hZ : Z ∈ lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) (hs : IsSS F Z) :
    lieRankNat d ≤
      finrank F (lieCentralizer (lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) Z) ∧
    (finrank F (lieCentralizer (lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) Z) =
        lieRankNat d ↔
      IsLieAbelian (lieCentralizer (lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) Z)) ∧
    (finrank F (lieCentralizer (lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) Z) =
        lieRankNat d → ∀ X ∈ lieCentralizer (lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) Z,
      IsNilpotent X → X = 0) := by
  set a : d.ambient := ((g : d.ambientˣ) : d.ambient)
  have ha1 : a.1 = ((d.fst g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) := rfl
  have ha2 : a.2 = ((d.snd g : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) := rfl
  have hfst : ∀ {X : d.ambient}, IsSS F X → IsSS F X.1 := fun hX =>
    isSS_algHom (AlgHom.fst F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) hX
  have hsnd : ∀ {X : d.ambient}, IsSS F X → IsSS F X.2 := fun hX =>
    isSS_algHom (AlgHom.snd F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) hX
  have hg1 := hfst hg
  have hg2 := hsnd hg
  have hs1 := hfst hs
  have hs2 := hsnd hs
  obtain ⟨⟨hZW, hZV⟩, hZa⟩ := mem_lieCentralizer.mp hZ
  have hZ1 : Z.1 ∈ lieCentralizer (gspin d.QW) a.1 :=
    mem_lieCentralizer.mpr ⟨hZW, congrArg Prod.fst hZa⟩
  have hZ2 : Z.2 ∈ lieCentralizer (gspin d.QV) a.2 :=
    mem_lieCentralizer.mpr ⟨hZV, congrArg Prod.snd hZa⟩
  rw [ha1] at hg1 hZ1
  rw [ha2] at hg2 hZ2
  have l1 := le_finrank_lieCentralizer_gspin_of_isSemisimple d.nondeg (d.fst g) hg1 hZ1 hs1
  have l2 := le_finrank_lieCentralizer_gspin_of_isSemisimple d.nondeg_QV (d.snd g) hg2 hZ2 hs2
  have e1 := finrank_lieCentralizer_gspin_eq_iff_isLieAbelian d.nondeg (d.fst g) hg1 hZ1 hs1
  have e2 := finrank_lieCentralizer_gspin_eq_iff_isLieAbelian d.nondeg_QV (d.snd g) hg2 hZ2 hs2
  have n1 := eq_zero_of_isNilpotent_of_finrank_eq d.nondeg (d.fst g) hg1 hZ1 hs1
  have n2 := eq_zero_of_isNilpotent_of_finrank_eq d.nondeg_QV (d.snd g) hg2 hZ2 hs2
  rw [← ha1] at l1 e1 n1
  rw [← ha2] at l2 e2 n2
  rw [finrank_lieCentralizer_lieCentralizer_lie, isLieAbelian_lieCentralizer_lieCentralizer_lie_iff,
    ← e1, ← e2]
  unfold lieRankNat
  have hle : ∀ {A B p q : ℕ}, p ≤ A → q ≤ B → A + B = p + q → A = p ∧ B = q := by
    intro A B p q h1 h2 h; omega
  refine ⟨Nat.add_le_add l1 l2, ⟨fun he => ⟨(hle l1 l2 he).1, (hle l1 l2 he).2⟩,
    fun ⟨h1, h2⟩ => by rw [h1, h2]⟩, fun he X hX hn => ?_⟩
  rw [mem_lieCentralizer_lieCentralizer_lie] at hX
  obtain ⟨k, hk⟩ := hn
  exact Prod.ext (n1 (hle l1 l2 he).1 hX.1 ⟨k, by rw [← Prod.pow_fst, hk, Prod.fst_zero]⟩)
    (n2 (hle l1 l2 he).2 hX.2 ⟨k, by rw [← Prod.pow_snd, hk, Prod.snd_zero]⟩)

/-- **The regular semisimple set of `𝔤_g` is open**, for `g ∈ G(F)` semisimple. Near a regular
semisimple `Z₀`, `dim ker (ad Z)^D ≤ dim ker (ad Z₀)^D = dim 𝔤_{g,Z₀} = ℓ` (semicontinuity;
`D = dim C(W) × C(V)`). For the Jordan decomposition `Z = s + n` (both in `𝔤_g`), `𝔤_{g,s}` lies in
`ker (ad Z)^D`, so `dim 𝔤_{g,s} = ℓ` (`lieClauses`): then `𝔤_{g,s}` is abelian and its nilpotent
element `n` is `0`, so `Z = s` is regular semisimple. -/
theorem isOpen_setOf_isRegularSS_lieCentralizer :
    IsOpen {Z : ↥(lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) |
      IsRegularSS (lieCentralizer d.lie ((g : d.ambientˣ) : d.ambient)) (Z : d.ambient)} := by
  set a : d.ambient := ((g : d.ambientˣ) : d.ambient)
  set L := lieCentralizer d.lie a
  set D := finrank F d.ambient
  let ad : d.ambient → Module.End F d.ambient := fun Y => LieAlgebra.ad F d.ambient Y
  let f : ↥L → (↥L.toSubmodule →ₗ[F] d.ambient) := fun Z =>
    (ad (Z : d.ambient) ^ D) ∘ₗ L.toSubmodule.subtype
  -- continuity of `Z ↦ (ad Z)^D v`
  have hc : ∀ (k : ℕ) (w : d.ambient), Continuous fun Y : d.ambient => (ad Y ^ k) w := by
    intro k
    induction k with
    | zero => intro w; exact continuous_const
    | succ k ih =>
      intro w
      simp only [pow_succ', Module.End.mul_apply, ad, LieAlgebra.ad_apply, Ring.lie_def]
      exact (continuous_id.mul (ih w)).sub ((ih w).mul continuous_id)
  have hf : ∀ v, Continuous fun Z : ↥L => f Z v := fun v =>
    (hc D v).comp continuous_subtype_val
  -- `dim ker f Z = dim (𝔤_g ∩ ker (ad Z)^D)`
  have hker : ∀ Z : ↥L, finrank F (LinearMap.ker (f Z)) =
      finrank F ↥(L.toSubmodule ⊓ LinearMap.ker (ad (Z : d.ambient) ^ D)) := by
    intro Z
    rw [← Submodule.finrank_map_subtype_eq L.toSubmodule, LinearMap.ker_comp,
      Submodule.map_comap_subtype]
  have hD : 0 < D := Module.finrank_pos
  have hlie : ∀ Y, finrank F (lieCentralizer L Y) =
      finrank F ↥(L.toSubmodule ⊓ LinearMap.ker (ad Y)) := fun Y => by
    rw [← lieCentralizer_toSubmodule_eq]; rfl
  rw [isOpen_iff_mem_nhds]
  intro Z₀ hZ₀
  obtain ⟨hss₀, hab₀⟩ := hZ₀
  have hcl₀ := lieClauses d g hg Z₀.2 hss₀
  have h₀ : finrank F (LinearMap.ker (f Z₀)) = lieRankNat d := by
    rw [hker, ker_pow_eq_ker_of_isSemisimple
      (LieAlgebra.ad_isSemisimple_of_isSemisimple_mulLeft hss₀) hD, ← hlie]
    exact hcl₀.2.1.mpr hab₀
  filter_upwards [eventually_finrank_ker_le f hf Z₀] with Z hZ
  rw [h₀] at hZ
  -- the Jordan decomposition `Z = s + n`
  obtain ⟨hZl, hZa⟩ := mem_lieCentralizer.mp Z.2
  obtain ⟨s, hs, n, hn, hss, hnil, hZsn⟩ := exists_jordan_algebra (F := F) (Z : d.ambient)
  have hsZ : Commute (Z : d.ambient) s := Algebra.commute_of_mem_adjoin_self hs
  have hsn : Commute s n := Algebra.commute_of_mem_adjoin_singleton_of_commute hn hsZ.symm
  have hfst : s.1 ∈ Algebra.adjoin F {(Z : d.ambient).1} := by
    have h : AlgHom.fst F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV) s ∈
        (Algebra.adjoin F {(Z : d.ambient)}).map
          (AlgHom.fst F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) :=
      Subalgebra.mem_map.mpr ⟨s, hs, rfl⟩
    rwa [AlgHom.map_adjoin, Set.image_singleton] at h
  have hsnd : s.2 ∈ Algebra.adjoin F {(Z : d.ambient).2} := by
    have h : AlgHom.snd F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV) s ∈
        (Algebra.adjoin F {(Z : d.ambient)}).map
          (AlgHom.snd F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) :=
      Subalgebra.mem_map.mpr ⟨s, hs, rfl⟩
    rwa [AlgHom.map_adjoin, Set.image_singleton] at h
  obtain ⟨k, hk⟩ := hnil
  have hn1 : IsNilpotent ((Z : d.ambient).1 - s.1) :=
    ⟨k, by rw [hZsn, Prod.fst_add, add_sub_cancel_left, ← Prod.pow_fst, hk, Prod.fst_zero]⟩
  have hn2 : IsNilpotent ((Z : d.ambient).2 - s.2) :=
    ⟨k, by rw [hZsn, Prod.snd_add, add_sub_cancel_left, ← Prod.pow_snd, hk, Prod.snd_zero]⟩
  have hsL : s ∈ L := mem_lieCentralizer.mpr
    ⟨⟨mem_gspin_of_mem_adjoin hZl.1 hfst
        (isSS_algHom (AlgHom.fst F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) hss) hn1,
      mem_gspin_of_mem_adjoin hZl.2 hsnd
        (isSS_algHom (AlgHom.snd F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)) hss) hn2⟩,
      Algebra.commute_of_mem_adjoin_singleton_of_commute hs hZa⟩
  have hnL : n ∈ L := by
    have := L.sub_mem Z.2 hsL
    rwa [hZsn, add_sub_cancel_left] at this
  -- `𝔤_{g,s} ⊆ ker (ad Z)^D`
  have hle : finrank F (lieCentralizer L s) ≤ lieRankNat d := by
    refine le_trans ?_ ((hker Z).symm.trans_le hZ)
    rw [hlie]
    refine Submodule.finrank_mono (inf_le_inf_left _ ?_)
    have had : ad (Z : d.ambient) = ad s + ad n := by
      simp only [ad, hZsn, map_add]
    rw [had]
    exact ker_le_ker_pow_add (LieAlgebra.commute_ad_of_commute hsn)
      (LieAlgebra.ad_nilpotent_of_nilpotent ⟨k, hk⟩)
  have hcl := lieClauses d g hg hsL hss
  have heq : finrank F (lieCentralizer L s) = lieRankNat d := le_antisymm hle hcl.1
  have hn0 : n = 0 := hcl.2.2 heq n (mem_lieCentralizer.mpr ⟨hnL, hsn.eq⟩) ⟨k, hk⟩
  change IsRegularSS L (Z : d.ambient)
  rw [hZsn, hn0, add_zero]
  exact ⟨hss, hcl.2.1.mp heq⟩

end Assembly

end GSpinGGP
