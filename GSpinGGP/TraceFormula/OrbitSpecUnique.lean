/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LuoTorus
import GSpinGGP.GGP.RegularOrbitClass
import GSpinGGP.GGP.RegularNilpotentConverse
import GSpinGGP.GGP.MovedCentralizer

/-!
# At most one regular nilpotent orbit of `𝔤⁰_X` meets Luo's recipe

For `X ∈ 𝔱⁰_♮` (`IsGammaEltLie T X`, `T = T_x` with `x ∈ Γ(G,H)`) let `W' = ker X`,
`W'' = W'^⊥`, `V' = W' ⊕ Z`.  The regular nilpotent orbits of `𝔤⁰_X` under `Z_G(X)` meeting
`OrbitSpecAt W'` (Luo §7.1: `O_ν` on `V'`, `O_{−ν}` on `W'`) coincide
(`orbitSpecAt_orbit_unique`).

* `exists_mem_soSub_adV_eq`, `finrank_lieCentralizer_lieCentralizer_soSub`: `adV` identifies
  `so_Cliff(V)_{X,Y}` with `so(V)_{adV X} ⊓ so(V)_{adV Y}`;
  `finrank_lieCentralizer_lieCentralizer_lieZero`: `𝔤⁰_{a,Y}` is the product of its factors.
* `isCompl_ker_adV`, `ker_adV_diagLie_snd`: `W = W' ⊥ W''` and `ker (ad X on V) = W' ⊕ Z`.
* `eq_zero_of_isNilpotent_of_commute`: a nilpotent skew endomorphism of `W` commuting with `ad X`
  and killing `W'` is `0` (it lies in `𝔱⁰`, whose elements are semisimple,
  `isSS_of_commute_of_isGammaElt`); so a nilpotent `Y ∈ 𝔤⁰_X` kills `W''` on both factors
  (`adV_fst_eq_zero_of_isNilpotent`, `adV_snd_eq_zero_of_isNilpotent`).
* `finrank_soCent_ker_eq_of_le`: a regular nilpotent `Y ∈ 𝔤⁰_X` has
  `dim so(W')_{Y|W'} = ⌊dim W'/2⌋` and `dim so(V')_{Y|V'} = ⌊dim V'/2⌋` (change one factor's
  `W'`-part at a time, as for `nilReg_centralizer_nonempty_imp`).
* `exists_conj_of_isometries`: isometries of determinant `1` of `W` and `V` commuting with `ad X`
  and conjugating `ad Y` to `ad Y'` lift to `γ ∈ Z_G(X)` with `γ Y γ⁻¹ = Y'`.
* `orbitSpecAt_orbit_unique`: on the odd one of `W'`, `V'` the restriction of `ad Y` is a single
  Jordan block (`pow_ne_zero_of_finrank_soCent_eq`), conjugate in `SO` by
  `SingleBlock.exists_isometry_det_one_conj_of_pow_ne_zero_sub`; on the even one it is pinned by
  `IsInOrbitNu` (`SingleBlock.exists_isometry_det_one_conj_of_isInOrbitNu_sub`) or vanishes
  (dimension `≤ 2`, `SingleBlock.eq_zero_of_finrank_le_two`).
-/

noncomputable section

open Module CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

/-! ## `adV` on `so_Cliff(V)` -/

section SoSubCent

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **`adV` maps `so_Cliff(V)` onto the skew endomorphisms** (a combination of bivectors,
`exists_mem_quadratic_commutator_eq`). -/
theorem exists_mem_soSub_adV_eq {Q : QuadraticForm K V} (hQ : IsNondeg Q) (M : Module.End K V)
    (hMs : ∀ u w, bform Q (M u) w = -bform Q u (M w)) : ∃ Z ∈ soSub Q, adV Q Z = M := by
  obtain ⟨Z, hZq, hZ⟩ := exists_mem_quadratic_commutator_eq hQ M hMs
  have hZs := quadraticLieSubalgebra_le_soSub Q hZq
  exact ⟨Z, hZs, by ext v; apply ι_injective Q; rw [ι_adV hZs.1, hZ]⟩

/-- `adV` is injective on `so_Cliff(V)`. -/
theorem eq_of_mem_soSub_of_adV_eq {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    {Z Z' : CliffordAlgebra Q} (hZ : Z ∈ soSub Q) (hZ' : Z' ∈ soSub Q) (h : adV Q Z = adV Q Z') :
    Z = Z' :=
  sub_eq_zero.mp (eq_zero_of_mem_soSub_of_adV_eq_zero hQ (sub_mem hZ hZ')
    (by rw [map_sub, h, sub_self]))

omit [FiniteDimensional K V] in
/-- Commuting elements of `gspin(V)` have commuting `adV`. -/
theorem adV_mul_comm_of_mul_comm {Q : QuadraticForm K V} {Z W : CliffordAlgebra Q}
    (hZ : Z ∈ gspin Q) (hW : W ∈ gspin Q) (h : W * Z = Z * W) :
    adV Q Z * adV Q W = adV Q W * adV Q Z := by
  have := adV_commutator hZ hW
  rw [← h, sub_self, map_zero, eq_comm, sub_eq_zero] at this
  exact this

/-- **`dim so_Cliff(V)_{X,Y} = dim (so(V)_{adV X} ⊓ so(V)_{adV Y})`**: `adV` is a bijection
between them (`exists_mem_soSub_adV_eq`, `commute_of_adV_commute`,
`eq_zero_of_mem_soSub_of_adV_eq_zero`).  The `so_Cliff` form of
`finrank_lieCentralizer_lieCentralizer_gspin`, without the scalars. -/
theorem finrank_lieCentralizer_lieCentralizer_soSub {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    {X Y : CliffordAlgebra Q} (hX : X ∈ soSub Q) (hY : Y ∈ soSub Q) :
    finrank K ↥(lieCentralizer (lieCentralizer (soSub Q) X) Y) =
      finrank K ↥(soCent Q (adV Q X) ⊓ soCent Q (adV Q Y)) := by
  have hmem : ∀ {Z}, Z ∈ lieCentralizer (lieCentralizer (soSub Q) X) Y ↔
      Z ∈ soSub Q ∧ X * Z = Z * X ∧ Y * Z = Z * Y := by
    intro Z; rw [mem_lieCentralizer, mem_lieCentralizer, and_assoc]
  let φ : ↥(lieCentralizer (lieCentralizer (soSub Q) X) Y) →ₗ[K]
      ↥(soCent Q (adV Q X) ⊓ soCent Q (adV Q Y)) :=
    { toFun := fun Z => ⟨adV Q Z, by
        obtain ⟨hZ, hXZ, hYZ⟩ := hmem.mp Z.2
        exact Submodule.mem_inf.mpr
          ⟨mem_soCent.2 ⟨bform_adV hZ.1, adV_mul_comm_of_mul_comm hZ.1 hX.1 hXZ⟩,
            mem_soCent.2 ⟨bform_adV hZ.1, adV_mul_comm_of_mul_comm hZ.1 hY.1 hYZ⟩⟩⟩
      map_add' := fun A B => Subtype.ext (map_add (adV Q) A.1 B.1)
      map_smul' := fun c A => Subtype.ext (map_smul (adV Q) c A.1) }
  have hinj : Function.Injective φ := fun A B h =>
    Subtype.ext (eq_of_mem_soSub_of_adV_eq hQ (hmem.mp A.2).1 (hmem.mp B.2).1
      (congrArg Subtype.val h))
  have hsurj : Function.Surjective φ := by
    rintro ⟨M, hM⟩
    obtain ⟨hMX, hMY⟩ := Submodule.mem_inf.mp hM
    obtain ⟨hMs, hMXc⟩ := mem_soCent.mp hMX
    obtain ⟨-, hMYc⟩ := mem_soCent.mp hMY
    obtain ⟨Z, hZ, rfl⟩ := exists_mem_soSub_adV_eq hQ M hMs
    exact ⟨⟨Z, hmem.mpr ⟨hZ, (commute_of_adV_commute hQ hZ.1 hX.1 hMXc).symm,
      (commute_of_adV_commute hQ hZ.1 hY.1 hMYc).symm⟩⟩, rfl⟩
  exact (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq

end SoSubCent

/-! ## Block endomorphisms -/

section SumEnd

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V] {U U' : Submodule K V}

theorem sumEnd_mul (h : IsCompl U U') (A C : Module.End K U) (A' C' : Module.End K U') :
    sumEnd h A A' * sumEnd h C C' = sumEnd h (A * C) (A' * C') := by
  symm
  refine LinearMap.ofIsCompl_eq h (fun u => ?_) (fun u => ?_)
  · simp [Module.End.mul_apply, sumEnd_left]
  · simp [Module.End.mul_apply, sumEnd_right]

theorem sumEnd_one (h : IsCompl U U') : sumEnd h (1 : Module.End K U) 1 = 1 :=
  LinearMap.ofIsCompl_eq h (fun _ => rfl) (fun _ => rfl)

theorem sumEnd_zero (h : IsCompl U U') : sumEnd h (0 : Module.End K U) 0 = 0 :=
  LinearMap.ofIsCompl_eq h (fun _ => by simp) (fun _ => by simp)

theorem sumEnd_pow (h : IsCompl U U') (A : Module.End K U) (A' : Module.End K U') (k : ℕ) :
    sumEnd h A A' ^ k = sumEnd h (A ^ k) (A' ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, pow_zero, sumEnd_one]
  | succ k ih => rw [pow_succ, ih, sumEnd_mul, ← pow_succ, ← pow_succ]

/-- `0 ⊕ A'` is nilpotent when `A'` is. -/
theorem isNilpotent_sumEnd_zero (h : IsCompl U U') {A' : Module.End K U'} (hA' : IsNilpotent A') :
    IsNilpotent (sumEnd h 0 A') := by
  obtain ⟨k, hk⟩ := hA'
  refine ⟨k + 1, ?_⟩
  rw [sumEnd_pow, zero_pow (Nat.succ_ne_zero k), pow_succ, hk, zero_mul, sumEnd_zero]

end SumEnd

/-! ## The part of a skew endomorphism on `(ker E)^⊥` -/

section KillPart

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- For skew `E` with `V = ker E ⊥ (ker E)^⊥` and skew `N` commuting with `E`, the endomorphism
`M = 0 ⊕ N|_{(ker E)^⊥}` is skew, commutes with `E`, kills `ker E`, agrees with `N` on
`(ker E)^⊥`, and is nilpotent if `N` is. -/
theorem exists_killPart {Q : QuadraticForm K V} {E N : Module.End K V}
    (hE : ∀ u w, bform Q (E u) w = -bform Q u (E w))
    (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w)) (hNE : N * E = E * N)
    (hc : IsCompl (LinearMap.ker E) ((bform Q).orthogonal (LinearMap.ker E))) :
    ∃ M : Module.End K V, (∀ u w, bform Q (M u) w = -bform Q u (M w)) ∧ M * E = E * M ∧
      (IsNilpotent N → IsNilpotent M) ∧ (∀ a ∈ LinearMap.ker E, M a = 0) ∧
      ∀ b ∈ (bform Q).orthogonal (LinearMap.ker E), M b = N b := by
  set A := LinearMap.ker E
  set B := (bform Q).orthogonal A
  have horth : ∀ u ∈ A, ∀ w ∈ B, bform Q u w = 0 := fun u hu w hw => hw u hu
  have hEA : Set.MapsTo E A A := fun a ha => by
    simp only [SetLike.mem_coe, A, LinearMap.mem_ker] at ha ⊢; rw [ha, map_zero]
  have hNA : Set.MapsTo N A A := fun a ha => by
    simp only [SetLike.mem_coe, A, LinearMap.mem_ker] at ha ⊢
    rw [← Module.End.mul_apply, ← hNE, Module.End.mul_apply, ha, map_zero]
  have hEB := mapsTo_orthogonal_of_skew hE hEA
  have hNB := mapsTo_orthogonal_of_skew hN hNA
  have hNmem : N ∈ soCent Q E := mem_soCent.2 ⟨hN, hNE⟩
  have h0 : (0 : Module.End K A) ∈ soCent (Q.comp A.subtype) (E.restrict hEA) :=
    mem_soCent.2 ⟨fun _ _ => by simp, by simp⟩
  have hM := sumEnd_mem_soCent horth hc hEA hEB h0 (restrict_mem_soCent hEB hNmem hNB)
  refine ⟨_, (mem_soCent.1 hM).1, (mem_soCent.1 hM).2,
    fun hNn => isNilpotent_sumEnd_zero hc (Module.End.isNilpotent.restrict hNB hNn),
    fun a ha => ?_, fun b hb => ?_⟩
  · simpa using sumEnd_left hc 0 (N.restrict hNB) ⟨a, ha⟩
  · exact sumEnd_right hc 0 (N.restrict hNB) ⟨b, hb⟩

end KillPart

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

/-! ## `𝔤⁰_{a,Y}` splits into its factors -/

theorem mem_lieCentralizer_lieCentralizer_lieZero {a Y Z : d.ambient} :
    Z ∈ lieCentralizer (lieCentralizer d.lieZero a) Y ↔
      Z.1 ∈ lieCentralizer (lieCentralizer (soSub d.QW) a.1) Y.1 ∧
        Z.2 ∈ lieCentralizer (lieCentralizer (soSub d.QV) a.2) Y.2 := by
  have hl : ∀ Z : d.ambient, Z ∈ d.lieZero ↔ Z.1 ∈ soSub d.QW ∧ Z.2 ∈ soSub d.QV :=
    fun Z => Iff.rfl
  simp only [mem_lieCentralizer, hl, Prod.ext_iff, Prod.fst_mul, Prod.snd_mul]
  tauto

/-- `dim 𝔤⁰_{a,Y} = dim so_Cliff(W)_{a₁,Y₁} + dim so_Cliff(V)_{a₂,Y₂}`. -/
theorem finrank_lieCentralizer_lieCentralizer_lieZero (a Y : d.ambient) :
    finrank F ↥(lieCentralizer (lieCentralizer d.lieZero a) Y) =
      finrank F ↥(lieCentralizer (lieCentralizer (soSub d.QW) a.1) Y.1) +
        finrank F ↥(lieCentralizer (lieCentralizer (soSub d.QV) a.2) Y.2) := by
  have h : (lieCentralizer (lieCentralizer d.lieZero a) Y).toSubmodule =
      (lieCentralizer (lieCentralizer (soSub d.QW) a.1) Y.1).toSubmodule.prod
        (lieCentralizer (lieCentralizer (soSub d.QV) a.2) Y.2).toSubmodule := by
    ext Z
    exact d.mem_lieCentralizer_lieCentralizer_lieZero
  show finrank F ↥(lieCentralizer (lieCentralizer d.lieZero a) Y).toSubmodule =
    finrank F ↥(lieCentralizer (lieCentralizer (soSub d.QW) a.1) Y.1).toSubmodule +
      finrank F ↥(lieCentralizer (lieCentralizer (soSub d.QV) a.2) Y.2).toSubmodule
  rw [h, (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]

/-! ## R0: the geometry of `X ∈ 𝔱⁰_♮` -/

/-- `W'_T = W'_x` for `T = T_x`. -/
theorem commonFixed_torusOf (x : ↥(GSpin d.QW)) : commonFixed (d.torusOf x) = fixedSub x := by
  apply le_antisymm
  · exact iInf_le_of_le ⟨x, d.self_mem_torusOf x⟩ le_rfl
  · exact le_iInf fun t w hw => (d.mem_fixedSub_iff).2 (t.2.2 w hw)

theorem ker_adV_eq_fixedSub {x : ↥(GSpin d.QW)} {X : CliffordAlgebra d.QW}
    (hX : d.IsGammaEltLie (d.torusOf x) X) : LinearMap.ker (adV d.QW X) = fixedSub x := by
  rw [hX.2.1, d.commonFixed_torusOf]

/-- **`W = W' ⊥ W''`** for `X ∈ 𝔱⁰_♮`, `W' = ker X`. -/
theorem isCompl_ker_adV {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) {X : CliffordAlgebra d.QW}
    (hX : d.IsGammaEltLie (d.torusOf x) X) :
    IsCompl (LinearMap.ker (adV d.QW X))
      ((bform d.QW).orthogonal (LinearMap.ker (adV d.QW X))) := by
  rw [d.ker_adV_eq_fixedSub hX]
  exact isCompl_fixedSub_orthogonal d.nondeg x (fixedSub_inf_movedSub_of_isSS x hx.1)

theorem adV_diagLie_snd {X : CliffordAlgebra d.QW} (hX : X ∈ soSub d.QW) (w : Fin d.m → F)
    (z : d.Z) : adV d.QV (d.diagLie X).2 (w, z) = (adV d.QW X w, 0) :=
  d.adV_map_inl hX.1 w z

/-- **On `V`, `ker X = W' ⊕ Z`.** -/
theorem ker_adV_diagLie_snd {X : CliffordAlgebra d.QW} (hX : X ∈ soSub d.QW) :
    LinearMap.ker (adV d.QV (d.diagLie X).2) = (LinearMap.ker (adV d.QW X)).prod ⊤ := by
  ext ⟨w, z⟩
  simp [LinearMap.mem_ker, d.adV_diagLie_snd hX]

theorem ker_adV_diagLie_snd_eq_fixedSub {x : ↥(GSpin d.QW)} {X : CliffordAlgebra d.QW}
    (hX : d.IsGammaEltLie (d.torusOf x) X) :
    LinearMap.ker (adV d.QV (d.diagLie X).2) = fixedSub (d.incl x) := by
  ext ⟨w, z⟩
  rw [d.ker_adV_diagLie_snd hX.1.1, d.mem_fixedSub_incl_iff, Submodule.mem_prod,
    d.ker_adV_eq_fixedSub hX]
  simp

/-- **`V = V' ⊥ V'^⊥`** with `V' = W' ⊕ Z` the kernel of `X` on `V`. -/
theorem isCompl_ker_adV_snd {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) {X : CliffordAlgebra d.QW}
    (hX : d.IsGammaEltLie (d.torusOf x) X) :
    IsCompl (LinearMap.ker (adV d.QV (d.diagLie X).2))
      ((bform d.QV).orthogonal (LinearMap.ker (adV d.QV (d.diagLie X).2))) := by
  rw [d.ker_adV_diagLie_snd_eq_fixedSub hX]
  exact isCompl_fixedSub_orthogonal d.nondeg_QV (d.incl x)
    (fixedSub_inf_movedSub_incl d x (fixedSub_inf_movedSub_of_isSS x hx.1))

/-! ## R1: nilpotent elements of `𝔤⁰_X` vanish on `W''` -/

/-- **A nilpotent skew endomorphism of `W` commuting with `ad X` and killing `W'` is `0`**, for
`X ∈ 𝔱⁰_♮`: its lift to `so_Cliff(W)` lies in `𝔱⁰` (`IsGammaEltLie`), so it commutes with `x` and
is semisimple (`isSS_of_commute_of_isGammaElt`). -/
theorem eq_zero_of_isNilpotent_of_commute {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    {X : CliffordAlgebra d.QW} (hX : d.IsGammaEltLie (d.torusOf x) X)
    {M : Module.End F (Fin d.m → F)} (hMs : ∀ u w, bform d.QW (M u) w = -bform d.QW u (M w))
    (hMn : IsNilpotent M) (hMX : M * adV d.QW X = adV d.QW X * M)
    (hMA : ∀ a ∈ LinearMap.ker (adV d.QW X), M a = 0) : M = 0 := by
  obtain ⟨Z, hZ, rfl⟩ := exists_mem_soSub_adV_eq d.nondeg M hMs
  have hZX : Z * X = X * Z := commute_of_adV_commute d.nondeg hZ.1 hX.1.1.1 hMX
  have hZT : Z ∈ d.lieTorus (d.torusOf x) :=
    hX.2.2 Z hZ hZX fun w hw => hMA w (by rw [hX.2.1]; exact hw)
  have hxZ := hZT.2.1 x (d.self_mem_torusOf x)
  have hss : IsSS F Z := d.isSS_of_commute_of_isGammaElt hx hZ.1 hxZ
    fun v hv => hMA v (by rw [d.ker_adV_eq_fixedSub hX]; exact hv)
  exact Module.End.eq_zero_of_isNilpotent_isSemisimple hMn (isSemisimple_adV hZ.1 hss)

/-! ## Skew endomorphisms of `V` killing `Z` -/

section Transfer

variable {M : Module.End F d.V}

/-- A skew endomorphism of `V = W ⊕ Z` killing `Z` takes values in `W`. -/
theorem snd_apply_eq_zero_of_skew (hMs : ∀ u w, bform d.QV (M u) w = -bform d.QV u (M w))
    (hMz : ∀ z : d.Z, M (0, z) = 0) (v : d.V) : (M v).2 = 0 := by
  refine (isNondeg_iff _).mp (isNondeg_splitOddForm d.r d.ν.ne_zero) _ fun z => ?_
  have := hMs (0, z) v
  rw [hMz z, map_zero, LinearMap.zero_apply, bform_prod] at this
  simp only [map_zero, LinearMap.zero_apply, zero_add] at this
  rw [bform_comm]; linear_combination this

/-- A skew endomorphism of `V` killing `Z` is `(w, z) ↦ (M_W w, 0)`. -/
theorem apply_eq_of_skew (hMs : ∀ u w, bform d.QV (M u) w = -bform d.QV u (M w))
    (hMz : ∀ z : d.Z, M (0, z) = 0) (v : d.V) : M v = ((M (v.1, 0)).1, 0) := by
  have e : v = (v.1, 0) + (0, v.2) := by simp
  conv_lhs => rw [e, map_add, hMz, add_zero]
  exact Prod.ext rfl (d.snd_apply_eq_zero_of_skew hMs hMz _)

/-- The `W`-part `M_W = fst ∘ M ∘ inl` of an endomorphism of `V`. -/
abbrev wPart (M : Module.End F d.V) : Module.End F (Fin d.m → F) :=
  LinearMap.fst F _ _ ∘ₗ M ∘ₗ LinearMap.inl F _ _

theorem wPart_skew (hMs : ∀ u w, bform d.QV (M u) w = -bform d.QV u (M w))
    (hMz : ∀ z : d.Z, M (0, z) = 0) (a b : Fin d.m → F) :
    bform d.QW (d.wPart M a) b = -bform d.QW a (d.wPart M b) := by
  have := hMs (a, 0) (b, 0)
  rw [d.apply_eq_of_skew hMs hMz (a, 0), d.apply_eq_of_skew hMs hMz (b, 0), bform_prod,
    bform_prod] at this
  simpa using this

theorem wPart_commute {E : Module.End F (Fin d.m → F)} {EV : Module.End F d.V}
    (hEV : ∀ w z, EV (w, z) = (E w, 0)) (hME : M * EV = EV * M) :
    d.wPart M * E = E * d.wPart M := by
  refine LinearMap.ext fun w => ?_
  have := congrArg (fun T : Module.End F d.V => (T (w, 0)).1) hME
  simp only [Module.End.mul_apply, hEV] at this
  exact this

theorem pow_apply_inl (hMs : ∀ u w, bform d.QV (M u) w = -bform d.QV u (M w))
    (hMz : ∀ z : d.Z, M (0, z) = 0) (k : ℕ) (w : Fin d.m → F) :
    (M ^ k) (w, 0) = ((d.wPart M ^ k) w, 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, d.apply_eq_of_skew hMs hMz, pow_succ',
      Module.End.mul_apply]
    rfl

theorem isNilpotent_wPart (hMs : ∀ u w, bform d.QV (M u) w = -bform d.QV u (M w))
    (hMz : ∀ z : d.Z, M (0, z) = 0) (hMn : IsNilpotent M) : IsNilpotent (d.wPart M) := by
  obtain ⟨k, hk⟩ := hMn
  refine ⟨k, LinearMap.ext fun w => ?_⟩
  have := d.pow_apply_inl hMs hMz k w
  rw [hk, LinearMap.zero_apply] at this
  exact (congrArg Prod.fst this).symm

theorem eq_zero_of_wPart_eq_zero (hMs : ∀ u w, bform d.QV (M u) w = -bform d.QV u (M w))
    (hMz : ∀ z : d.Z, M (0, z) = 0) (h : d.wPart M = 0) : M = 0 := by
  refine LinearMap.ext fun v => ?_
  rw [d.apply_eq_of_skew hMs hMz v]
  have := LinearMap.congr_fun h v.1
  simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.fst_apply,
    LinearMap.zero_apply] at this
  rw [this]; rfl

end Transfer

/-- **R1 on `W`**: a nilpotent `Y ∈ 𝔤⁰_X` kills `W''` on `W`. -/
theorem adV_fst_eq_zero_of_isNilpotent {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    {X : CliffordAlgebra d.QW} (hX : d.IsGammaEltLie (d.torusOf x) X) {Y : d.ambient}
    (hY : Y ∈ lieCentralizer d.lieZero (d.diagLie X)) (hYn : IsNilpotent Y) :
    ∀ b ∈ (bform d.QW).orthogonal (LinearMap.ker (adV d.QW X)), adV d.QW Y.1 b = 0 := by
  obtain ⟨⟨hY1, -⟩, hYc⟩ := mem_lieCentralizer.mp hY
  have hXY : X * Y.1 = Y.1 * X := congrArg Prod.fst hYc
  have hX0 : X ∈ soSub d.QW := hX.1.1
  obtain ⟨M, hMs, hME, hMn, hMA, hMB⟩ := exists_killPart (bform_adV hX0.1) (bform_adV hY1.1)
    (adV_mul_comm_of_mul_comm hY1.1 hX0.1 hXY) (d.isCompl_ker_adV hx hX)
  have h0 := d.eq_zero_of_isNilpotent_of_commute hx hX hMs
    (hMn (isNilpotent_adV hY1.1 (hYn.map (RingHom.fst _ _)))) hME hMA
  intro b hb
  rw [← hMB b hb, h0, LinearMap.zero_apply]

/-- **R1 on `V`**: a nilpotent `Y ∈ 𝔤⁰_X` kills `(W' ⊕ Z)^⊥ = W''` on `V` (through the
`W`-part, `wPart`). -/
theorem adV_snd_eq_zero_of_isNilpotent {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    {X : CliffordAlgebra d.QW} (hX : d.IsGammaEltLie (d.torusOf x) X) {Y : d.ambient}
    (hY : Y ∈ lieCentralizer d.lieZero (d.diagLie X)) (hYn : IsNilpotent Y) :
    ∀ b ∈ (bform d.QV).orthogonal (LinearMap.ker (adV d.QV (d.diagLie X).2)),
      adV d.QV Y.2 b = 0 := by
  obtain ⟨⟨-, hY2⟩, hYc⟩ := mem_lieCentralizer.mp hY
  have hXY : (d.diagLie X).2 * Y.2 = Y.2 * (d.diagLie X).2 := congrArg Prod.snd hYc
  have hX0 : X ∈ soSub d.QW := hX.1.1
  have hXV : (d.diagLie X).2 ∈ soSub d.QV := (d.diagLie_mem_lieZero hX0).2
  obtain ⟨M, hMs, hME, hMn, hMA, hMB⟩ := exists_killPart (bform_adV hXV.1) (bform_adV hY2.1)
    (adV_mul_comm_of_mul_comm hY2.1 hXV.1 hXY) (d.isCompl_ker_adV_snd hx hX)
  have hMz : ∀ z : d.Z, M (0, z) = 0 := fun z => hMA _ (by
    rw [d.ker_adV_diagLie_snd hX0]; exact ⟨zero_mem _, trivial⟩)
  have hw := d.eq_zero_of_isNilpotent_of_commute hx hX (d.wPart_skew hMs hMz)
    (d.isNilpotent_wPart hMs hMz (hMn (isNilpotent_adV hY2.1 (hYn.map (RingHom.snd _ _)))))
    (d.wPart_commute (d.adV_diagLie_snd hX0) hME) fun a ha => by
      show (M (a, 0)).1 = 0
      rw [hMA (a, 0) (by rw [d.ker_adV_diagLie_snd hX0]; exact ⟨ha, trivial⟩), Prod.fst_zero]
  have h0 := d.eq_zero_of_wPart_eq_zero hMs hMz hw
  intro b hb
  rw [← hMB b hb, h0, LinearMap.zero_apply]

end GGPData

end GSpinGGP
