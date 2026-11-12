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

/-! ## Minimal centralizer on `ker X` -/

section FactorRegular

variable {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [CharZero K] [FiniteDimensional K V] in
theorem soCent_one_add (Q : QuadraticForm K V) (N : Module.End K V) :
    soCent Q (1 + N) = soCent Q N := by
  ext M
  simp only [mem_soCent, mul_add, add_mul, mul_one, one_mul, add_right_inj]

/-- **A minimizer of `dim so_Cliff(V)_{X,·}` killing `(ker X)^⊥` has minimal centralizer on
`ker X`**: with `A = ker (adV X)`, `V = A ⊥ A^⊥`, if `Y ∈ so_Cliff(V)_X` kills `A^⊥` and
`dim so_Cliff(V)_{X,Y} ≤ dim so_Cliff(V)_{X,Y'}` for all `Y' ∈ so_Cliff(V)_X`, then
`dim so(A)_{adV Y|_A} = ⌊dim A/2⌋`.  Changing the `A`-part of `adV Y` to any skew `M`
(`sumEnd`, lifted by `exists_mem_soSub_adV_eq`) changes `dim so_Cliff(V)_{X,·}` by
`dim so(A)_M − dim so(A)_{adV Y|_A}` (`finrank_soCent_inf_eq` for `g = 1 + adV X`,
`soCent_inf_killSub_congr`); conclude with `exists_skew_finrank_soCent_le` and
`le_finrank_soCent`.  The `so_Cliff` form of `isQuasiSplitQF_fixedSub_of_forall_finrank_le`. -/
theorem finrank_soCent_ker_eq_of_forall_le {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    {Xc Yc : CliffordAlgebra Q} (hXc : Xc ∈ soSub Q) (hYc : Yc ∈ lieCentralizer (soSub Q) Xc)
    (hc : IsCompl (LinearMap.ker (adV Q Xc))
      ((bform Q).orthogonal (LinearMap.ker (adV Q Xc))))
    (hYB : ∀ b ∈ (bform Q).orthogonal (LinearMap.ker (adV Q Xc)), adV Q Yc b = 0)
    (hmin : ∀ Y' ∈ lieCentralizer (soSub Q) Xc,
      finrank K ↥(lieCentralizer (lieCentralizer (soSub Q) Xc) Yc) ≤
        finrank K ↥(lieCentralizer (lieCentralizer (soSub Q) Xc) Y'))
    (hYA : ∀ a ∈ LinearMap.ker (adV Q Xc), adV Q Yc a ∈ LinearMap.ker (adV Q Xc)) :
    finrank K ↥(soCent (Q.comp (LinearMap.ker (adV Q Xc)).subtype) ((adV Q Yc).restrict hYA)) =
      finrank K ↥(LinearMap.ker (adV Q Xc)) / 2 := by
  set A := LinearMap.ker (adV Q Xc)
  set B := (bform Q).orthogonal A
  set E := adV Q Xc
  have hE := bform_adV (Q := Q) hXc.1
  have horth : ∀ u ∈ A, ∀ w ∈ B, bform Q u w = 0 := fun u hu w hw => hw u hu
  have hEA : Set.MapsTo E A A := fun a ha => by
    simp only [SetLike.mem_coe, A, E, LinearMap.mem_ker] at ha ⊢; rw [ha, map_zero]
  have hEB := mapsTo_orthogonal_of_skew hE hEA
  have hAg : ∀ v, v ∈ A ↔ (1 + E) v = v := fun v => by
    simp [A, E, LinearMap.mem_ker]
  have hgB : ∀ b ∈ B, (1 + E) b ∈ B := fun b hb => by
    rw [LinearMap.add_apply, Module.End.one_apply]; exact add_mem hb (hEB hb)
  have hQA := isNondeg_comp_subtype_of_isCompl hc
  -- the dimension formula
  have key : ∀ Z ∈ lieCentralizer (soSub Q) Xc, ∀ hZA : ∀ a ∈ A, adV Q Z a ∈ A,
      finrank K ↥(lieCentralizer (lieCentralizer (soSub Q) Xc) Z) =
        finrank K ↥(soCent (Q.comp A.subtype) ((adV Q Z).restrict hZA)) +
        finrank K ↥(soCent Q (1 + E) ⊓ soCent Q (adV Q Z) ⊓ killSub A) := by
    intro Z hZ hZA
    obtain ⟨hZs, hZX⟩ := mem_lieCentralizer.mp hZ
    have hZE : adV Q Z * E = E * adV Q Z := adV_mul_comm_of_mul_comm hZs.1 hXc.1 hZX
    have hZg : adV Q Z * (1 + E) = (1 + E) * adV Q Z := by
      rw [mul_add, add_mul, mul_one, one_mul, hZE]
    rw [finrank_lieCentralizer_lieCentralizer_soSub hQ hXc hZs, ← soCent_one_add Q E]
    exact finrank_soCent_inf_eq hc hAg hgB (bform_adV hZs.1) hZg
  have hYs := (mem_lieCentralizer.mp hYc).1
  have hNs : ∀ u w, bform (Q.comp A.subtype) ((adV Q Yc).restrict hYA u) w =
      -bform (Q.comp A.subtype) u ((adV Q Yc).restrict hYA w) := fun u w => by
    simp only [bform_comp_subtype, LinearMap.coe_restrict_apply]; exact bform_adV hYs.1 _ _
  have hle : ∀ M : Module.End K A, (∀ u w, bform (Q.comp A.subtype) (M u) w =
      -bform (Q.comp A.subtype) u (M w)) →
      finrank K ↥(soCent (Q.comp A.subtype) ((adV Q Yc).restrict hYA)) ≤
        finrank K ↥(soCent (Q.comp A.subtype) M) := by
    intro M hM
    have hM0 : M ∈ soCent (Q.comp A.subtype) (E.restrict hEA) := by
      have hr : E.restrict hEA = 0 := LinearMap.ext fun a => Subtype.ext a.2
      exact mem_soCent.2 ⟨hM, by rw [hr, mul_zero, zero_mul]⟩
    have h0 : (0 : Module.End K B) ∈ soCent (Q.comp B.subtype) (E.restrict hEB) :=
      mem_soCent.2 ⟨fun _ _ => by simp, by simp⟩
    have hmem := sumEnd_mem_soCent horth hc hEA hEB hM0 h0
    obtain ⟨Z, hZs, hZ⟩ := exists_mem_soSub_adV_eq hQ _ (mem_soCent.1 hmem).1
    have hZ' : Z ∈ lieCentralizer (soSub Q) Xc := mem_lieCentralizer.mpr
      ⟨hZs, (commute_of_adV_commute hQ hZs.1 hXc.1 (by rw [hZ]; exact (mem_soCent.1 hmem).2)).symm⟩
    have h3 := hmin Z hZ'
    have hZA : ∀ a ∈ A, adV Q Z a ∈ A := fun a ha => by
      rw [hZ, show a = ((⟨a, ha⟩ : A) : V) from rfl, sumEnd_left]; exact (M ⟨a, ha⟩).2
    have hcong := soCent_inf_killSub_congr (g := 1 + E) hc hYA hZA fun b hb => by
      rw [hYB b hb, hZ, show b = ((⟨b, hb⟩ : B) : V) from rfl, sumEnd_right]; rfl
    have hres : (adV Q Z).restrict hZA = M := by
      ext a
      simp only [LinearMap.coe_restrict_apply, hZ]
      exact sumEnd_left hc M 0 a
    have h1' := key Yc hYc hYA
    have h2' := key Z hZ' hZA
    rw [hres, ← hcong] at h2'
    omega
  obtain ⟨M, hM, hMle⟩ := exists_skew_finrank_soCent_le _ (Q.comp A.subtype) rfl hQA
  have h1 := hle M (mem_soCent.1 hM).1
  have h2 := le_finrank_soCent hQA hNs
  exact le_antisymm (h1.trans hMle) h2

end FactorRegular

/-! ## Conjugating one factor -/

section Factor

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- If `P(g)` conjugates `adV Z` to `adV Z'` (`Z, Z' ∈ so_Cliff(V)`), then `g Z g⁻¹ = Z'`
(`adV_conj`, `adV` injective on `so_Cliff(V)`). -/
theorem conj_eq_of_specP_conj {Q : QuadraticForm K V} (hQ : IsNondeg Q) (g : GSpin Q)
    {Z Z' : CliffordAlgebra Q} (hZ : Z ∈ soSub Q) (hZ' : Z' ∈ soSub Q)
    (h : ∀ v, specP Q g (adV Q Z v) = adV Q Z' (specP Q g v)) :
    ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * Z *
      (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = Z' := by
  refine eq_of_mem_soSub_of_adV_eq hQ (conj_mem_soSub g hZ) hZ' (LinearMap.ext fun v => ?_)
  rw [adV_conj g hZ.1 v, h]
  congr 1
  simp

end Factor

section FactorConj

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
variable {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]

omit [PAdicField F] [FiniteDimensional F W] in
/-- `(N|_U)^n ≠ 0` gives `u ∈ U` with `N^n u ≠ 0`. -/
theorem exists_pow_apply_ne_zero_of_restrict {U : Submodule F W} {N : Module.End F W}
    (hNU : ∀ u ∈ U, N u ∈ U) {n : ℕ} (h : N.restrict hNU ^ n ≠ 0) : ∃ u ∈ U, (N ^ n) u ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  refine LinearMap.ext fun u => Subtype.ext ?_
  rw [Module.End.pow_restrict, LinearMap.restrict_apply]
  exact hc u u.2

/-- **The factor classification**: on a nondegenerate `U ⊆ W` with `W = U ⊥ U^⊥`, two nilpotent
skew `N, N'` preserving `U` with minimal centralizer on `U` (`dim so(U)_{N|_U} = ⌊dim U/2⌋`), and,
when `dim U` is even and `≥ 4`, both in `O_ν(U)`, are conjugate on `U` by some `g ∈ SO(W)` fixing
`U^⊥`.  Odd `dim U`: one Jordan block (`pow_ne_zero_of_finrank_soCent_eq`); even `dim U ≥ 4`:
`IsInOrbitNu`; even `dim U ≤ 2`: `N|_U = N'|_U = 0`. -/
theorem exists_isometry_conj_of_finrank_soCent_eq {Q : QuadraticForm F W} (hQ : IsNondeg Q)
    {U : Submodule F W} (hc : IsCompl U ((bform Q).orthogonal U)) {ν : F} (hν : ν ≠ 0)
    {N N' : Module.End F W} (hN : ∀ u w, bform Q (N u) w = -bform Q u (N w))
    (hN' : ∀ u w, bform Q (N' u) w = -bform Q u (N' w)) (hn : IsNilpotent N)
    (hn' : IsNilpotent N') (hNU : ∀ u ∈ U, N u ∈ U) (hNU' : ∀ u ∈ U, N' u ∈ U)
    (hd : finrank F ↥(soCent (Q.comp U.subtype) (N.restrict hNU)) = finrank F U / 2)
    (hd' : finrank F ↥(soCent (Q.comp U.subtype) (N'.restrict hNU')) = finrank F U / 2)
    (hev : Even (finrank F U) → 4 ≤ finrank F U →
      IsInOrbitNu Q U ν N ∧ IsInOrbitNu Q U ν N') :
    ∃ g : Q.IsometryEquiv Q, LinearMap.det (g.toLinearEquiv : W →ₗ[F] W) = 1 ∧
      (∀ b ∈ (bform Q).orthogonal U, g b = b) ∧ ∀ u ∈ U, g (N u) = N' (g u) := by
  have horth : ∀ a ∈ U, ∀ b ∈ (bform Q).orthogonal U, bform Q a b = 0 := fun a ha b hb => hb a ha
  have hU := isNondeg_comp_subtype_of_isCompl hc
  rcases Nat.even_or_odd (finrank F U) with he | ho
  · by_cases h4 : 4 ≤ finrank F U
    · obtain ⟨h, h'⟩ := hev he h4
      obtain ⟨k, hk⟩ := he
      exact SingleBlock.exists_isometry_det_one_conj_of_isInOrbitNu_sub hQ hc horth (k := k - 1)
        (by omega) hν hN hN' hn hn' h h'
    · have h2 : finrank F U ≤ 2 := by obtain ⟨k, hk⟩ := he; omega
      have h0 := SingleBlock.eq_zero_of_finrank_le_two hU h2 (skew_restrict hN hNU)
        (Module.End.isNilpotent.restrict hNU hn)
      have h0' := SingleBlock.eq_zero_of_finrank_le_two hU h2 (skew_restrict hN' hNU')
        (Module.End.isNilpotent.restrict hNU' hn')
      refine ⟨QuadraticMap.IsometryEquiv.refl Q, ?_, fun b _ => rfl, fun u hu => ?_⟩
      · exact LinearMap.det_id
      · have e1 := congrArg Subtype.val (LinearMap.congr_fun h0 ⟨u, hu⟩)
        have e2 := congrArg Subtype.val (LinearMap.congr_fun h0' ⟨u, hu⟩)
        simp only [LinearMap.restrict_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero] at e1 e2
        change N u = N' u
        rw [e1, e2]
  · obtain ⟨k, hk⟩ := ho
    have hpow : ∀ {M : Module.End F W} (hM : ∀ u w, bform Q (M u) w = -bform Q u (M w))
        (hm : IsNilpotent M) (hMU : ∀ u ∈ U, M u ∈ U),
        finrank F ↥(soCent (Q.comp U.subtype) (M.restrict hMU)) = finrank F U / 2 →
        ∃ u ∈ U, (M ^ (2 * k)) u ≠ 0 := by
      intro M hM hm hMU hdM
      apply exists_pow_apply_ne_zero_of_restrict hMU
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · have : Nontrivial ↥U := Module.nontrivial_of_finrank_pos (R := F) (by omega)
        rw [Nat.mul_zero, pow_zero]
        exact one_ne_zero
      · have := (pow_ne_zero_of_finrank_soCent_eq hU (skew_restrict hM hMU)
          (Module.End.isNilpotent.restrict hMU hm) hdM (by omega)).1 ⟨k, hk⟩
        rwa [show finrank F U - 1 = 2 * k by omega] at this
    exact SingleBlock.exists_isometry_det_one_conj_of_pow_ne_zero_sub hQ hc horth hk hN hN' hn hn'
      hNU hNU' (hpow hN hn hNU hd) (hpow hN' hn' hNU' hd')

end FactorConj

/-! ## Isometries fixing `U^⊥` -/

section FixOrth

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- An isometry fixing `U^⊥` pointwise preserves `U`, when `V = U ⊥ U^⊥` is nondegenerate. -/
theorem isometry_mem_of_fix_orthogonal {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    {U : Submodule K V} (hc : IsCompl U ((bform Q).orthogonal U)) (g : Q.IsometryEquiv Q)
    (hg : ∀ b ∈ (bform Q).orthogonal U, g b = b) {u : V} (hu : u ∈ U) : g u ∈ U := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := g u))
  have hb0 : b = 0 := by
    refine (isNondeg_iff Q).1 hQ b fun v => ?_
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
    have h1 : bform Q b a' = 0 := by rw [bform_comm]; exact hb a' ha'
    have h2 : bform Q (g u) b' = 0 := by
      rw [← hg b' hb']
      exact (bform_isometry g.toIsometry u b').trans (hb' u hu)
    have h3 : bform Q a b' = 0 := hb' a ha
    rw [← hab, map_add, LinearMap.add_apply, h3, zero_add] at h2
    rw [map_add, h1, zero_add, h2]
  rw [← hab, hb0, add_zero]; exact ha

/-- An isometry fixing `U^⊥` pointwise and conjugating `N` to `N'` on `U` conjugates them on all
of `V`, if `N` maps `U^⊥` into itself and `N = N'` there. -/
theorem isometry_conj_of_fix_orthogonal {Q : QuadraticForm K V} {U : Submodule K V}
    (hc : IsCompl U ((bform Q).orthogonal U)) (g : Q.IsometryEquiv Q)
    (hg : ∀ b ∈ (bform Q).orthogonal U, g b = b) {N N' : Module.End K V}
    (hU : ∀ u ∈ U, g (N u) = N' (g u))
    (hB : ∀ b ∈ (bform Q).orthogonal U, N b ∈ (bform Q).orthogonal U ∧ N' b = N b) (v : V) :
    g (N v) = N' (g v) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
  rw [map_add, map_add, map_add, map_add, hU a ha, hg b hb, hg _ (hB b hb).1, (hB b hb).2]

end FixOrth

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

/-! ## R2: regular elements of `𝔤⁰_X` are regular on each factor -/

theorem mem_lieCentralizer_lieZero_iff {a Z : d.ambient} :
    Z ∈ lieCentralizer d.lieZero a ↔
      Z.1 ∈ lieCentralizer (soSub d.QW) a.1 ∧ Z.2 ∈ lieCentralizer (soSub d.QV) a.2 := by
  have hl : ∀ Z : d.ambient, Z ∈ d.lieZero ↔ Z.1 ∈ soSub d.QW ∧ Z.2 ∈ soSub d.QV :=
    fun Z => Iff.rfl
  simp only [mem_lieCentralizer, hl, Prod.ext_iff, Prod.fst_mul, Prod.snd_mul]
  tauto

theorem finrank_le_of_isRegularNil {a Y Y' : d.ambient}
    (hY : IsRegularNil (lieCentralizer d.lieZero a) Y) (hY' : Y' ∈ lieCentralizer d.lieZero a) :
    finrank F ↥(lieCentralizer (lieCentralizer d.lieZero a) Y) ≤
      finrank F ↥(lieCentralizer (lieCentralizer d.lieZero a) Y') := by
  rw [hY.2.2]
  exact ciInf_le (OrderBot.bddBelow _) (⟨Y', hY'⟩ : lieCentralizer d.lieZero a)

/-- **R2 on `W`**: a regular nilpotent `Y ∈ 𝔤⁰_X` has `dim so(W')_{Y|W'} = ⌊dim W'/2⌋`. -/
theorem finrank_soCent_ker_fst_eq {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    {X : CliffordAlgebra d.QW} (hX : d.IsGammaEltLie (d.torusOf x) X) {Y : d.ambient}
    (hY : IsRegularNil (lieCentralizer d.lieZero (d.diagLie X)) Y)
    (hYA : ∀ a ∈ LinearMap.ker (adV d.QW X), adV d.QW Y.1 a ∈ LinearMap.ker (adV d.QW X)) :
    finrank F ↥(soCent (d.QW.comp (LinearMap.ker (adV d.QW X)).subtype)
        ((adV d.QW Y.1).restrict hYA)) = finrank F ↥(LinearMap.ker (adV d.QW X)) / 2 := by
  have hYm := (d.mem_lieCentralizer_lieZero_iff).1 hY.1
  refine finrank_soCent_ker_eq_of_forall_le d.nondeg hX.1.1 hYm.1 (d.isCompl_ker_adV hx hX)
    (d.adV_fst_eq_zero_of_isNilpotent hx hX hY.1 hY.2.1) (fun Y' hY' => ?_) hYA
  have h := d.finrank_le_of_isRegularNil hY
    ((d.mem_lieCentralizer_lieZero_iff (Z := (Y', Y.2))).2 ⟨hY', hYm.2⟩)
  rw [d.finrank_lieCentralizer_lieCentralizer_lieZero,
    d.finrank_lieCentralizer_lieCentralizer_lieZero] at h
  exact Nat.le_of_add_le_add_right h

/-- **R2 on `V`**: a regular nilpotent `Y ∈ 𝔤⁰_X` has `dim so(V')_{Y|V'} = ⌊dim V'/2⌋`,
`V' = W' ⊕ Z = ker X` on `V`. -/
theorem finrank_soCent_ker_snd_eq {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    {X : CliffordAlgebra d.QW} (hX : d.IsGammaEltLie (d.torusOf x) X) {Y : d.ambient}
    (hY : IsRegularNil (lieCentralizer d.lieZero (d.diagLie X)) Y)
    (hYA : ∀ a ∈ LinearMap.ker (adV d.QV (d.diagLie X).2),
      adV d.QV Y.2 a ∈ LinearMap.ker (adV d.QV (d.diagLie X).2)) :
    finrank F ↥(soCent (d.QV.comp (LinearMap.ker (adV d.QV (d.diagLie X).2)).subtype)
        ((adV d.QV Y.2).restrict hYA)) =
      finrank F ↥(LinearMap.ker (adV d.QV (d.diagLie X).2)) / 2 := by
  have hYm := (d.mem_lieCentralizer_lieZero_iff).1 hY.1
  refine finrank_soCent_ker_eq_of_forall_le d.nondeg_QV (d.diagLie_mem_lieZero hX.1.1).2 hYm.2
    (d.isCompl_ker_adV_snd hx hX) (d.adV_snd_eq_zero_of_isNilpotent hx hX hY.1 hY.2.1)
    (fun Y' hY' => ?_) hYA
  have h := d.finrank_le_of_isRegularNil hY
    ((d.mem_lieCentralizer_lieZero_iff (Z := (Y.1, Y'))).2 ⟨hYm.1, hY'⟩)
  rw [d.finrank_lieCentralizer_lieCentralizer_lieZero,
    d.finrank_lieCentralizer_lieCentralizer_lieZero] at h
  exact Nat.le_of_add_le_add_left h

/-! ## R2′: regularity is a property of the orbit -/

/-- `Z_G(X)` preserves `𝔤⁰_X`. -/
theorem conj_mem_lieCentralizer_lieZero {D : d.ambient} {g : d.ambientˣ}
    (hg : g ∈ lieGrpCentralizer d.G D) {Y : d.ambient} (hY : Y ∈ lieCentralizer d.lieZero D) :
    (g : d.ambient) * Y * (↑g⁻¹ : d.ambient) ∈ lieCentralizer d.lieZero D := by
  obtain ⟨hY0, hDY⟩ := mem_lieCentralizer.mp hY
  have h1 : (g : d.ambient) * D = D * g := hg.2
  have h2 : (↑g⁻¹ : d.ambient) * D = D * ↑g⁻¹ :=
    (Commute.units_inv_left (show Commute (g : d.ambient) D from h1)).eq
  refine mem_lieCentralizer.mpr ⟨d.conj_mem_lie0 ⟨g, hg.1⟩ hY0, ?_⟩
  calc D * ((g : d.ambient) * Y * ↑g⁻¹) = (D * g) * Y * ↑g⁻¹ := by simp only [mul_assoc]
    _ = g * (D * Y) * ↑g⁻¹ := by rw [← h1]; simp only [mul_assoc]
    _ = g * (Y * D) * ↑g⁻¹ := by rw [hDY]
    _ = g * Y * (↑g⁻¹ * D) := by rw [h2]; simp only [mul_assoc]
    _ = (g : d.ambient) * Y * ↑g⁻¹ * D := by simp only [mul_assoc]

/-- **R2′**: every element of a regular nilpotent orbit of `𝔤⁰_X` is regular nilpotent
(`finrank_lieCentralizer_conj`). -/
theorem isRegularNil_of_mem_nilOrbitSet {D : d.ambient}
    {O : NilOrbit (lieGrpCentralizer d.G D) (lieCentralizer d.lieZero D)}
    (hO : O ∈ NilReg _ _) {Y : ↥(lieCentralizer d.lieZero D)} (hY : Y ∈ nilOrbitSet O) :
    IsRegularNil (lieCentralizer d.lieZero D) (Y : d.ambient) := by
  obtain ⟨hn, hYO⟩ := hY
  obtain ⟨g, hg, hgY⟩ := Quotient.exact ((Quotient.out_eq O).trans hYO.symm)
  refine ⟨Y.2, hn, ?_⟩
  rw [← hgY, finrank_lieCentralizer_conj _ g (fun Z hZ => d.conj_mem_lieCentralizer_lieZero hg hZ)
    (fun Z hZ => by
      simpa using d.conj_mem_lieCentralizer_lieZero (Subgroup.inv_mem _ hg) hZ)]
  exact hO.2.2

/-! ## R3: lifting conjugating isometries to `Z_G(X)` -/

/-- **Isometries of determinant `1` of `W` and `V` commuting with `ad X` and conjugating `ad Y` to
`ad Y'` lift to `γ ∈ Z_G(X)` with `γ Y γ⁻¹ = Y'`** (`gspin_specP_surjective_SO` on each factor,
`conj_eq_of_specP_conj`). -/
theorem exists_conj_of_isometries {X : CliffordAlgebra d.QW} (hX : X ∈ soSub d.QW)
    {Y Y' : d.ambient} (hY : Y ∈ d.lieZero) (hY' : Y' ∈ d.lieZero)
    (gW : d.QW.IsometryEquiv d.QW) (gV : d.QV.IsometryEquiv d.QV)
    (hgW1 : LinearMap.det (gW.toLinearEquiv : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) = 1)
    (hgV1 : LinearMap.det (gV.toLinearEquiv : d.V →ₗ[F] d.V) = 1)
    (hgWX : ∀ w, gW (adV d.QW X w) = adV d.QW X (gW w))
    (hgVX : ∀ v, gV (adV d.QV (d.diagLie X).2 v) = adV d.QV (d.diagLie X).2 (gV v))
    (hgWY : ∀ w, gW (adV d.QW Y.1 w) = adV d.QW Y'.1 (gW w))
    (hgVY : ∀ v, gV (adV d.QV Y.2 v) = adV d.QV Y'.2 (gV v)) :
    ∃ γ ∈ lieGrpCentralizer d.G (d.diagLie X),
      ((γ : d.ambientˣ) : d.ambient) * Y * ((γ⁻¹ : d.ambientˣ) : d.ambient) = Y' := by
  obtain ⟨γ₁, h₁⟩ := gspin_specP_surjective_SO d.QW d.nondeg gW.toLinearEquiv
    (fun v => gW.map_app v) hgW1
  obtain ⟨γ₂, h₂⟩ := gspin_specP_surjective_SO d.QV d.nondeg_QV gV.toLinearEquiv
    (fun v => gV.map_app v) hgV1
  set γ : d.G := d.pair (γ₁, γ₂)
  have hXV : (d.diagLie X).2 ∈ soSub d.QV := (d.diagLie_mem_lieZero hX).2
  have hconj : ∀ Z : d.ambient, ((γ : d.ambientˣ) : d.ambient) * Z *
      (((γ : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) =
      (((γ₁ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * Z.1 *
          (((γ₁ : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
        ((γ₂ : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) * Z.2 *
          (((γ₂ : (CliffordAlgebra d.QV)ˣ)⁻¹ : (CliffordAlgebra d.QV)ˣ) :
            CliffordAlgebra d.QV)) := by
    intro Z
    have hi : (γ : d.ambientˣ)⁻¹ = ((d.pair (γ₁⁻¹, γ₂⁻¹) : d.G) : d.ambientˣ) := by
      rw [← Subgroup.coe_inv, ← map_inv]; rfl
    rw [hi]; rfl
  have hD : ((γ : d.ambientˣ) : d.ambient) * d.diagLie X *
      (((γ : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) = d.diagLie X := by
    rw [hconj]
    exact Prod.ext
      (conj_eq_of_specP_conj d.nondeg γ₁ hX hX fun v => by rw [h₁]; exact hgWX v)
      (conj_eq_of_specP_conj d.nondeg_QV γ₂ hXV hXV fun v => by rw [h₂]; exact hgVX v)
  refine ⟨γ, ⟨γ.2, ?_⟩, ?_⟩
  · calc ((γ : d.ambientˣ) : d.ambient) * d.diagLie X =
          ((γ : d.ambientˣ) : d.ambient) * d.diagLie X *
            (((γ : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient) * ((γ : d.ambientˣ) : d.ambient) := by
          simp [mul_assoc]
      _ = d.diagLie X * ((γ : d.ambientˣ) : d.ambient) := by rw [hD]
  · rw [hconj]
    exact Prod.ext
      (conj_eq_of_specP_conj d.nondeg γ₁ hY.1 hY'.1 fun v => by rw [h₁]; exact hgWY v)
      (conj_eq_of_specP_conj d.nondeg_QV γ₂ hY.2 hY'.2 fun v => by rw [h₂]; exact hgVY v)

/-! ## R4: uniqueness of the orbit -/

theorem finrank_prod_top (U : Submodule F (Fin d.m → F)) :
    finrank F ↥(U.prod (⊤ : Submodule F d.Z)) = finrank F U + (2 * d.r + 1) := by
  rw [(Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod, finrank_top,
    Module.finrank_fin_fun]

/-- `ad Y` preserves `ker X` on `W` for `Y ∈ 𝔤⁰_X`. -/
theorem mapsTo_ker_fst {X : CliffordAlgebra d.QW} (hX : X ∈ soSub d.QW) {Y : d.ambient}
    (hY : Y ∈ lieCentralizer d.lieZero (d.diagLie X)) :
    ∀ a ∈ LinearMap.ker (adV d.QW X), adV d.QW Y.1 a ∈ LinearMap.ker (adV d.QW X) := by
  obtain ⟨⟨hY1, -⟩, hYc⟩ := mem_lieCentralizer.mp hY
  have hc := adV_mul_comm_of_mul_comm hY1.1 hX.1 (congrArg Prod.fst hYc)
  intro a ha
  rw [LinearMap.mem_ker] at ha ⊢
  rw [← Module.End.mul_apply, ← hc, Module.End.mul_apply, ha, map_zero]

/-- `ad Y` preserves `ker X` on `V` for `Y ∈ 𝔤⁰_X`. -/
theorem mapsTo_ker_snd {X : CliffordAlgebra d.QW} (hX : X ∈ soSub d.QW) {Y : d.ambient}
    (hY : Y ∈ lieCentralizer d.lieZero (d.diagLie X)) :
    ∀ a ∈ LinearMap.ker (adV d.QV (d.diagLie X).2),
      adV d.QV Y.2 a ∈ LinearMap.ker (adV d.QV (d.diagLie X).2) := by
  obtain ⟨⟨-, hY2⟩, hYc⟩ := mem_lieCentralizer.mp hY
  have hc := adV_mul_comm_of_mul_comm hY2.1 (d.diagLie_mem_lieZero hX).2.1
    (congrArg Prod.snd hYc)
  intro a ha
  rw [LinearMap.mem_ker] at ha ⊢
  rw [← Module.End.mul_apply, ← hc, Module.End.mul_apply, ha, map_zero]

/-- **Two regular nilpotent elements of `𝔤⁰_X` meeting Luo's recipe are `Z_G(X)`-conjugate.** -/
theorem exists_conj_of_orbitSpecAt {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    {X : CliffordAlgebra d.QW} (hX : d.IsGammaEltLie (d.torusOf x) X) {Y Y' : d.ambient}
    (hY : IsRegularNil (lieCentralizer d.lieZero (d.diagLie X)) Y)
    (hY' : IsRegularNil (lieCentralizer d.lieZero (d.diagLie X)) Y')
    (hYs : d.OrbitSpecAt (LinearMap.ker (adV d.QW X)) Y)
    (hY's : d.OrbitSpecAt (LinearMap.ker (adV d.QW X)) Y') :
    ∃ γ ∈ lieGrpCentralizer d.G (d.diagLie X),
      ((γ : d.ambientˣ) : d.ambient) * Y * ((γ⁻¹ : d.ambientˣ) : d.ambient) = Y' := by
  have hX0 : X ∈ soSub d.QW := hX.1.1
  have hXV : (d.diagLie X).2 ∈ soSub d.QV := (d.diagLie_mem_lieZero hX0).2
  have hc := d.isCompl_ker_adV hx hX
  have hcV := d.isCompl_ker_adV_snd hx hX
  obtain ⟨hY1, hY2⟩ := (mem_lieCentralizer.mp hY.1).1
  obtain ⟨hY'1, hY'2⟩ := (mem_lieCentralizer.mp hY'.1).1
  have hn1 : IsNilpotent (adV d.QW Y.1) := isNilpotent_adV hY1.1 (hY.2.1.map (RingHom.fst _ _))
  have hn2 : IsNilpotent (adV d.QV Y.2) := isNilpotent_adV hY2.1 (hY.2.1.map (RingHom.snd _ _))
  have hn'1 : IsNilpotent (adV d.QW Y'.1) :=
    isNilpotent_adV hY'1.1 (hY'.2.1.map (RingHom.fst _ _))
  have hn'2 : IsNilpotent (adV d.QV Y'.2) :=
    isNilpotent_adV hY'2.1 (hY'.2.1.map (RingHom.snd _ _))
  have hA := d.mapsTo_ker_fst hX0 hY.1
  have hA' := d.mapsTo_ker_fst hX0 hY'.1
  have hAV := d.mapsTo_ker_snd hX0 hY.1
  have hAV' := d.mapsTo_ker_snd hX0 hY'.1
  have hfin := d.finrank_prod_top (LinearMap.ker (adV d.QW X))
  -- the factor `W' = ker X`, form `−ν`
  obtain ⟨gW, hgW1, hgWB, hgWU⟩ := exists_isometry_conj_of_finrank_soCent_eq d.nondeg hc
    (neg_ne_zero.2 (Units.ne_zero d.ν)) (bform_adV hY1.1) (bform_adV hY'1.1) hn1 hn'1 hA hA'
    (d.finrank_soCent_ker_fst_eq hx hX hY hA) (d.finrank_soCent_ker_fst_eq hx hX hY' hA')
    fun he h4 => by
      have hnot : ¬ (Even (finrank F ↥((LinearMap.ker (adV d.QW X)).prod
          (⊤ : Submodule F d.Z))) ∧ 4 ≤ finrank F ↥((LinearMap.ker (adV d.QW X)).prod
          (⊤ : Submodule F d.Z))) := fun h => by
        obtain ⟨k, hk⟩ := he
        obtain ⟨j, hj⟩ := h.1
        omega
      unfold OrbitSpecAt at hYs hY's
      simp only [hnot, he, h4, and_self, ↓reduceIte] at hYs hY's
      exact ⟨hYs, hY's⟩
  -- the factor `V' = W' ⊕ Z`, form `ν`
  obtain ⟨gV, hgV1, hgVB, hgVU⟩ := exists_isometry_conj_of_finrank_soCent_eq d.nondeg_QV hcV
    (Units.ne_zero d.ν) (bform_adV hY2.1) (bform_adV hY'2.1) hn2 hn'2 hAV hAV'
    (d.finrank_soCent_ker_snd_eq hx hX hY hAV) (d.finrank_soCent_ker_snd_eq hx hX hY' hAV')
    fun he h4 => by
      rw [d.ker_adV_diagLie_snd hX0] at he h4 ⊢
      unfold OrbitSpecAt at hYs hY's
      simp only [he, h4, and_self, ↓reduceIte] at hYs hY's
      exact ⟨hYs, hY's⟩
  have hB1 := d.adV_fst_eq_zero_of_isNilpotent hx hX hY.1 hY.2.1
  have hB1' := d.adV_fst_eq_zero_of_isNilpotent hx hX hY'.1 hY'.2.1
  have hB2 := d.adV_snd_eq_zero_of_isNilpotent hx hX hY.1 hY.2.1
  have hB2' := d.adV_snd_eq_zero_of_isNilpotent hx hX hY'.1 hY'.2.1
  have hXB : ∀ b ∈ (bform d.QW).orthogonal (LinearMap.ker (adV d.QW X)),
      adV d.QW X b ∈ (bform d.QW).orthogonal (LinearMap.ker (adV d.QW X)) :=
    fun b hb => mapsTo_orthogonal_of_skew (bform_adV hX0.1)
      (fun a ha => by simp only [SetLike.mem_coe, LinearMap.mem_ker] at ha ⊢; rw [ha, map_zero])
      hb
  have hXVB : ∀ b ∈ (bform d.QV).orthogonal (LinearMap.ker (adV d.QV (d.diagLie X).2)),
      adV d.QV (d.diagLie X).2 b ∈
        (bform d.QV).orthogonal (LinearMap.ker (adV d.QV (d.diagLie X).2)) :=
    fun b hb => mapsTo_orthogonal_of_skew (bform_adV hXV.1)
      (fun a ha => by simp only [SetLike.mem_coe, LinearMap.mem_ker] at ha ⊢; rw [ha, map_zero])
      hb
  refine d.exists_conj_of_isometries hX0 hY.1.1 hY'.1.1 gW gV hgW1 hgV1 ?_ ?_ ?_ ?_
  · refine isometry_conj_of_fix_orthogonal hc gW hgWB (fun u hu => ?_) fun b hb => ⟨hXB b hb, rfl⟩
    rw [LinearMap.mem_ker.mp hu, map_zero,
      LinearMap.mem_ker.mp (isometry_mem_of_fix_orthogonal d.nondeg hc gW hgWB hu)]
  · refine isometry_conj_of_fix_orthogonal hcV gV hgVB (fun u hu => ?_) fun b hb => ⟨hXVB b hb, rfl⟩
    rw [LinearMap.mem_ker.mp hu, map_zero,
      LinearMap.mem_ker.mp (isometry_mem_of_fix_orthogonal d.nondeg_QV hcV gV hgVB hu)]
  · exact isometry_conj_of_fix_orthogonal hc gW hgWB hgWU fun b hb => by
      rw [hB1 b hb, hB1' b hb]; exact ⟨zero_mem _, rfl⟩
  · exact isometry_conj_of_fix_orthogonal hcV gV hgVB hgVU fun b hb => by
      rw [hB2 b hb, hB2' b hb]; exact ⟨zero_mem _, rfl⟩

/-- **At most one regular nilpotent orbit of `𝔤⁰_X` meets Luo's recipe** (Luo §7.1;
Waldspurger 2010 §7.1), for `X ∈ 𝔱⁰_♮`: two regular nilpotent orbits of `Z_G(X)` on `𝔤⁰_X`
containing elements `Y`, `Y'` with `OrbitSpecAt (ker X)` coincide (`exists_conj_of_orbitSpecAt`).
This is the hypothesis `horb` of `cTheta_toSO_of_transport`. -/
theorem orbitSpecAt_orbit_unique (T : d.GammaTorus) {X : CliffordAlgebra d.QW}
    (hX : d.IsGammaEltLie T.1 X) :
    ∀ O O' : NilOrbit (lieGrpCentralizer d.G (d.diagLie X))
        (lieCentralizer d.lieZero (d.diagLie X)), O ∈ NilReg _ _ → O' ∈ NilReg _ _ →
      (∃ Y ∈ nilOrbitSet O, d.OrbitSpecAt (LinearMap.ker (adV d.QW X)) (Y : d.ambient)) →
      (∃ Y ∈ nilOrbitSet O', d.OrbitSpecAt (LinearMap.ker (adV d.QW X)) (Y : d.ambient)) →
      O = O' := by
  obtain ⟨_, x, hx, rfl⟩ := T
  rintro O O' hO hO' ⟨Y, hYO, hYs⟩ ⟨Y', hY'O, hY's⟩
  obtain ⟨γ, hγ, hγY⟩ := d.exists_conj_of_orbitSpecAt hx hX
    (d.isRegularNil_of_mem_nilOrbitSet hO hYO) (d.isRegularNil_of_mem_nilOrbitSet hO' hY'O)
    hYs hY's
  obtain ⟨hn, rfl⟩ := hYO
  obtain ⟨hn', rfl⟩ := hY'O
  exact Quotient.sound ⟨γ, hγ, hγY⟩

end GGPData

end GSpinGGP
