import GSpinGGP.Foundations.HypFrame
import GSpinGGP.Foundations.Determinant
import GSpinGGP.Foundations.IsometryDet
import TauCeti.LinearAlgebra.QuadraticForm.SepClosed

/-!
# Eigen-frames of a semisimple isometry

Let `Q` be a nondegenerate quadratic form on a finite-dimensional space `V` over an algebraically
closed field of characteristic `0`, and `X` a semisimple isometry of `Q` with `det X = 1`. Then `V`
has a hyperbolic frame of eigenvectors of `X` whose orthogonal complement is `ker (X − 1)`:
`X eᵢ = μᵢ eᵢ`, `X fᵢ = μᵢ⁻¹ fᵢ` (`exists_hypFrame_eigen`).

Proof. `R = im (X − 1)` is `X`-stable, nondegenerate, meets `ker (X − 1)` trivially and is its
orthogonal complement. Peel off hyperbolic pairs of eigenvectors from `R`: an eigenvector `u`
for `μ ≠ −1` is isotropic and pairs with an eigenvector for `μ⁻¹`
(`IsomCent.exists_eigen_pair_ne_zero`);
if every eigenvalue on the remaining space `U` is `−1`, then `U ⊆ E₋₁`, which is even-dimensional
(`det X = 1`, `IsomCent.det_eq_det_one_mul_det_neg_one`), and an isotropic vector exists in
dimension `≥ 2` over an algebraically closed field (Tau Ceti's `not_anisotropic_of_isSepClosed`).
-/

noncomputable section

open Module QuadraticMap Module.End

namespace GSpinGGP

namespace IsomCent

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- `U ∩ {u, w}^⊥`. -/
def orthPair (Q : QuadraticForm K V) (U : Submodule K V) (u w : V) : Submodule K V :=
  U ⊓ LinearMap.ker ((polarBilin Q).flip u) ⊓ LinearMap.ker ((polarBilin Q).flip w)

theorem mem_orthPair {Q : QuadraticForm K V} {U : Submodule K V} {u w v : V} :
    v ∈ orthPair Q U u w ↔ v ∈ U ∧ polar Q v u = 0 ∧ polar Q v w = 0 := by
  simp [orthPair, and_assoc]

variable {Q : QuadraticForm K V} {U : Submodule K V} {u w : V}

/-- `U = (U ∩ {u, w}^⊥) + span {u, w}` for a hyperbolic pair `u, w ∈ U`. -/
theorem sub_mem_orthPair (huu : polar Q u u = 0) (hww : polar Q w w = 0) (huw : polar Q u w = 1)
    (hu : u ∈ U) (hw : w ∈ U) {v : V} (hv : v ∈ U) :
    v - polar Q v w • u - polar Q v u • w ∈ orthPair Q U u w := by
  have hwu : polar Q w u = 1 := by rw [polar_comm, huw]
  refine mem_orthPair.2 ⟨U.sub_mem (U.sub_mem hv (U.smul_mem _ hu)) (U.smul_mem _ hw), ?_, ?_⟩ <;>
    simp [polar_sub_left, polar_smul_left, huu, hww, huw, hwu]

/-- `dim (U ∩ {u, w}^⊥) + 2 = dim U` for a hyperbolic pair `u, w ∈ U`. -/
theorem finrank_orthPair_add_two [FiniteDimensional K V] (huu : polar Q u u = 0)
    (hww : polar Q w w = 0) (huw : polar Q u w = 1) (hu : u ∈ U) (hw : w ∈ U) :
    finrank K (orthPair Q U u w) + 2 = finrank K U := by
  have hwu : polar Q w u = 1 := by rw [polar_comm, huw]
  have hli : LinearIndependent K ![u, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun z => polar Q z u) hst
    have h2 := congrArg (fun z => polar Q z w) hst
    simp only [polar_add_left, polar_smul_left, huu, hwu, hww, huw, polar_zero_left,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at h1 h2
    exact ⟨h2, h1⟩
  have hspan : finrank K (Submodule.span K {u, w}) = 2 := by
    rw [← Matrix.range_cons_cons_empty u w ![], finrank_span_eq_card hli]
    simp
  have hsup : orthPair Q U u w ⊔ Submodule.span K {u, w} = U := by
    refine le_antisymm (sup_le (fun v hv => (mem_orthPair.1 hv).1) (Submodule.span_le.2 ?_))
      fun v hv => ?_
    · rintro x (rfl | rfl | _)
      · exact hu
      · exact hw
    · rw [Submodule.mem_sup]
      exact ⟨_, sub_mem_orthPair huu hww huw hu hw hv, polar Q v w • u + polar Q v u • w,
        Submodule.mem_span_pair.2 ⟨_, _, rfl⟩, by abel⟩
  have hinf : orthPair Q U u w ⊓ Submodule.span K {u, w} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx2
    obtain ⟨-, h1, h2⟩ := mem_orthPair.1 hx1
    simp only [polar_add_left, polar_smul_left, huu, hww, huw, hwu, smul_eq_mul, mul_one,
      mul_zero, add_zero, zero_add] at h1 h2
    simp [h1, h2]
  have := Submodule.finrank_sup_add_finrank_inf_eq (orthPair Q U u w) (Submodule.span K {u, w})
  rw [hsup, hinf, finrank_bot, hspan] at this
  omega

section Frame

variable [CharZero K] [IsAlgClosed K] [FiniteDimensional K V] [Invertible (2 : K)]
  {X : Module.End K V}

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K V] [Invertible (2 : K)] in
theorem polar_eq_zero_of_eigen (hX : (polarBilin Q).IsOrthogonal X) {μ ν : K}
    (hμν : μ * ν ≠ 1) {a b : V}
    (ha : X a = μ • a) (hb : X b = ν • b) : polar Q a b = 0 :=
  bform_eigen_eq_zero (B := polarBilin Q) hX hμν (mem_eigenspace_iff.2 ha) (mem_eigenspace_iff.2 hb)

/-- The inductive step: a hyperbolic frame of eigenvectors of `X` spanning an `X`-stable
nondegenerate subspace `U` without fixed vectors and with `dim (U ∩ E₋₁)` even. -/
theorem exists_frame_aux (hQ : (polarBilin Q).Nondegenerate) (hX : (polarBilin Q).IsOrthogonal X)
    (hss : X.IsSemisimple) (N : ℕ) : ∀ U : Submodule K V, finrank K U = N → (∀ u ∈ U, X u ∈ U) →
      (∀ u ∈ U, (∀ u' ∈ U, polar Q u u' = 0) → u = 0) → (∀ u ∈ U, X u = u → u = 0) →
      Even (finrank K ↥(U ⊓ X.eigenspace (-1))) →
      ∃ (n : ℕ) (e f : Fin n → V) (μ : Fin n → Kˣ),
        (∀ i j, polar Q (e i) (e j) = 0) ∧ (∀ i j, polar Q (f i) (f j) = 0) ∧
        (∀ i j, polar Q (e i) (f j) = if i = j then 1 else 0) ∧
        (∀ i, e i ∈ U ∧ f i ∈ U) ∧ U ≤ IsHypFrame.span K e f ∧
        ∀ i, X (e i) = (μ i : K) • e i ∧ X (f i) = (((μ i)⁻¹ : Kˣ) : K) • f i := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro U hN hU hnd h1 hev
  have hpX : ∀ a b, polar Q (X a) (X b) = polar Q a b := fun a b => hX a b
  by_cases hbot : U = ⊥
  · subst hbot
    exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0, bot_le, fun i => i.elim0⟩
  -- the step, given a hyperbolic pair of eigenvectors in `U`
  have step : ∀ (u w : V) (μ : Kˣ), u ∈ U → w ∈ U → polar Q u u = 0 → polar Q w w = 0 →
      polar Q u w = 1 → X u = (μ : K) • u → X w = ((μ⁻¹ : Kˣ) : K) • w →
      Even (finrank K ↥(orthPair Q U u w ⊓ X.eigenspace (-1))) →
      ∃ (n : ℕ) (e f : Fin n → V) (μ : Fin n → Kˣ),
        (∀ i j, polar Q (e i) (e j) = 0) ∧ (∀ i j, polar Q (f i) (f j) = 0) ∧
        (∀ i j, polar Q (e i) (f j) = if i = j then 1 else 0) ∧
        (∀ i, e i ∈ U ∧ f i ∈ U) ∧ U ≤ IsHypFrame.span K e f ∧
        ∀ i, X (e i) = (μ i : K) • e i ∧ X (f i) = (((μ i)⁻¹ : Kˣ) : K) • f i := by
    intro u w μ hu hw huu hww huw hXu hXw hev₁
    have hwu : polar Q w u = 1 := by rw [polar_comm, huw]
    have hlt : finrank K (orthPair Q U u w) < N := by
      have := finrank_orthPair_add_two huu hww huw hu hw; omega
    have hU₁X : ∀ v ∈ orthPair Q U u w, X v ∈ orthPair Q U u w := by
      intro v hv
      obtain ⟨hvU, hvu, hvw⟩ := mem_orthPair.1 hv
      refine mem_orthPair.2 ⟨hU v hvU, ?_, ?_⟩
      · have h := hpX v u
        rw [hXu, polar_smul_right, hvu, smul_eq_mul] at h
        exact (mul_eq_zero.1 h).resolve_left (Units.ne_zero μ)
      · have h := hpX v w
        rw [hXw, polar_smul_right, hvw, smul_eq_mul] at h
        exact (mul_eq_zero.1 h).resolve_left (Units.ne_zero _)
    have hnd₁ : ∀ v ∈ orthPair Q U u w, (∀ v' ∈ orthPair Q U u w, polar Q v v' = 0) → v = 0 := by
      intro v hv hv0
      obtain ⟨hvU, hvu, hvw⟩ := mem_orthPair.1 hv
      refine hnd v hvU fun z hz => ?_
      have := hv0 _ (sub_mem_orthPair huu hww huw hu hw hz)
      simpa [polar_sub_right, polar_smul_right, hvu, hvw] using this
    have h1₁ : ∀ v ∈ orthPair Q U u w, X v = v → v = 0 := fun v hv => h1 v (mem_orthPair.1 hv).1
    obtain ⟨m, e, f, ν, hee, hff, hef, hmem, hspan, hXef⟩ :=
      ih _ hlt (orthPair Q U u w) rfl hU₁X hnd₁ h1₁ hev₁
    have hp : ∀ i, polar Q (e i) u = 0 ∧ polar Q (e i) w = 0 ∧ polar Q (f i) u = 0 ∧
        polar Q (f i) w = 0 := fun i =>
      ⟨(mem_orthPair.1 (hmem i).1).2.1, (mem_orthPair.1 (hmem i).1).2.2,
        (mem_orthPair.1 (hmem i).2).2.1, (mem_orthPair.1 (hmem i).2).2.2⟩
    have hp' : ∀ i, polar Q u (e i) = 0 ∧ polar Q w (e i) = 0 ∧ polar Q u (f i) = 0 ∧
        polar Q w (f i) = 0 := fun i => by
      simp only [polar_comm Q u, polar_comm Q w]; exact hp i
    refine ⟨m + 1, Fin.cons u e, Fin.cons w f, Fin.cons μ ν, fun i j => ?_, fun i j => ?_,
      fun i j => ?_, fun i => ?_, fun v hv => ?_, fun i => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [huu, hee, (hp _).1, (hp' _).1]
    · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [hww, hff, (hp _).2.2.2, (hp' _).2.2.2]
    · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [huw, hef, (hp _).2.1, (hp' _).2.2.1, Fin.succ_ne_zero, eq_comm (a := (0 : Fin _))]
    · refine Fin.cases ⟨hu, hw⟩ (fun i => ?_) i
      exact ⟨(mem_orthPair.1 (hmem i).1).1, (mem_orthPair.1 (hmem i).2).1⟩
    · have hmono : IsHypFrame.span K e f ≤ IsHypFrame.span K (Fin.cons u e) (Fin.cons w f) := by
        refine Submodule.span_mono ?_
        rintro _ ⟨i | i, rfl⟩
        · exact ⟨Sum.inl i.succ, by simp⟩
        · exact ⟨Sum.inr i.succ, by simp⟩
      have hu' : u ∈ IsHypFrame.span K (Fin.cons u e) (Fin.cons w f) :=
        Submodule.subset_span ⟨Sum.inl 0, by simp⟩
      have hw' : w ∈ IsHypFrame.span K (Fin.cons u e) (Fin.cons w f) :=
        Submodule.subset_span ⟨Sum.inr 0, by simp⟩
      have h := Submodule.add_mem _ (Submodule.add_mem _
        (hmono (hspan (sub_mem_orthPair huu hww huw hu hw hv)))
        (Submodule.smul_mem _ (polar Q v w) hu')) (Submodule.smul_mem _ (polar Q v u) hw')
      convert h using 1
      abel
    · refine Fin.cases ⟨?_, ?_⟩ (fun i => ?_) i
      · simpa using hXu
      · simpa using hXw
      · simpa using hXef i
  have hinj : Function.Injective X := LinearMap.IsOrthogonal.injective hQ hX
  have hinv : U ∈ X.invtSubmodule := (mem_invtSubmodule X).2 hU
  set X' : Module.End K U := X.restrict hinv with hX'
  have hss' : X'.IsSemisimple := Module.End.IsSemisimple.restrict hinv hss
  have hX'apply : ∀ v : U, (X' v : V) = X v := fun v => rfl
  have hmemE : ∀ (v : U) (c : K), v ∈ X'.eigenspace c ↔ X v = c • (v : V) := fun v c => by
    rw [mem_eigenspace_iff, Subtype.ext_iff, hX'apply, Submodule.coe_smul]
  by_cases hA : ∃ v ∈ U, v ≠ 0 ∧ ∃ μ : K, μ ≠ -1 ∧ X v = μ • v
  · obtain ⟨v, hvU, hv0, μ, hμ, hXv⟩ := hA
    have hμ1 : μ ≠ 1 := fun h => hv0 (h1 v hvU (by rw [hXv, h, one_smul]))
    have hμ0 : μ ≠ 0 := fun h => hv0 (hinj (by rw [hXv, h, zero_smul, map_zero]))
    have hμμ : ∀ ν : K, ν ≠ 1 → ν ≠ -1 → ν * ν ≠ 1 := fun ν h1 h2 h => by
      have : (ν - 1) * (ν + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h0 | h0
      · exact h1 (by linear_combination h0)
      · exact h2 (by linear_combination h0)
    have huu : polar Q v v = 0 := polar_eq_zero_of_eigen hX (hμμ μ hμ1 hμ) hXv hXv
    -- a partner in `E_{μ⁻¹} ∩ U`
    have hnd' : ((polarBilin Q).domRestrict₁₂ U U).Nondegenerate := by
      refine ⟨fun x hx => Subtype.ext (hnd x x.2 fun y hy => hx ⟨y, hy⟩), fun x hx =>
        Subtype.ext (hnd x x.2 fun y hy => ?_)⟩
      rw [polar_comm]; exact hx ⟨y, hy⟩
    have hX'i : LinearMap.IsOrthogonal ((polarBilin Q).domRestrict₁₂ U U) X' := fun a b => hX a b
    obtain ⟨w', hw'E, hw'0⟩ := exists_eigen_pair_ne_zero hnd' hX'i hss'
      ((hmemE ⟨v, hvU⟩ μ).2 hXv) (fun h => hv0 (congrArg Subtype.val h))
    have hXw' : X w' = μ⁻¹ • (w' : V) := (hmemE w' _).1 hw'E
    set c := polar Q v w' with hc
    have hc0 : c ≠ 0 := hw'0
    set w := c⁻¹ • (w' : V) with hw
    have hXw : X w = μ⁻¹ • w := by rw [hw, map_smul, hXw', smul_comm]
    have hμ'1 : μ⁻¹ ≠ 1 := by rwa [ne_eq, inv_eq_one]
    have hμ'm : μ⁻¹ ≠ -1 := fun h => hμ (by rw [← inv_inv μ, h, inv_neg, inv_one])
    have hww : polar Q w w = 0 := polar_eq_zero_of_eigen hX (hμμ _ hμ'1 hμ'm) hXw hXw
    have huw : polar Q v w = 1 := by
      rw [hw, polar_smul_right, smul_eq_mul, ← hc, inv_mul_cancel₀ hc0]
    have heq : orthPair Q U v w ⊓ X.eigenspace (-1) = U ⊓ X.eigenspace (-1) := by
      ext z
      simp only [Submodule.mem_inf, mem_orthPair, mem_eigenspace_iff]
      constructor
      · rintro ⟨⟨hz, -, -⟩, hzE⟩; exact ⟨hz, hzE⟩
      · rintro ⟨hz, hzE⟩
        refine ⟨⟨hz, polar_eq_zero_of_eigen hX ?_ hzE hXv,
          polar_eq_zero_of_eigen hX ?_ hzE hXw⟩, hzE⟩
        · intro h; exact hμ (by linear_combination -h)
        · intro h; exact hμ'm (by linear_combination -h)
    refine step v w (Units.mk0 μ hμ0) hvU (U.smul_mem _ w'.2) huu hww huw hXv
      (by simpa using hXw) ?_
    rw [heq]
    exact hev
  -- otherwise `X = −1` on `U`
  push Not at hA
  have hall : ∀ v ∈ U, X v = -v := by
    intro v hv
    have htop : (⟨v, hv⟩ : U) ∈ ⨆ ν, X'.eigenspace ν := by
      rw [hss'.iSup_eigenspace_eq_top]; trivial
    have hle : ⨆ ν, X'.eigenspace ν ≤ X'.eigenspace (-1) := iSup_le fun ν => by
      by_cases hν : ν = -1
      · rw [hν]
      intro y hy
      have : (y : V) = 0 := by
        by_contra hy0
        exact hA y y.2 hy0 ν hν ((hmemE y ν).1 hy) |>.elim
      rw [show y = 0 from Subtype.ext this]
      exact Submodule.zero_mem _
    have := (hmemE _ _).1 (hle htop)
    simpa using this
  have hUE : U ≤ X.eigenspace (-1) := fun v hv => by
    rw [mem_eigenspace_iff, hall v hv, neg_one_smul]
  rw [inf_eq_left.2 hUE] at hev
  have h2 : 2 ≤ finrank K U := by
    have hpos : finrank K U ≠ 0 := fun h => hbot (Submodule.finrank_eq_zero.1 h)
    obtain ⟨k, hk⟩ := hev
    omega
  obtain ⟨x, hxQ, hx0⟩ : ∃ x : U, Q x = 0 ∧ x ≠ 0 := by
    have := QuadraticForm.not_anisotropic_of_isSepClosed (Q.restrict U) h2
    simp only [QuadraticMap.Anisotropic, not_forall] at this
    obtain ⟨x, hx, hx0⟩ := this
    exact ⟨x, hx, hx0⟩
  have hu : (x : V) ∈ U := x.2
  have hu0 : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have huu : polar Q x x = 0 := by rw [polar_self, hxQ, smul_zero]
  obtain ⟨w', hw'U, hw'⟩ : ∃ w' ∈ U, polar Q x w' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (hnd x hu hcon)
  set w'' := (polar Q x w')⁻¹ • w' with hw''
  have hw''U : w'' ∈ U := U.smul_mem _ hw'U
  have hw''u : polar Q x w'' = 1 := by
    rw [hw'', polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hw']
  clear_value w''
  set w := w'' - Q w'' • (x : V) with hw
  have hwU : w ∈ U := U.sub_mem hw''U (U.smul_mem _ hu)
  have huw : polar Q x w = 1 := by
    rw [hw, polar_sub_right, polar_smul_right, hw''u, huu, smul_zero, sub_zero]
  have hww : polar Q w w = 0 := by
    have hs := polar_self Q w''
    rw [nsmul_eq_mul, Nat.cast_ofNat] at hs
    have hc : polar Q w'' x = 1 := by rw [polar_comm, hw''u]
    rw [hw, polar_sub_left, polar_sub_right, polar_sub_right, polar_smul_left, polar_smul_left,
      polar_smul_right, polar_smul_right, hs, hc, hw''u, huu]
    simp only [smul_eq_mul]
    ring
  refine step x w (-1) hu hwU huu hww huw ?_ ?_ ?_
  · rw [hall _ hu]; simp
  · rw [hall _ hwU]; simp
  · have hle : orthPair Q U x w ≤ X.eigenspace (-1) := fun v hv => hUE (mem_orthPair.1 hv).1
    rw [inf_eq_left.2 hle]
    have := finrank_orthPair_add_two huu hww huw hu hwU
    obtain ⟨k, hk⟩ := hev
    exact ⟨k - 1, by omega⟩

/-- **Eigen-frames**: a semisimple isometry `X` with `det X = 1` of a nondegenerate quadratic
space over an algebraically closed field of characteristic `0` has a hyperbolic frame of
eigenvectors, `X eᵢ = μᵢ eᵢ`, `X fᵢ = μᵢ⁻¹ fᵢ`, with orthogonal complement `ker (X − 1)`. -/
theorem exists_hypFrame_eigen (hQ : (polarBilin Q).Nondegenerate)
    (hX : (polarBilin Q).IsOrthogonal X)
    (hss : X.IsSemisimple) (hdet : LinearMap.det X = 1) :
    ∃ (n : ℕ) (e f : Fin n → V) (μ : Fin n → Kˣ), IsHypFrame Q (X.eigenspace 1) e f ∧
      ∀ i, X (e i) = (μ i : K) • e i ∧ X (f i) = (((μ i)⁻¹ : Kˣ) : K) • f i := by
  have hpX : ∀ a b, polar Q (X a) (X b) = polar Q a b := fun a b => hX a b
  have hinj : Function.Injective X := LinearMap.IsOrthogonal.injective hQ hX
  have hE1 : ∀ v, v ∈ X.eigenspace 1 ↔ X v = v := fun v => by rw [mem_eigenspace_iff, one_smul]
  set R := LinearMap.range (X - 1) with hR
  have hcompl : IsCompl (X.eigenspace 1) R := by
    have hss1 : (X - 1).IsSemisimple := by
      have := (Module.End.isSemisimple_sub_algebraMap_iff (μ := (1 : K))).2 hss
      simpa using this
    have h := isCompl_ker_range_of_isSemisimple hss1
    have hk : LinearMap.ker (X - 1) = X.eigenspace 1 := by
      ext v; rw [LinearMap.mem_ker, hE1, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    rwa [hk] at h
  have hperp : ∀ v ∈ X.eigenspace 1, ∀ r ∈ R, polar Q v r = 0 := by
    rintro v hv _ ⟨y, rfl⟩
    have h := hpX v y
    rw [(hE1 v).1 hv] at h
    rw [LinearMap.sub_apply, Module.End.one_apply, polar_sub_right, h, sub_self]
  have hRX : ∀ r ∈ R, X r ∈ R := by
    rintro _ ⟨y, rfl⟩
    exact ⟨X y, by simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]⟩
  have hRnd : ∀ v ∈ R, (∀ v' ∈ R, polar Q v v' = 0) → v = 0 := by
    intro v hv hv0
    refine hQ.1 v fun z => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hcompl.sup_eq_top ▸ Submodule.mem_top :
      z ∈ X.eigenspace 1 ⊔ R)
    rw [polarBilin_apply_apply, polar_add_right, polar_comm, hperp a ha v hv, hv0 b hb, add_zero]
  have hR1 : ∀ v ∈ R, X v = v → v = 0 := fun v hv h =>
    Submodule.disjoint_def.1 hcompl.disjoint v ((hE1 v).2 h) hv
  -- `E₋₁ ⊆ R` is even-dimensional
  have hEm : R ⊓ X.eigenspace (-1) = X.eigenspace (-1) := by
    refine inf_eq_right.2 fun v hv => ⟨-(2 : K)⁻¹ • v, ?_⟩
    rw [mem_eigenspace_iff] at hv
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_smul, hv, neg_one_smul]
    module
  have hevEm : Even (finrank K (X.eigenspace (-1))) := by
    have hB : LinearMap.BilinForm.IsSymm (polarBilin Q) := ⟨fun u v => polar_comm Q u v⟩
    have h := det_eq_det_one_mul_det_neg_one hB hQ hX hss hX (Commute.refl X)
    have hid : X.restrict (mapsTo_eigenspace_of_commute (Commute.refl X) 1) = LinearMap.id :=
      LinearMap.ext fun v => Subtype.ext (by simpa using mem_eigenspace_iff.1 v.2)
    have hneg : X.restrict (mapsTo_eigenspace_of_commute (Commute.refl X) (-1)) =
        (-1 : K) • LinearMap.id :=
      LinearMap.ext fun v => Subtype.ext (by simpa using mem_eigenspace_iff.1 v.2)
    rw [hid, hneg, LinearMap.det_id, LinearMap.det_smul, LinearMap.det_id, hdet, one_mul,
      mul_one] at h
    exact (neg_one_pow_eq_one_iff_even (by norm_num)).1 h.symm
  obtain ⟨n, e, f, μ, hee, hff, hef, hmem, hspan, hXef⟩ :=
    exists_frame_aux hQ hX hss _ R rfl hRX hRnd hR1 (by rw [hEm]; exact hevEm)
  refine ⟨n, e, f, μ, ⟨hee, hff, hef, fun v => ⟨fun hv i =>
    ⟨hperp v hv _ (hmem i).1, hperp v hv _ (hmem i).2⟩, fun hv => ?_⟩⟩, hXef⟩
  -- `v ⊥ e, f`, hence `v ⊥ R = im (X − 1)`, hence `X v = v`
  have hvR : ∀ r ∈ R, polar Q v r = 0 := by
    have : IsHypFrame.span K e f ≤ LinearMap.ker (polarBilin Q v) := Submodule.span_le.2 (by
      rintro _ ⟨i | i, rfl⟩
      · exact LinearMap.mem_ker.2 (hv i).1
      · exact LinearMap.mem_ker.2 (hv i).2)
    exact fun r hr => this (hspan hr)
  rw [hE1, ← sub_eq_zero]
  refine hQ.1 _ fun z => ?_
  obtain ⟨y, rfl⟩ := (LinearMap.injective_iff_surjective.1 hinj) z
  rw [polarBilin_apply_apply, polar_sub_left, hpX]
  have := hvR _ ⟨y, rfl⟩
  rw [LinearMap.sub_apply, Module.End.one_apply, polar_sub_right] at this
  linear_combination -this

end Frame

end IsomCent

end GSpinGGP
