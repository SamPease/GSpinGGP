/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.CentralizerSign
import GSpinGGP.GGP.LeviSubgroup
import GSpinGGP.GGP.CentralizerBaseChange
import GSpinGGP.GGP.TorusCentral

/-!
# Centralizers of regular semisimple elements of `GSpin(V)`

For `x ∈ GSpin(V)` regular semisimple (`x` semisimple on `C(V)` and `gspin(V)_x` abelian), the
centralizer `GSpin(V)_x` is a maximal torus; in particular it is commutative
(`commute_of_isRegular`; over `K̄`, `Steinberg.commute_of_forall_skew_commute`, with the plane
lemmas `exists_hypPair_of_finrank_eq_two`, `exists_smul_of_det_restrict_eq_one`).  From this: if moreover `x` lies in the Levi subgroup
`M_F = flagLevi b wt` of a flag stabilizer, then `GSpin(V)_x ⊆ M_F`
(`mem_flagLevi_of_commute_of_isRegular`; Waldspurger, Compos. Math. 146 (2010), §2.3,
`G_x = M_x ⊂ M`; Beuzart-Plessis, Astérisque 418, §1.10; Waldspurger's `G_x` is the neutral
component `Z_G(x)⁰`, which is the full centralizer here: centralizers of semisimple elements of
`GSpin` are connected, by Steinberg's theorem, as `Spin` is simply connected).  The argument for
the inclusion: a lift `T ∈ GSpin(V)` of the cocharacter `λ(2) : bᵢ ↦ 2^{wtᵢ} bᵢ`
(`IsFlagSplitting.exists_cochar_lift`) satisfies `T x T⁻¹ = ±x` (`P(T)` commutes with `P(x)`,
`CentralizerSign.exists_conj_eq_smul`), so
`T²` lies in `GSpin(V)_x`; every `g ∈ GSpin(V)_x` commutes with `T²`, so `P(g)` commutes with
`λ(4)`, whose eigenvalues `4^w` separate the weights; hence `P(g)` preserves each weight space.
-/

noncomputable section

open CliffordAlgebra Module
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

section Plane

variable {L : Type*} [Field L] [Invertible (2 : L)]
  {V : Type*} [AddCommGroup V] [Module L V] {Q : QuadraticForm L V}

open QuadraticMap

/-- **A hyperbolic pair in a nondegenerate plane** over an algebraically closed field of
characteristic `0` (`IsomCent.exists_frame_aux` for `X = −1`). -/
theorem exists_hypPair_of_finrank_eq_two [CharZero L] [IsAlgClosed L] [FiniteDimensional L V]
    (hQ : (polarBilin Q).Nondegenerate) {W : Submodule L V} (hW : finrank L W = 2)
    (hnd : ∀ u ∈ W, (∀ u' ∈ W, polar Q u u' = 0) → u = 0) :
    ∃ e ∈ W, ∃ f ∈ W, polar Q e e = 0 ∧ polar Q f f = 0 ∧ polar Q e f = 1 := by
  have hX : (polarBilin Q).IsOrthogonal (-LinearMap.id : Module.End L V) := fun a b => by
    simp
  have hss : Module.End.IsSemisimple (-LinearMap.id : Module.End L V) :=
    Module.End.isSemisimple_neg.2 Module.End.isSemisimple_id
  have hE : Module.End.eigenspace (-LinearMap.id : Module.End L V) (-1) = ⊤ := by
    ext v; simp
  obtain ⟨n, e, f, -, hee, hff, hef, hmem, hspan, -⟩ := IsomCent.exists_frame_aux hQ hX hss 2 W hW
    (fun u hu => by simpa using W.neg_mem hu) hnd
    (fun u _ h => by
      have h2 : (2 : L) • u = 0 := by
        rw [two_smul]; nth_rewrite 1 [← h]; simp
      exact (smul_eq_zero.1 h2).resolve_left two_ne_zero)
    (by rw [hE, inf_top_eq, hW]; exact even_two)
  have hn : n ≠ 0 := by
    rintro rfl
    have hb : W = ⊥ := le_bot_iff.1 (hspan.trans (by simp [IsHypFrame.span]))
    rw [hb, finrank_bot] at hW
    exact absurd hW (by norm_num)
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  exact ⟨e i, (hmem i).1, f i, (hmem i).2, hee i i, hff i i, by simpa using hef i i⟩

omit [Invertible (2 : L)] in
/-- A hyperbolic pair `e, f` of a plane `W` is a basis of `W`. -/
theorem exists_basis_of_hypPair {W : Submodule L V} (hW2 : finrank L W = 2) {e f : V} (he : e ∈ W)
    (hf : f ∈ W) (hee : polar Q e e = 0) (hff : polar Q f f = 0) (hef : polar Q e f = 1) :
    ∃ bW : Basis (Fin 2) L W, (bW 0 : V) = e ∧ (bW 1 : V) = f := by
  have hfe : polar Q f e = 1 := by rw [polar_comm, hef]
  let v : Fin 2 → W := ![⟨e, he⟩, ⟨f, hf⟩]
  have hli : LinearIndependent L v := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h := congrArg Subtype.val hst
    simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero] at h
    have h1 := congrArg (fun z => polar Q z f) h
    have h2 := congrArg (fun z => polar Q z e) h
    simp only [polar_add_left, polar_smul_left, hef, hff, hfe, hee, polar_zero_left,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at h1 h2
    exact ⟨h1, h2⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [hW2]), ?_, ?_⟩ <;>
    simp [v, coe_basisOfLinearIndependentOfCardEqFinrank]

omit [Invertible (2 : L)] in
/-- A plane `W` with a hyperbolic pair `e, f` is spanned by it. -/
theorem exists_eq_smul_add_smul_of_hypPair {W : Submodule L V} (hW2 : finrank L W = 2) {e f : V}
    (he : e ∈ W) (hf : f ∈ W) (hee : polar Q e e = 0) (hff : polar Q f f = 0)
    (hef : polar Q e f = 1) {w : V} (hw : w ∈ W) : ∃ a b : L, w = a • e + b • f := by
  obtain ⟨bW, hb0, hb1⟩ := exists_basis_of_hypPair hW2 he hf hee hff hef
  refine ⟨bW.repr ⟨w, hw⟩ 0, bW.repr ⟨w, hw⟩ 1, ?_⟩
  have h := congrArg Subtype.val (bW.sum_repr ⟨w, hw⟩)
  simp only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul, hb0, hb1] at h
  exact h.symm

/-- **Isometries of determinant `1` of a hyperbolic plane are diagonal**: if `σ` preserves `polar Q`
and the plane `W ∋ e, f` (`e, f` isotropic, `polar(e, f) = 1`), with `det σ|_W = 1`, then
`σ e = c e` and `σ f = c⁻¹ f`. -/
theorem exists_smul_of_det_restrict_eq_one {σ : Module.End L V}
    (hσ : ∀ a b, polar Q (σ a) (σ b) = polar Q a b) {W : Submodule L V} (hW2 : finrank L W = 2)
    (hW : ∀ w ∈ W, σ w ∈ W) {e f : V} (he : e ∈ W) (hf : f ∈ W) (hee : polar Q e e = 0)
    (hff : polar Q f f = 0) (hef : polar Q e f = 1) (hdet : LinearMap.det (σ.restrict hW) = 1) :
    ∃ c : Lˣ, σ e = (c : L) • e ∧ σ f = ((c⁻¹ : Lˣ) : L) • f := by
  have hfe : polar Q f e = 1 := by rw [polar_comm, hef]
  obtain ⟨bW, hb0, hb1⟩ := exists_basis_of_hypPair hW2 he hf hee hff hef
  have hbW : ∀ i, (bW i : V) = ![e, f] i := fun i => by fin_cases i <;> simp [hb0, hb1]
  -- coordinates of `σ e`, `σ f`
  have hcoord : ∀ w (hw : w ∈ W), w = bW.repr ⟨w, hw⟩ 0 • e + bW.repr ⟨w, hw⟩ 1 • f := by
    intro w hw
    have h := congrArg Subtype.val (bW.sum_repr ⟨w, hw⟩)
    simp only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul, hb0, hb1] at h
    exact h.symm
  set a := bW.repr ⟨σ e, hW e he⟩ 0
  set b := bW.repr ⟨σ e, hW e he⟩ 1
  set c := bW.repr ⟨σ f, hW f hf⟩ 0
  set d := bW.repr ⟨σ f, hW f hf⟩ 1
  have hσe : σ e = a • e + b • f := hcoord _ (hW e he)
  have hσf : σ f = c • e + d • f := hcoord _ (hW f hf)
  -- `det σ|_W = a d − c b`
  have hdet' : a * d - c * b = 1 := by
    rw [← LinearMap.det_toMatrix bW, Matrix.det_fin_two] at hdet
    simp only [LinearMap.toMatrix_apply] at hdet
    have e0 : σ.restrict hW (bW 0) = ⟨σ e, hW e he⟩ :=
      Subtype.ext (by rw [LinearMap.coe_restrict_apply, hbW]; rfl)
    have e1 : σ.restrict hW (bW 1) = ⟨σ f, hW f hf⟩ :=
      Subtype.ext (by rw [LinearMap.coe_restrict_apply, hbW]; rfl)
    rw [e0, e1] at hdet
    exact hdet
  have hab : 2 * (a * b) = 0 := by
    have h := hσ e e
    rw [hσe, hee] at h
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, hee, hff, hef,
      hfe, smul_eq_mul] at h
    linear_combination h
  have hcd : 2 * (c * d) = 0 := by
    have h := hσ f f
    rw [hσf, hff] at h
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, hee, hff, hef,
      hfe, smul_eq_mul] at h
    linear_combination h
  have hp : a * d + b * c = 1 := by
    have h := hσ e f
    rw [hσe, hσf, hef] at h
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, hee, hff, hef,
      hfe, smul_eq_mul] at h
    linear_combination h
  have had : a * d = 1 :=
    mul_left_cancel₀ (Invertible.ne_zero (2 : L)) (by linear_combination hdet' + hp)
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one had
  have hd : d ≠ 0 := right_ne_zero_of_mul_eq_one had
  have hb : b = 0 := by
    have := (mul_eq_zero.1 hab).resolve_left (Invertible.ne_zero 2)
    exact (mul_eq_zero.1 this).resolve_left ha
  have hc : c = 0 := by
    have := (mul_eq_zero.1 hcd).resolve_left (Invertible.ne_zero 2)
    exact (mul_eq_zero.1 this).resolve_right hd
  refine ⟨Units.mk0 a ha, ?_, ?_⟩
  · rw [hσe, hb, zero_smul, add_zero, Units.val_mk0]
  · rw [hσf, hc, zero_smul, zero_add, Units.val_inv_eq_inv_val, Units.val_mk0,
      eq_inv_of_mul_eq_one_right had]

end Plane

namespace Steinberg

variable {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Invertible (2 : L)]
  {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V] {Q : QuadraticForm L V}

open QuadraticMap

/-- **Regular centralizers are commutative**, over an algebraically closed field of
characteristic `0`: if `P(x)` is semisimple and `so(V)_{P(x)}` is abelian, any two elements of
`GSpin(V)` commuting with `x` commute.  `so(V)_{P(x)} ⊇ so(ker (P(x) − 1))` forces
`dim ker (P(x) − 1) ≤ 2` (`IsomCent.finrank_eigenspace_neg_one_le_two` for `−P(x)`).  An element
commuting with `x` has determinant `1` on `ker (P(x) − 1)`
(`det_restrict_one_eq_one_of_commute`): in dimension `≤ 1` it fixes `ker (P(x) − 1)`, and
`commute_of_fixes_eigenspace_one` applies.  In dimension `2`, `ker (P(x) − 1)` is a hyperbolic
plane `⟨e, f⟩` on which `P(g)` acts by `diag(c, c⁻¹)` (`exists_smul_of_det_restrict_eq_one`); with
`s` the pair element of `⟨e, f⟩` acting by `diag(c⁻¹, c)`, `g s` fixes `ker (P(x) − 1)`, so
commutes with `h`, and `s` commutes with `h` (`commute_hypUnit`), hence so does `g`. -/
theorem commute_of_forall_skew_commute (hQ : IsNondeg Q) {x : GSpin Q}
    (hss : Module.End.IsSemisimple (specP Q x : V →ₗ[L] V))
    (hab : ∀ Y₁ Y₂ : Module.End L V, (bform Q).IsSkewAdjoint Y₁ → (bform Q).IsSkewAdjoint Y₂ →
      Commute (specP Q x : V →ₗ[L] V) Y₁ → Commute (specP Q x : V →ₗ[L] V) Y₂ → Commute Y₁ Y₂)
    {g h : GSpin Q} (hg : Commute g x) (hh : Commute h x) : Commute g h := by
  set X : Module.End L V := (specP Q x : V →ₗ[L] V) with hXdef
  have hB : (bform Q).IsSymm := ⟨fun u v => bform_comm Q u v⟩
  have hXo := isOrthogonal_specP x
  have hL : IsomCent.LieAbelian (bform Q) X := fun Y₁ Y₂ h₁ h₂ c₁ c₂ _ _ => hab Y₁ Y₂ h₁ h₂ c₁ c₂
  -- `dim ker (X − 1) ≤ 2`
  have hE : Module.End.eigenspace (-X) (-1) = Module.End.eigenspace X 1 := by
    ext v; simp
  have hdim : finrank L (Module.End.eigenspace X 1) ≤ 2 := by
    rw [← hE]
    refine IsomCent.finrank_eigenspace_neg_one_le_two hB hQ (fun u v => ?_)
      (Module.End.isSemisimple_neg.2 hss) ?_
    · simp only [LinearMap.neg_apply, map_neg, neg_neg]
      exact hXo u v
    · intro Y₁ Y₂ h₁ h₂ c₁ c₂ _ _
      exact hab Y₁ Y₂ h₁ h₂ (by simpa using c₁.neg_left) (by simpa using c₂.neg_left)
  obtain ⟨hcg, hdg⟩ := det_restrict_one_eq_one_of_commute hQ x hss g hg
  obtain ⟨hch, hdh⟩ := det_restrict_one_eq_one_of_commute hQ x hss h hh
  rcases Nat.lt_or_ge (finrank L (Module.End.eigenspace X 1)) 2 with h1 | h2
  · -- `dim ≤ 1`: `P(g)` fixes `ker (X − 1)`
    refine (commute_of_fixes_eigenspace_one hQ hss hL hg (fun w hw => ?_) hh).symm
    rcases Nat.lt_succ_iff.1 h1 |> Nat.le_one_iff_eq_zero_or_eq_one.1 with h0 | h1
    · have : (⟨w, hw⟩ : Module.End.eigenspace X 1) = 0 :=
        (Module.finrank_zero_iff.1 h0).elim _ _
      rw [show w = 0 from congrArg Subtype.val this, map_zero]
    · obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1
        ((specP Q g : V →ₗ[L] V).restrict
          (IsomCent.mapsTo_eigenspace_of_commute (commute_toLinearMap hcg) 1))
      rw [hc, LinearMap.det_smul, LinearMap.det_id, h1, pow_one, mul_one] at hdg
      have := congrArg Subtype.val (LinearMap.congr_fun hc ⟨w, hw⟩)
      rw [hdg, one_smul, LinearMap.coe_restrict_apply] at this
      exact this
  · -- `dim = 2`: a hyperbolic plane
    have h2 : finrank L (Module.End.eigenspace X 1) = 2 := le_antisymm hdim h2
    have hpnd : (polarBilin Q).Nondegenerate :=
      QuadraticMap.nondegenerate_polar_iff.mpr ((isNondeg_iff_nondegenerate _).1 hQ)
    have hnd : ∀ u ∈ Module.End.eigenspace X 1,
        (∀ u' ∈ Module.End.eigenspace X 1, polar Q u u' = 0) → u = 0 := by
      intro u hu h0
      have h := (IsomCent.pairing_eigenspace hB hQ hXo hss 1).2 u hu
      rw [inv_one] at h
      refine h fun w hw => ?_
      have := h0 w hw
      rw [polar_eq_two_mul_bform] at this
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero
    obtain ⟨e, he, f, hf, hee, hff, hef⟩ := exists_hypPair_of_finrank_eq_two hpnd h2 hnd
    have hQe : Q e = 0 := by
      have := hee; rw [polar_self, nsmul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left (by norm_num)
    have hQf : Q f = 0 := by
      have := hff; rw [polar_self, nsmul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left (by norm_num)
    obtain ⟨c, hce, hcf⟩ := exists_smul_of_det_restrict_eq_one (polar_specP g) h2 _ he hf hee hff
      hef hdg
    obtain ⟨d, hde, hdf⟩ := exists_smul_of_det_restrict_eq_one (polar_specP h) h2 _ he hf hee hff
      hef hdh
    have hfe : polar Q f e = 1 := by rw [polar_comm, hef]
    set s := hypGSpin hQe hQf hef c
    have hs : ∀ v, specP Q s v = v + (((c⁻¹ : Lˣ) : L) - 1) • (polar Q f v • e) +
        ((c : L) - 1) • (polar Q e v • f) := specP_hypGSpin hQe hQf hef c
    -- `s` commutes with `x` and `h`
    have hxe : specP Q x e = ((1 : Lˣ) : L) • e := by
      rw [Units.val_one, one_smul]; exact Module.End.mem_eigenspace_iff.1 he |>.trans (one_smul _ _)
    have hxf : specP Q x f = (((1 : Lˣ)⁻¹ : Lˣ) : L) • f := by
      rw [inv_one, Units.val_one, one_smul]
      exact Module.End.mem_eigenspace_iff.1 hf |>.trans (one_smul _ _)
    have hsx : Commute s x :=
      Subtype.ext (Units.ext (commute_hypUnit hQe hQf hef hxe hxf c).symm.eq)
    have hhs : Commute h s := Subtype.ext (Units.ext (commute_hypUnit hQe hQf hef hde hdf c))
    -- `g s` fixes `ker (X − 1)`, so commutes with `h`
    have hse : specP Q s e = ((c⁻¹ : Lˣ) : L) • e := by rw [hs, hfe, hee]; module
    have hsf : specP Q s f = (c : L) • f := by rw [hs, hff, hef]; module
    have hgs : ∀ w ∈ Module.End.eigenspace X 1, specP Q (g * s) w = w := by
      intro w hw
      obtain ⟨α, β, rfl⟩ := exists_eq_smul_add_smul_of_hypPair h2 he hf hee hff hef hw
      have hce' : specP Q g e = (c : L) • e := hce
      have hcf' : specP Q g f = ((c⁻¹ : Lˣ) : L) • f := hcf
      rw [map_mul, mul_apply_eq_comp, map_add, map_smul, map_smul, hse, hsf, map_add,
        map_smul, map_smul, map_smul, map_smul, hce', hcf', smul_smul, smul_smul]
      simp
    have hhgs := commute_of_fixes_eigenspace_one hQ hss hL (hg.mul_left hsx) hgs hh
    have hgh : Commute h g := by
      have e1 : g = g * s * s⁻¹ := by group
      rw [e1]
      exact hhgs.mul_right hhs.inv_right
    exact hgh.symm

end Steinberg

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V}

/-- **The centralizer of a regular semisimple element of `GSpin(V)` is commutative**: for `x`
semisimple on `C(V)` with `gspin(V)_x` abelian, any two elements of `GSpin(V)` commuting with `x`
commute.  (The centralizer is a maximal torus: connected by Steinberg's theorem, as the derived
group `Spin(V)` is simply connected, with abelian Lie algebra.)

Proof, without connectedness, after base change to `K̄` (`bcGSpin_injective`): `P(x)_{K̄}` is
semisimple (`isSemisimple_specP_baseChange`), and the skew endomorphisms of `V_{K̄}` commuting
with `P(x)_{K̄}` commute, since `gspin(V)_x` is abelian (`commute_baseChange_of_lie_eq_zero` with
`U = 0`); conclude by `Steinberg.commute_of_forall_skew_commute`. -/
theorem commute_of_isRegular [CharZero K] [FiniteDimensional K V] (hQ : IsNondeg Q) (x : GSpin Q)
    (hss : Module.End.IsSemisimple
      (LinearMap.mulLeft K ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))
    (hab : IsLieAbelian
      (lieCentralizer (gspin Q) ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))
    {g h : GSpin Q} (hg : Commute g x) (hh : Commute h x) : Commute g h := by
  have hQL := isNondeg_baseChange Q hQ
  have hssL : Module.End.IsSemisimple (specP _ (bcGSpin Q x) :
      AlgebraicClosure K ⊗[K] V →ₗ[AlgebraicClosure K] AlgebraicClosure K ⊗[K] V) := by
    rw [specP_bcGSpin]; exact isSemisimple_specP_baseChange x hss
  have habL : ∀ Y₁ Y₂ : Module.End (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] V),
      (bform (Q.baseChange (AlgebraicClosure K))).IsSkewAdjoint Y₁ →
      (bform (Q.baseChange (AlgebraicClosure K))).IsSkewAdjoint Y₂ →
      Commute (specP _ (bcGSpin Q x) :
        AlgebraicClosure K ⊗[K] V →ₗ[AlgebraicClosure K] AlgebraicClosure K ⊗[K] V) Y₁ →
      Commute (specP _ (bcGSpin Q x) :
        AlgebraicClosure K ⊗[K] V →ₗ[AlgebraicClosure K] AlgebraicClosure K ⊗[K] V) Y₂ →
      Commute Y₁ Y₂ := by
    intro Y₁ Y₂ h₁ h₂ c₁ c₂
    rw [specP_bcGSpin] at c₁ c₂
    refine commute_baseChange_of_lie_eq_zero hQ x ⊥ (fun X hX Y hY _ _ => ?_) h₁ h₂ c₁ c₂
      (fun w hw => by rw [(Submodule.mem_bot K).1 hw, TensorProduct.tmul_zero, map_zero])
      (fun w hw => by rw [(Submodule.mem_bot K).1 hw, TensorProduct.tmul_zero, map_zero])
    have h0 := congrArg Subtype.val (hab.trivial ⟨X, hX⟩ ⟨Y, hY⟩)
    rwa [LieSubalgebra.coe_bracket] at h0
  have key := Steinberg.commute_of_forall_skew_commute hQL hssL habL (hg.map (bcGSpin Q))
    (hh.map (bcGSpin Q))
  exact bcGSpin_injective Q (by rw [map_mul, map_mul, key.eq])

section FlagLevi

variable {F : IsotropicFlag Q} {ι : Type*} [Fintype ι] {b : Basis ι K V} {wt : ι → ℤ}

/-- **`GSpin(V)_x ⊆ M_F` for `x ∈ M_F` with commutative centralizer** (Waldspurger 2010, §2.3,
for `G_x = Z_G(x)⁰`, here the full centralizer since `Z_G(x)` is connected (Steinberg; `Spin` is
simply connected)):
if every two elements commuting with `x ∈ flagLevi b wt` commute, then every `g` commuting with
`x` lies in `flagLevi b wt`.  A lift `T` of `λ(2)` has `T x T⁻¹ = ±x`, so `T²` commutes with `x`,
hence with `g`; then `P(g)` commutes with `λ(4)` and preserves its eigenspaces, the weight
spaces. -/
theorem mem_flagLevi_of_commute [CharZero K] [FiniteDimensional K V] (hQ : IsNondeg Q)
    (hs : IsFlagSplitting F b wt) {x : GSpin Q} (hx : x ∈ flagLevi (Q := Q) b wt)
    (hcomm : ∀ g h : GSpin Q, Commute g x → Commute h x → Commute g h)
    {g : GSpin Q} (hg : Commute g x) : g ∈ flagLevi (Q := Q) b wt := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  obtain ⟨T, hT⟩ := hs.exists_cochar_lift hQ h2
  have hTc : (specP Q T : V →ₗ[K] V) = cochar b wt 2 :=
    b.ext fun i => by rw [cochar_basis]; exact hT i
  -- `P(T)` commutes with `P(x)`
  have hTx : Commute (specP Q T) (specP Q x) := by
    change specP Q T * specP Q x = specP Q x * specP Q T
    refine LinearEquiv.toLinearMap_injective ?_
    change (specP Q T : V →ₗ[K] V) ∘ₗ (specP Q x : V →ₗ[K] V) =
      (specP Q x : V →ₗ[K] V) ∘ₗ (specP Q T : V →ₗ[K] V)
    rw [hTc]
    exact cochar_comp_of_isHomog (mem_flagLevi_iff.1 hx) 2
  -- `T x T⁻¹ = c x` with `c² = 1`, so `T²` commutes with `x`
  obtain ⟨c, hc2, hc⟩ := CentralizerSign.exists_conj_eq_smul hQ hTx
  have hT2 : Commute (T * T) x := by
    have hcen := fun y => Subgroup.mem_center_iff.mp (scalarGSpin_mem_center Q c) y
    have e : T * T * x * (T * T)⁻¹ = x := by
      calc T * T * x * (T * T)⁻¹ = T * (T * x * T⁻¹) * T⁻¹ := by group
        _ = T * (scalarGSpin Q c * x) * T⁻¹ := by rw [hc]
        _ = scalarGSpin Q c * (T * x * T⁻¹) := by rw [← mul_assoc T, hcen T]; group
        _ = scalarGSpin Q c * (scalarGSpin Q c * x) := by rw [hc]
        _ = x := by rw [← mul_assoc, ← map_mul, ← pow_two, hc2, map_one, one_mul]
    exact (mul_inv_eq_iff_eq_mul.mp e)
  have hgT := hcomm g (T * T) hg hT2
  -- `P(g)` commutes with `λ(4)`
  have hP : (specP Q g : V →ₗ[K] V) ∘ₗ cochar b wt 4 =
      cochar b wt 4 ∘ₗ (specP Q g : V →ₗ[K] V) := by
    have h4 : cochar b wt (4 : K) = (specP Q (T * T) : V →ₗ[K] V) := by
      rw [map_mul, show ((specP Q T * specP Q T : V ≃ₗ[K] V) : V →ₗ[K] V) =
        (specP Q T : V →ₗ[K] V) ∘ₗ (specP Q T : V →ₗ[K] V) from rfl, hTc, cochar_mul]
      norm_num
    rw [h4, map_mul]
    have := congrArg (fun e : V ≃ₗ[K] V => (e : V →ₗ[K] V)) (congrArg (specP Q) hgT.eq)
    simp only [map_mul] at this
    exact this
  -- `4^w` separates the weights
  have hinj : Function.Injective fun w : ℤ => (4 : K) ^ w := by
    intro m n hmn
    have h : (((4 : ℚ) ^ m : ℚ) : K) = (((4 : ℚ) ^ n : ℚ) : K) := by
      simpa only [Rat.cast_zpow, Rat.cast_ofNat] using hmn
    exact zpow_right_injective₀ (by norm_num : (0 : ℚ) < 4) (by norm_num) (Rat.cast_injective h)
  exact mem_flagLevi_iff.2 (isHomog_of_comp_cochar hinj hP)

/-- **`GSpin(V)_x ⊆ M_F` for regular semisimple `x ∈ M_F`** (Waldspurger 2010, §2.3:
`G_x = M_x ⊂ M`; Beuzart-Plessis §1.10), from `mem_flagLevi_of_commute` and
`commute_of_isRegular`. -/
theorem mem_flagLevi_of_commute_of_isRegular [CharZero K] [FiniteDimensional K V]
    (hQ : IsNondeg Q) (hs : IsFlagSplitting F b wt) {x : GSpin Q}
    (hx : x ∈ flagLevi (Q := Q) b wt)
    (hss : Module.End.IsSemisimple
      (LinearMap.mulLeft K ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))
    (hab : IsLieAbelian
      (lieCentralizer (gspin Q) ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))
    {g : GSpin Q} (hg : Commute g x) : g ∈ flagLevi (Q := Q) b wt :=
  mem_flagLevi_of_commute hQ hs hx (fun _ _ => commute_of_isRegular hQ x hss hab) hg

end FlagLevi

end GSpinGGP
