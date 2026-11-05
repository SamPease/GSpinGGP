/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.KottwitzDelta
import GSpinGGP.GGP.WittParity

/-!
# Multiplicativity of the Kottwitz sign on `H¹(F, S_x)`

`kottwitzSign_twistIdx_mul` (BP *Astérisque* 418, (12.1.6), with the sign of Kottwitz 1983),
proved without Brauer groups from `GalCocycle.DRel` (`GGP/KottwitzDelta.lean`): the sign of `G_α` is
`1` exactly when `W_α ≅ W`, and isometry of twists is the relation "lifts to `T_x(F̄)` with equal
obstructions", which is compatible with products.
-/

noncomputable section

open scoped Classical TensorProduct

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

set_option linter.unusedSectionVars false

/-- **The Kottwitz sign is multiplicative on `H¹(F, S_x)`**.
For `G` quasi-split and `x ∈ Γ(G,H)`, if the cocycle `c` is the pointwise product of the cocycles
`a`, `b` (with values in `S_x`), then `e(G_{q_x[c]}) = e(G_{q_x[a]}) e(G_{q_x[b]})`.
(BP *Astérisque* 418, (12.1.6), states this for any quasi-split group through the connecting map to
`Br₂(F)`; for `p`-adic `F` the Kottwitz sign is `(−1)^{rk_F G − rk_F G'}`, Kottwitz, Trans. Amer.
Math. Soc. 278 (1983).)

Own work, without Brauer groups: `e(G_α) = 1` exactly when `W_α ≅ W`
(`WittParity.kottwitzSign_eq_one_of_nonempty`, `WittParity.kottwitzSign_eq_neg_one`), and
`W_α ≅ W_β` exactly when the cocycles have lifts to `T_x(F̄)` with equal obstructions
(`GalCocycle.DRel`), a relation compatible with products; there are at most two classes of the
dimension and discriminant of `W`. The quasi-split hypothesis is not needed. `F : Type`, as in
`GaloisTorus` (commutativity of `S_x`). -/
theorem kottwitzSign_twistIdx_mul {d : GGPData F} (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (x : ↥(GSpin d.QW)) (hx : d.IsGammaElt x)
    (a b c : GalCocycle (d.torusBarFbar x)) (hc : ∀ σ, c.toFun σ = a.toFun σ * b.toFun σ)
    (α β γ : IF.Idx) (ha : TwistIdx IF x (H1.mk a) α) (hb : TwistIdx IF x (H1.mk b) β)
    (hγ : TwistIdx IF x (H1.mk c) γ) :
    kottwitzSign d (IF.twist γ) = kottwitzSign d (IF.twist α) * kottwitzSign d (IF.twist β) := by
  have _ := hqs
  have hcomm := torusBarFbar_commute x hx
  have hstab : ∀ σ : GalF F, ∀ s ∈ d.torusBarFbar x, galGL d.m σ s ∈ d.torusBarFbar x :=
    fun σ => galGL_mem_torusBarFbar x σ
  obtain ⟨a', ha'mk, ha'⟩ := ha
  obtain ⟨b', hb'mk, hb'⟩ := hb
  obtain ⟨c', hc'mk, hc'⟩ := hγ
  have Da : GalCocycle.DRel a' a := GalCocycle.DRel.of_rel (H1.mk_eq_mk.1 ha'mk)
  have Db : GalCocycle.DRel b' b := GalCocycle.DRel.of_rel (H1.mk_eq_mk.1 hb'mk)
  have Dc : GalCocycle.DRel c' c := GalCocycle.DRel.of_rel (H1.mk_eq_mk.1 hc'mk)
  have h1 : IsTwistBy d.QW d.QW (GalCocycle.one (d.torusBarFbar x)).toFun :=
    TwistDescent.isTwistBy_refl d.QW
  set one := GalCocycle.one (d.torusBarFbar x)
  set mul := GalCocycle.mulOf hcomm hstab
  have hcab : GalCocycle.DRel c (mul a b) := GalCocycle.DRel.of_toFun_eq (funext hc)
  -- `W_u ≅ W` iff `u` is `DRel`-related to the trivial cocycle
  have iso_of {u u' : GalCocycle (d.torusBarFbar x)} {Q : QuadraticForm F (Fin d.m → F)}
      (hQ : IsNondeg Q) (hu : IsTwistBy d.QW Q u.toFun) (h : GalCocycle.DRel u' one) (h' : GalCocycle.DRel u u') :
      Nonempty (d.QW.IsometryEquiv Q) :=
    GalCocycle.DRel.isometryEquiv d.nondeg hQ h1 hu (h'.trans h).symm
  have rel_of {u : GalCocycle (d.torusBarFbar x)} {Q : QuadraticForm F (Fin d.m → F)}
      (hu : IsTwistBy d.QW Q u.toFun) (h : Nonempty (d.QW.IsometryEquiv Q)) :
      GalCocycle.DRel u one :=
    GalCocycle.DRel.of_isometryEquiv d.nondeg hu h1 (h.map fun e => e.symm)
  have sgn (δ : IF.Idx) : kottwitzSign d (IF.twist δ) =
      if Nonempty (d.QW.IsometryEquiv (IF.twist δ).Q') then 1 else -1 := by
    split_ifs with h
    · exact WittParity.kottwitzSign_eq_one_of_nonempty d _ h
    · exact WittParity.kottwitzSign_eq_neg_one d _ h
  have hd : ∀ δ : IF.Idx, QuadClassify.DiscRel d.QW (IF.twist δ).Q' := fun δ =>
    (QuadClassify.sameDisc_iff_discRel _ _).1 (IF.twist δ).sameDisc
  -- the product with the trivial class
  have mul_one' {u v : GalCocycle (d.torusBarFbar x)} (h : GalCocycle.DRel u one) :
      GalCocycle.DRel (mul u v) v :=
    (h.mul_right hx v).trans (GalCocycle.DRel.of_toFun_eq (funext fun σ => one_mul _))
  rw [sgn α, sgn β, sgn γ]
  by_cases A : Nonempty (d.QW.IsometryEquiv (IF.twist α).Q')
  · -- `c ~ b`
    have hcb : GalCocycle.DRel c' b' :=
      ((Dc.trans hcab).trans (mul_one' ((Da.symm.trans (rel_of ha' A))))).trans Db.symm
    obtain ⟨e⟩ := GalCocycle.DRel.isometryEquiv (IF.twist γ).nondeg' (IF.twist β).nondeg' hc' hb' hcb
    have : Nonempty (d.QW.IsometryEquiv (IF.twist γ).Q') ↔
        Nonempty (d.QW.IsometryEquiv (IF.twist β).Q') :=
      ⟨fun ⟨f⟩ => ⟨f.trans e⟩, fun ⟨f⟩ => ⟨f.trans e.symm⟩⟩
    simp only [A, this, ite_true, one_mul]
  by_cases B : Nonempty (d.QW.IsometryEquiv (IF.twist β).Q')
  · have hba : GalCocycle.DRel (mul a b) (mul b a) := GalCocycle.DRel.of_toFun_eq
      (funext fun σ => (hcomm _ (a.mem' σ) _ (b.mem' σ)).eq)
    have hca : GalCocycle.DRel c' a' :=
      (((Dc.trans hcab).trans hba).trans (mul_one' ((Db.symm.trans (rel_of hb' B))))).trans
        Da.symm
    obtain ⟨e⟩ := GalCocycle.DRel.isometryEquiv (IF.twist γ).nondeg' (IF.twist α).nondeg' hc' ha' hca
    have : Nonempty (d.QW.IsometryEquiv (IF.twist γ).Q') ↔
        Nonempty (d.QW.IsometryEquiv (IF.twist α).Q') :=
      ⟨fun ⟨f⟩ => ⟨f.trans e⟩, fun ⟨f⟩ => ⟨f.trans e.symm⟩⟩
    simp only [B, this, A, ite_true, ite_false, mul_one]
  · simp only [A, B, ↓reduceIte]
    by_contra C
    have C' : ¬ Nonempty (d.QW.IsometryEquiv (IF.twist γ).Q') := fun h => C (by simp [h])
    -- `W_α ≅ W_γ` (two classes), so `a ~ c`, so `b ~ 1`
    have hαγ : Nonempty ((IF.twist α).Q'.IsometryEquiv (IF.twist γ).Q') := by
      rcases WittParity.pigeon d.nondeg (hd α) (hd γ) with h | h | h
      · exact absurd h A
      · exact absurd h C'
      · exact h
    have hac : GalCocycle.DRel (mul a (GalCocycle.invOf hx a)) (mul c (GalCocycle.invOf hx a)) :=
      ((Da.symm.trans (GalCocycle.DRel.of_isometryEquiv (IF.twist γ).nondeg' ha' hc' hαγ)).trans
        Dc).mul_right hx _
    have hb1 : GalCocycle.DRel b one := by
      refine ((GalCocycle.DRel.of_toFun_eq (funext fun σ => ?_)).trans hac.symm).trans
        (GalCocycle.DRel.of_toFun_eq (funext fun σ => ?_))
      · show b.toFun σ = c.toFun σ * (a.toFun σ)⁻¹
        rw [hc, (hcomm _ (a.mem' σ) _ (b.mem' σ)).eq, mul_inv_cancel_right]
      · show a.toFun σ * (a.toFun σ)⁻¹ = 1
        exact mul_inv_cancel _
    exact B (iso_of (IF.twist β).nondeg' hb' hb1 Db)

end GSpinGGP
