/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.Triple

/-!
# Galois cohomology of the tori `S_x` and Kottwitz signs (cited)

The bookkeeping of Thesis §6.6–6.7, set up as follows: inner forms are indexed by `H¹(F, SO(W))`
(`InnerFormSystem`), and the torus attached to `x ∈ Γ(G,H)` is `S_x = T_x/A_{G,H}`, viewed in
`SO(W)` through `P : GSpin(W) → SO(W)`.

## §1 Definitions (real definitions, no axioms)

* `GalF F = Aut(F̄/F)` and its entrywise action `galGL` on `GL_m(F̄)`.
* `GalCocycle S`: continuous `1`-cocycles `σ ↦ a_σ ∈ S ⊆ GL_m(F̄)`, `a_{στ} = a_σ σ(a_τ)`, where
  *continuous* means that `a_σ` only depends on `σ|_E` for some finite extension `E/F`
  (equivalently, `a` is locally constant for the Krull topology).
* `H1 S`: cocycles modulo `a ∼ b ⇔ b_σ = c⁻¹ a_σ σ(c)` for some `c ∈ S`
  (Serre, *Cohomologie galoisienne*, I §5.1).  For `S = S_x(F̄)` this is `H¹(F, S_x)`.
* `torusFbar d x = T_x(F̄)` (centralizer of `x` in `GSpin(W)(F̄)` fixing `W'_x ⊗ F̄`) and
  `torusBarFbar d x = P(T_x(F̄)) = S_x(F̄) ⊆ SO(W)(F̄)`, as matrices in the rational basis.
* `IsTwistBy Q Q' a`: `a_σ = φ⁻¹ ∘ σφ` for some `F̄`-isometry `φ : W_{F̄} ≃ W'_{F̄}`, i.e. the
  class of `a` in `H¹(F, O(W))` is that of `W'` (same convention as `InnerTwist.cocycle`).
* `TwistIdx IF x β α`: `q_x(β) = α`, where `q_x : H¹(F, S_x) → H¹(F, SO(W)) ≃ IF.Idx` is
  induced by `S_x ⊆ SO(W)`.  It is a relation; that it is the graph of
  a function is `Main.existsUnique_twistIdx`.

## §2 Cited results (axioms)

* `finite_H1_torusBar`: `H¹(F, S_x)` is finite (Borel–Serre; Serre, *Cohomologie galoisienne*,
  III §4.3 Thm. 4).
* `kottwitzSign_twistIdx_mul`: `β ↦ e(G_{q_x(β)})` is multiplicative on `H¹(F, S_x)`
  (Kottwitz 1983 and BP (12.1.6), for the inner forms indexed by `H¹(F, SO(W))`; see its
  docstring).
-/

noncomputable section

open scoped Classical TensorProduct

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

set_option linter.unusedSectionVars false

/-! ## §1 Definitions -/

/-- The absolute Galois group `Γ_F = Aut(F̄/F)` (abstract group; continuity of cocycles is imposed
separately, `GalCocycle.continuous'`). -/
abbrev GalF (F : Type*) [Field F] : Type _ := AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F

/-- The action of `σ ∈ Γ_F` on `GL_m(F̄)`, entrywise.  For the matrix `M` of an `F̄`-linear
endomorphism `f` of `F̄ ⊗ F^m` in the rational basis, `σ(M)` is the matrix of `galoisConj σ f`. -/
def galGL (m : ℕ) (σ : GalF F) :
    GL (Fin m) (AlgebraicClosure F) →* GL (Fin m) (AlgebraicClosure F) :=
  Units.map (RingHom.mapMatrix (σ : AlgebraicClosure F →+* AlgebraicClosure F)).toMonoidHom

theorem coe_galGL (m : ℕ) (σ : GalF F) (g : GL (Fin m) (AlgebraicClosure F)) :
    ((galGL m σ g : GL (Fin m) (AlgebraicClosure F)) : Matrix (Fin m) (Fin m) _) =
      (g : Matrix (Fin m) (Fin m) _).map σ := rfl

/-- A continuous `1`-cocycle of `Γ_F` with values in `S ⊆ GL_m(F̄)` (Serre, *Cohomologie
galoisienne*, I §5.1): `a_{στ} = a_σ · σ(a_τ)`, and `a_σ` depends only on the restriction of `σ`
to some finite extension `E/F` (continuity for the Krull topology, `S` being discrete). -/
structure GalCocycle {m : ℕ} (S : Subgroup (GL (Fin m) (AlgebraicClosure F))) where
  /-- `σ ↦ a_σ` -/
  toFun : GalF F → GL (Fin m) (AlgebraicClosure F)
  mem' : ∀ σ, toFun σ ∈ S
  cocycle' : ∀ σ τ, toFun (σ * τ) = toFun σ * galGL m σ (toFun τ)
  continuous' : ∃ E : IntermediateField F (AlgebraicClosure F), FiniteDimensional F E ∧
    ∀ σ τ : GalF F, (∀ e ∈ E, σ e = τ e) → toFun σ = toFun τ

namespace GalCocycle

variable {m : ℕ} {S : Subgroup (GL (Fin m) (AlgebraicClosure F))}

/-- Cohomologous cocycles: `b_σ = c⁻¹ a_σ σ(c)` for some `c ∈ S`. -/
def Rel (a b : GalCocycle S) : Prop :=
  ∃ c ∈ S, ∀ σ, b.toFun σ = c⁻¹ * a.toFun σ * galGL m σ c

theorem rel_refl (a : GalCocycle S) : Rel a a :=
  ⟨1, S.one_mem, fun σ => by simp⟩

theorem rel_symm {a b : GalCocycle S} (h : Rel a b) : Rel b a := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c⁻¹, S.inv_mem hc, fun σ => ?_⟩
  rw [h σ, map_inv]
  group

theorem rel_trans {a b e : GalCocycle S} (h₁ : Rel a b) (h₂ : Rel b e) : Rel a e := by
  obtain ⟨c, hc, h₁⟩ := h₁
  obtain ⟨c', hc', h₂⟩ := h₂
  refine ⟨c * c', S.mul_mem hc hc', fun σ => ?_⟩
  rw [h₂ σ, h₁ σ, map_mul]
  group

/-- Cohomology of cocycles is an equivalence relation. -/
instance setoid (S : Subgroup (GL (Fin m) (AlgebraicClosure F))) : Setoid (GalCocycle S) :=
  ⟨Rel, ⟨rel_refl, rel_symm, rel_trans⟩⟩

end GalCocycle

/-- `H¹(F, S)` for `S ⊆ GL_m(F̄)` (a pointed set; Serre, *Cohomologie galoisienne*, I §5.1). -/
def H1 {m : ℕ} (S : Subgroup (GL (Fin m) (AlgebraicClosure F))) : Type _ :=
  Quotient (GalCocycle.setoid S)

/-- The class of a cocycle. -/
def H1.mk {m : ℕ} {S : Subgroup (GL (Fin m) (AlgebraicClosure F))} (a : GalCocycle S) : H1 S :=
  Quotient.mk _ a

theorem H1.mk_eq_mk {m : ℕ} {S : Subgroup (GL (Fin m) (AlgebraicClosure F))}
    {a b : GalCocycle S} : H1.mk a = H1.mk b ↔ GalCocycle.Rel a b :=
  Quotient.eq

theorem H1.ind {m : ℕ} {S : Subgroup (GL (Fin m) (AlgebraicClosure F))} {p : H1 S → Prop}
    (h : ∀ a, p (H1.mk a)) (β : H1 S) : p β :=
  Quotient.ind h β

theorem H1.mk_out {m : ℕ} {S : Subgroup (GL (Fin m) (AlgebraicClosure F))} (β : H1 S) :
    H1.mk (Quotient.out β) = β :=
  Quotient.out_eq β

namespace GalCocycle

variable {m : ℕ} {S : Subgroup (GL (Fin m) (AlgebraicClosure F))}

/-- The trivial cocycle `σ ↦ 1`. -/
def one (S : Subgroup (GL (Fin m) (AlgebraicClosure F))) : GalCocycle S where
  toFun _ := 1
  mem' _ := S.one_mem
  cocycle' σ τ := by rw [map_one, mul_one]
  continuous' := ⟨⊥, inferInstance, fun _ _ _ => rfl⟩

/-- If `S` is trivial, every cocycle is the trivial one, so `H¹(F, S)` is a point. -/
theorem rel_one_of_eq_bot (hS : S = ⊥) (a : GalCocycle S) : Rel (one S) a := by
  subst hS
  exact ⟨1, Subgroup.one_mem _, fun σ => by
    rw [Subgroup.mem_bot.1 (a.mem' σ)]
    simp [one]⟩

/-- The pointwise product of two cocycles with values in a commutative, Galois-stable `S`
(for a torus, the group law of `H¹(F, S)`, Serre, *Cohomologie galoisienne*, I §5.1). -/
def mulOf (hcomm : ∀ s ∈ S, ∀ t ∈ S, Commute s t)
    (hstab : ∀ σ : GalF F, ∀ s ∈ S, galGL m σ s ∈ S) (a b : GalCocycle S) : GalCocycle S where
  toFun σ := a.toFun σ * b.toFun σ
  mem' σ := S.mul_mem (a.mem' σ) (b.mem' σ)
  cocycle' σ τ := by
    rw [a.cocycle', b.cocycle', map_mul]
    have h := hcomm _ (hstab σ _ (a.mem' τ)) _ (b.mem' σ)
    simp only [mul_assoc]
    rw [← mul_assoc (galGL m σ (a.toFun τ)), h.eq, mul_assoc]
  continuous' := by
    obtain ⟨E₁, h₁, he₁⟩ := a.continuous'
    obtain ⟨E₂, h₂, he₂⟩ := b.continuous'
    refine ⟨E₁ ⊔ E₂, inferInstance, fun σ τ h => ?_⟩
    rw [he₁ σ τ fun e he => h e (le_sup_left (a := E₁) he),
      he₂ σ τ fun e he => h e (le_sup_right (a := E₁) he)]

theorem mulOf_toFun (hcomm : ∀ s ∈ S, ∀ t ∈ S, Commute s t)
    (hstab : ∀ σ : GalF F, ∀ s ∈ S, galGL m σ s ∈ S) (a b : GalCocycle S) (σ : GalF F) :
    (mulOf hcomm hstab a b).toFun σ = a.toFun σ * b.toFun σ := rfl

end GalCocycle

/-- Translation `β ↦ [a] · β` on `H¹(F, S)` for `S` commutative and Galois-stable. -/
def H1.translate {m : ℕ} {S : Subgroup (GL (Fin m) (AlgebraicClosure F))}
    (hcomm : ∀ s ∈ S, ∀ t ∈ S, Commute s t)
    (hstab : ∀ σ : GalF F, ∀ s ∈ S, galGL m σ s ∈ S) (a : GalCocycle S) : H1 S → H1 S :=
  Quotient.map (GalCocycle.mulOf hcomm hstab a) fun b b' hb => by
    obtain ⟨c, hc, h⟩ := hb
    refine ⟨c, hc, fun σ => ?_⟩
    show a.toFun σ * b'.toFun σ = c⁻¹ * (a.toFun σ * b.toFun σ) * galGL m σ c
    have hac := (hcomm _ (a.mem' σ) _ (S.inv_mem hc))
    rw [h σ, ← mul_assoc, ← mul_assoc, hac.eq]
    simp only [mul_assoc]

theorem H1.translate_mk {m : ℕ} {S : Subgroup (GL (Fin m) (AlgebraicClosure F))}
    (hcomm : ∀ s ∈ S, ∀ t ∈ S, Commute s t)
    (hstab : ∀ σ : GalF F, ∀ s ∈ S, galGL m σ s ∈ S) (a b : GalCocycle S) :
    H1.translate hcomm hstab a (H1.mk b) = H1.mk (GalCocycle.mulOf hcomm hstab a b) := rfl

/-- Translation on `H¹(F, S)` is injective (so bijective when `H¹(F, S)` is finite). -/
theorem H1.translate_injective {m : ℕ} {S : Subgroup (GL (Fin m) (AlgebraicClosure F))}
    (hcomm : ∀ s ∈ S, ∀ t ∈ S, Commute s t)
    (hstab : ∀ σ : GalF F, ∀ s ∈ S, galGL m σ s ∈ S) (a : GalCocycle S) :
    Function.Injective (H1.translate hcomm hstab a) := by
  intro β β' h
  induction β using H1.ind with | h b => ?_
  induction β' using H1.ind with | h b' => ?_
  rw [H1.translate_mk, H1.translate_mk, H1.mk_eq_mk] at h
  obtain ⟨c, hc, h⟩ := h
  refine H1.mk_eq_mk.2 ⟨c, hc, fun σ => ?_⟩
  have h' := h σ
  simp only [GalCocycle.mulOf_toFun] at h'
  have hac := (hcomm _ (a.mem' σ) _ (S.inv_mem hc))
  rw [← mul_assoc c⁻¹, hac.symm.eq, mul_assoc (a.toFun σ), mul_assoc (a.toFun σ)] at h'
  rw [mul_left_cancel h', mul_assoc]

/-- The matrix, in the rational basis `bcBasis`, of `P(g)` for `g ∈ GSpin(W)(F̄)`:
`P_{F̄} : GSpin(W)(F̄) → SO(W)(F̄) ⊆ GL_m(F̄)`. -/
def specMatFbar {m : ℕ} (Q : QuadraticForm F (Fin m → F)) :
    GSpin (Q.baseChange (AlgebraicClosure F)) →* GL (Fin m) (AlgebraicClosure F) :=
  (Units.map (LinearMap.toMatrixAlgEquiv (bcBasis F m)).toMonoidHom).comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (AlgebraicClosure F)
      (AlgebraicClosure F ⊗[F] (Fin m → F))).symm.toMonoidHom.comp
      (specP (Q.baseChange (AlgebraicClosure F))))

theorem coe_specMatFbar {m : ℕ} (Q : QuadraticForm F (Fin m → F))
    (g : GSpin (Q.baseChange (AlgebraicClosure F))) :
    ((specMatFbar Q g : GL (Fin m) (AlgebraicClosure F)) : Matrix (Fin m) (Fin m) _) =
      LinearMap.toMatrix (bcBasis F m) (bcBasis F m)
        ((specP (Q.baseChange (AlgebraicClosure F)) g :
          (AlgebraicClosure F ⊗[F] (Fin m → F)) ≃ₗ[AlgebraicClosure F] _) :
          (AlgebraicClosure F ⊗[F] (Fin m → F)) →ₗ[AlgebraicClosure F] _) := rfl

namespace GGPData

variable (d : GGPData F)

/-- `T_x(F̄)`: the elements of `GSpin(W)(F̄)` commuting with `x` and acting trivially on
`W'_x ⊗ F̄` (the `F̄`-points of the torus `T_x`; compare `GGPData.torusOf`, its
`F`-points). -/
def torusFbar (x : ↥(GSpin d.QW)) :
    Subgroup ↥(GSpin (d.QW.baseChange (AlgebraicClosure F))) where
  carrier := {g | Commute ((g : (CliffordAlgebra _)ˣ)) (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ)) ∧
    ∀ w ∈ (fixedSub x).baseChange (AlgebraicClosure F),
      specP (d.QW.baseChange (AlgebraicClosure F)) g w = w}
  one_mem' := ⟨Commute.one_left _, fun w _ => by simp⟩
  mul_mem' := fun {g h} hg hh => by
    refine ⟨?_, fun w hw => ?_⟩
    · simpa only [Subgroup.coe_mul] using hg.1.mul_left hh.1
    · rw [map_mul, LinearEquiv.mul_apply, hh.2 w hw, hg.2 w hw]
  inv_mem' := fun {g} hg => by
    refine ⟨?_, fun w hw => ?_⟩
    · simpa only [Subgroup.coe_inv] using hg.1.inv_left
    · have h1 : specP _ g⁻¹ (specP _ g w) = w := by
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      rw [hg.2 w hw] at h1
      exact h1

/-- `S_x(F̄) = P(T_x(F̄)) ⊆ SO(W)(F̄) ⊆ GL_m(F̄)`: the `F̄`-points of `S_x = T_x/A_{G,H}`
(`ker P = F̄^×` is the `F̄`-points of `A_{G,H}`).  For `x ∈ Γ(G,H)` this is the
anisotropic maximal torus `Z_{SO(W''_x)}(x̄)⁰` of `SO(W''_x)`, extended by `1` on `W'_x`. -/
def torusBarFbar (x : ↥(GSpin d.QW)) : Subgroup (GL (Fin d.m) (AlgebraicClosure F)) :=
  (d.torusFbar x).map (specMatFbar d.QW)

end GGPData

/-- `a` is the cocycle of the twist `W ⇝ W'`: `a_σ = φ⁻¹ ∘ σφ` for some `F̄`-isometry
`φ : W_{F̄} ≃ W'_{F̄}` (matrices in the rational basis; same convention as
`InnerTwist.cocycle`).  So the class of `a` in `H¹(F, O(W))` is the class of the quadratic space
`W'`. -/
def IsTwistBy {m : ℕ} (Q Q' : QuadraticForm F (Fin m → F))
    (a : GalF F → GL (Fin m) (AlgebraicClosure F)) : Prop :=
  ∃ φ : (Q.baseChange (AlgebraicClosure F)).IsometryEquiv (Q'.baseChange (AlgebraicClosure F)),
    ∀ σ : GalF F, LinearMap.toMatrix (bcBasis F m) (bcBasis F m)
      (φ.toLinearEquiv.symm.toLinearMap ∘ₗ galoisConj σ φ.toLinearEquiv.toLinearMap) =
        ((a σ : GL (Fin m) (AlgebraicClosure F)) : Matrix (Fin m) (Fin m) _)

/-- `q_x(β) = α`: some cocycle representing `β ∈ H¹(F, S_x)` is the
cocycle of an `F̄`-isometry `W_{F̄} ≃ W_{α,F̄}`, i.e. the image of `β` under
`H¹(F, S_x) → H¹(F, SO(W)) ≃ IF.Idx` is `α`.  (Since `H¹(F,SO(W)) → H¹(F,O(W))` is injective,
the isometry need not be proper.) -/
def TwistIdx {d : GGPData F} (IF : InnerFormSystem d) (x : ↥(GSpin d.QW))
    (β : H1 (d.torusBarFbar x)) (α : IF.Idx) : Prop :=
  ∃ a : GalCocycle (d.torusBarFbar x), H1.mk a = β ∧ IsTwistBy d.QW (IF.twist α).Q' a.toFun

/-! ## §2 Cited results -/

/-- **Finiteness of `H¹(F, S_x)`** (Borel–Serre; Serre, *Cohomologie galoisienne*, III §4.3,
Thm. 4: for a linear algebraic group `L` over a `p`-adic field, `H¹(F, L)` is finite; for a torus
this is also Tate–Nakayama, Serre loc. cit. II §5.8).  Applied to `L = S_x`, whose `F̄`-points
with their Galois action are `torusBarFbar d x` (`P` is defined over `F`).  Stated for
`x ∈ Γ(G,H)`, where `S_x` is a torus. -/
axiom finite_H1_torusBar (d : GGPData F) (x : ↥(GSpin d.QW)) (hx : d.IsGammaElt x) :
    Finite (H1 (d.torusBarFbar x))

/-- **The Kottwitz sign is multiplicative on `H¹(F, S_x)`**.
For `G` quasi-split and `x ∈ Γ(G,H)`, if the cocycle `c` is the pointwise product of the cocycles
`a`, `b` (with values in `S_x`), then `e(G_{q_x[c]}) = e(G_{q_x[a]}) e(G_{q_x[b]})`.

Sources, combined as follows:
* Kottwitz, *Sign changes in harmonic analysis on reductive groups*, Trans. Amer. Math. Soc. 278
  (1983), 289–297: the sign `e(G')` of an inner form of a quasi-split group, equal to
  `(-1)^{rk_F G - rk_F G'}` for `F` `p`-adic (the formula `kottwitzSign`).  **The theorem number
  in Kottwitz 1983 is not verified**; the statement used is the one
  recalled in BP, *Astérisque* 418 (2020), §12.1.
* Beuzart-Plessis, loc. cit., §12.1: for pure inner forms of a quasi-split group `Ḡ`, `e(Ḡ')`
  is the image of the class of `Ḡ'` under the connecting map `H¹(F, Ḡ) → H²(F, {±1})` of the
  canonical central extension `Ḡ~ → Ḡ`; and (12.1.6): for a subtorus `S ⊆ Ḡ`, the composite
  `H¹(F, S) → H¹(F, Ḡ) → H²(F, {±1})` is a group homomorphism.
* The setup here: `Ḡ = SO(W) × SO(V)`, the inner form
  `G_α` has `e(G_α) = e(Ḡ_α)` (same adjoint group, same split central rank), the cocycles of the
  inner forms of the triple are `(a, a ⊕ 1_Z)` with `a` valued in `SO(W)`, and `S_x ⊆ Ḡ`
  diagonally.  So `e(G_{q_x(β)})` is the image of `β` under the homomorphism of (12.1.6).

The cohomology classes are compared through `TwistIdx` (`q_x`), so the axiom needs no group
structure on `H1`.  Degenerate cases: for `x` central, `S_x(F̄) = 1` and only `a = b = c = 1`
occur, with `q_x = 1` and `e = 1`. -/
axiom kottwitzSign_twistIdx_mul {d : GGPData F} (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (x : ↥(GSpin d.QW)) (hx : d.IsGammaElt x)
    (a b c : GalCocycle (d.torusBarFbar x)) (hc : ∀ σ, c.toFun σ = a.toFun σ * b.toFun σ)
    (α β γ : IF.Idx) (ha : TwistIdx IF x (H1.mk a) α) (hb : TwistIdx IF x (H1.mk b) β)
    (hγ : TwistIdx IF x (H1.mk c) γ) :
    kottwitzSign d (IF.twist γ) = kottwitzSign d (IF.twist α) * kottwitzSign d (IF.twist β)

end GSpinGGP
