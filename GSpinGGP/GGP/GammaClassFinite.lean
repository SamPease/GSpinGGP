/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.GaloisTorus
import GSpinGGP.GGP.TorusFrame
import GSpinGGP.GGP.ConjCocycle

/-!
# Finitely many conjugacy classes of the tori `T_x`

The tori `T_x`, `x ∈ Γ(G,H)`, fall into finitely many `GSpin(W)(F)`-conjugacy classes
(`finite_gammaClass`), by the twisting argument of Serre, *Cohomologie galoisienne*,
I §5: tori `S_y(F̄)` of the same type (`dim W''_y`) are conjugate under `SO(W)(F̄)`
(`exists_conj_torusBarFbar`); the conjugator gives a class in `H¹(F, N_x)` (`conjCocycle`), finite by
Borel–Serre (`finite_H1_normalizerBar`); equal classes give an `F`-rational conjugator
(`exists_fixed_conj_of_rel`, `exists_specMatFbar_bcGSpin_eq`), which conjugates the tori
(`mem_torusOf_iff`).
-/

noncomputable section

open scoped Classical

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

namespace GGPData

variable {d : GGPData F}

theorem isGalStable_range_specMatFbar : IsGalStable (F := F) (specMatFbar d.QW).range := by
  rintro σ _ ⟨g, rfl⟩
  exact ⟨_, specMatFbar_galGS σ g⟩

/-- **`N_x(F̄)` is Galois-stable**: it is the intersection of the normalizer of the Galois-stable
`S_x(F̄)` (`galGL_mem_torusBarFbar`) with the Galois-stable `SO(W)(F̄)`. -/
theorem galGL_mem_normalizerBar (x : ↥(GSpin d.QW)) (σ : GalF F) :
    ∀ s ∈ d.normalizerBar x, galGL d.m σ s ∈ d.normalizerBar x :=
  IsGalStable.inf (IsGalStable.normalizer fun σ => galGL_mem_torusBarFbar x σ)
    isGalStable_range_specMatFbar σ

/-- **Tori of the same type are conjugate over `F̄`**: for `x, y ∈ Γ(G,H)` with
`dim W''_x = dim W''_y`, some `g ∈ SO(W)(F̄)` conjugates `S_x(F̄)` to `S_y(F̄)`.

Own work, standard. `S_x(F̄)` is the split torus of a hyperbolic frame of eigenvectors of
`P(x)_{F̄}` with orthogonal complement `W'_x ⊗ F̄` (`exists_hypFrame_torusFbar`); the frames of `x`
and `y` have the same size `(m − dim W')/2`, so an element of `SO(W)(F̄)` carries one to the other
(`IsHypFrame.exists_conj_hypTorus`: Witt's extension theorem and a reflection), and it is
`P` of an element of `GSpin(W)(F̄)` (`gspin_specP_surjective_SO`). -/
theorem exists_conj_torusBarFbar (x y : GSpin d.QW) (hx : d.IsGammaElt x) (hy : d.IsGammaElt y)
    (hdim : Module.finrank F (movedSub x) = Module.finrank F (movedSub y)) :
    ∃ g ∈ (specMatFbar d.QW).range,
      (d.torusBarFbar x).map (MulAut.conj g).toMonoidHom = d.torusBarFbar y := by
  obtain ⟨n₁, e₁, f₁, hF₁, hT₁⟩ := exists_hypFrame_torusFbar x hx
  obtain ⟨n₂, e₂, f₂, hF₂, hT₂⟩ := exists_hypFrame_torusFbar y hy
  have hfix : ∀ z : GSpin d.QW,
      Module.finrank F (fixedSub z) + Module.finrank F (movedSub z) = d.m := fun z => by
    have := LinearMap.finrank_range_add_finrank_ker
      ((specP d.QW z : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) - LinearMap.id)
    rw [Module.finrank_fin_fun] at this
    unfold fixedSub movedSub
    omega
  have h₁ := hF₁.finrank_add
  have h₂ := hF₂.finrank_add
  rw [finrank_eigenspace_bc_one, Module.finrank_baseChange, Module.finrank_fin_fun] at h₁ h₂
  have hn : n₁ = n₂ := by
    have := hfix x; have := hfix y; omega
  subst hn
  obtain ⟨g, hgQ, hgdet, hgT⟩ :=
    IsHypFrame.exists_conj_hypTorus polarBilin_baseChange_nondegenerate.1 hF₁ hF₂
  obtain ⟨γ, hγ⟩ := gspin_specP_surjective_SO _ (isNondeg_baseChange _ d.nondeg) g hgQ hgdet
  refine ⟨specMatFbar d.QW γ, ⟨γ, rfl⟩, ?_⟩
  rw [torusBarFbar_eq_map, torusBarFbar_eq_map, specMatFbar_eq_matGL_comp, MonoidHom.comp_apply,
    hγ, map_matGL_conj, hT₁, hgT, hT₂]

/-- Conjugating `S_y(F̄)` by `P(t)`, `t ∈ GSpin(W)(F)`, conjugates `T_y` by `t`. -/
theorem torusOf_eq_map_conj_of_torusBarFbar {y y' t : GSpin d.QW}
    (h : (d.torusBarFbar y').map (MulAut.conj (specMatFbar d.QW (bcGSpin d.QW t))).toMonoidHom =
      d.torusBarFbar y) :
    d.torusOf y = (d.torusOf y').map (MulAut.conj t).toMonoidHom := by
  ext s
  rw [mem_torusOf_iff, ← h]
  constructor
  · rintro ⟨u, hu, hus⟩
    refine ⟨t⁻¹ * s * t, (mem_torusOf_iff y' _).2 ?_, by simp [mul_assoc]⟩
    have e : specMatFbar d.QW (bcGSpin d.QW (t⁻¹ * s * t)) = u := by
      have := congrArg (fun v => (specMatFbar d.QW (bcGSpin d.QW t))⁻¹ * v *
        specMatFbar d.QW (bcGSpin d.QW t)) hus
      simpa [map_mul, map_inv, mul_assoc] using this.symm
    rw [e]; exact hu
  · rintro ⟨u, hu, rfl⟩
    refine ⟨_, (mem_torusOf_iff y' u).1 hu, ?_⟩
    simp [map_mul, map_inv, mul_assoc]

/-- **Equal classes give conjugate tori**: if `g, g' ∈ SO(W)(F̄)` conjugate `S_x(F̄)` to `S_y(F̄)`,
`S_{y'}(F̄)` and their cocycles have the same class in `H¹(F, N_x)`, then `T_y` and `T_{y'}` are
`GSpin(W)(F)`-conjugate. -/
theorem exists_conj_torusOf_of_H1 {x y y' : GSpin d.QW} {g g' : GL (Fin d.m) Kb}
    (hgA : g ∈ (specMatFbar d.QW).range) (hg'A : g' ∈ (specMatFbar d.QW).range)
    (hgS : (d.torusBarFbar x).map (MulAut.conj g).toMonoidHom = d.torusBarFbar y)
    (hg'S : (d.torusBarFbar x).map (MulAut.conj g').toMonoidHom = d.torusBarFbar y')
    (hg : ∀ σ : GalF F, g⁻¹ * galGL d.m σ g ∈ d.normalizerBar x)
    (hg' : ∀ σ : GalF F, g'⁻¹ * galGL d.m σ g' ∈ d.normalizerBar x)
    (hH : H1.mk (conjCocycle g hg) = H1.mk (conjCocycle g' hg')) :
    ∃ t : GSpin d.QW, d.torusOf y = (d.torusOf y').map (MulAut.conj t).toMonoidHom := by
  obtain ⟨h, hA, hfix, hconj⟩ := exists_fixed_conj_of_rel (A := (specMatFbar d.QW).range)
    (S := d.torusBarFbar x) (N := d.normalizerBar x) le_rfl hgA hg'A hg hg'
    (H1.mk_eq_mk.mp hH)
  obtain ⟨t, ht⟩ := exists_specMatFbar_bcGSpin_eq hA hfix
  refine ⟨t, torusOf_eq_map_conj_of_torusBarFbar ?_⟩
  rw [ht, ← hg'S, hconj, hgS]

end GGPData

open GGPData in
/-- **`Γ(G,H)` meets finitely many conjugacy classes of tori** (used implicitly in Thesis §6.5,
(6.5.3)).  Twisting argument: tori `S_y` of the same type `dim W''_y` are conjugate over `F̄`
(`GGPData.exists_conj_torusBarFbar`); the conjugator defines a class in
`H¹(F, N_{SO(W)}(S_x))`, a finite set by Borel–Serre, *Théorèmes de finitude en cohomologie
galoisienne*, Comment. Math. Helv. 39 (1964), Thm. 6.1 (`finite_H1_normalizerBar`); tori with equal
classes are `GSpin(W)(F)`-conjugate (`GGPData.exists_conj_torusOf_of_H1`).  (Borel–Serre's Cor. 6.5,
finiteness of conjugacy classes of maximal tori, is the direct statement but needs algebraic tori,
not formalized here.)  Consistent with `toyD_subsingleton_gammaClass` (`Sanity/Witnesses.lean`) and
`subsingleton_gammaClass` (`TraceFormula/Lie.lean`). -/
theorem finite_gammaClass (d : GGPData F) : Finite (GammaClass d) := by
  -- types `k = dim W''_y` and a representative of each
  let Ty := {k : Fin (d.m + 1) // ∃ y, d.IsGammaElt y ∧ Module.finrank F (movedSub y) = k}
  let rep : Ty → GSpin d.QW := fun k => Classical.choose k.2
  have hrep : ∀ k : Ty, d.IsGammaElt (rep k) ∧ Module.finrank F (movedSub (rep k)) = k.1 :=
    fun k => Classical.choose_spec k.2
  have hfin : ∀ k : Ty, Finite (H1 (d.normalizerBar (rep k))) :=
    fun k => finite_H1_normalizerBar d _ (hrep k).1
  have hlt : ∀ y : GSpin d.QW, Module.finrank F (movedSub y) < d.m + 1 := fun y =>
    Nat.lt_succ_of_le ((Submodule.finrank_le _).trans (by simp))
  -- the data of a torus
  let yOf : d.GammaTorus → GSpin d.QW := fun T => Classical.choose T.2
  have hyOf : ∀ T, d.IsGammaElt (yOf T) ∧ d.torusOf (yOf T) = T.1 :=
    fun T => Classical.choose_spec T.2
  let kOf : d.GammaTorus → Ty := fun T => ⟨⟨_, hlt (yOf T)⟩, yOf T, (hyOf T).1, rfl⟩
  have hdim : ∀ (k : Ty) (T : d.GammaTorus), kOf T = k →
      Module.finrank F (movedSub (rep k)) = Module.finrank F (movedSub (yOf T)) := by
    rintro k T rfl
    exact (hrep _).2
  choose g hgA hgS using fun (k : Ty) (T : d.GammaTorus) (hT : kOf T = k) =>
    exists_conj_torusBarFbar (rep k) (yOf T) (hrep k).1 (hyOf T).1 (hdim k T hT)
  have hN : ∀ (k : Ty) (T : d.GammaTorus) (hT : kOf T = k) (σ : GalF F),
      (g k T hT)⁻¹ * galGL d.m σ (g k T hT) ∈ d.normalizerBar (rep k) := fun k T hT σ =>
    ⟨inv_mul_galGL_mem_normalizer (galGL_mem_torusBarFbar _) (galGL_mem_torusBarFbar _)
      (hgS k T hT) σ, inv_mul_galGL_mem isGalStable_range_specMatFbar (hgA k T hT) σ⟩
  let φ : (k : Ty) → (T : d.GammaTorus) → kOf T = k → H1 (d.normalizerBar (rep k)) :=
    fun k T hT => H1.mk (conjCocycle (g k T hT) (hN k T hT))
  have hφ : ∀ (k k' : Ty) (hk : k = k') (T : d.GammaTorus) (hT : kOf T = k),
      (⟨k, φ k T hT⟩ : (k : Ty) × H1 (d.normalizerBar (rep k))) = ⟨k', φ k' T (hT.trans hk)⟩ := by
    rintro k k' rfl T hT
    rfl
  let f : GammaClass d → (k : Ty) × H1 (d.normalizerBar (rep k)) := fun c =>
    ⟨kOf (Quot.out c), φ _ (Quot.out c) rfl⟩
  refine Finite.of_injective f fun c₁ c₂ hf => ?_
  set T₁ := Quot.out c₁
  set T₂ := Quot.out c₂
  have hk : kOf T₁ = kOf T₂ := congrArg Sigma.fst hf
  have hf' : (⟨kOf T₂, φ (kOf T₂) T₁ hk⟩ : (k : Ty) × H1 (d.normalizerBar (rep k))) =
      ⟨kOf T₂, φ (kOf T₂) T₂ rfl⟩ := (hφ _ _ hk T₁ rfl).symm.trans hf
  have hH := eq_of_heq (Sigma.mk.inj_iff.mp hf').2
  obtain ⟨t, ht⟩ := exists_conj_torusOf_of_H1 (hgA _ T₁ hk) (hgA _ T₂ rfl) (hgS _ T₁ hk)
    (hgS _ T₂ rfl) (hN _ T₁ hk) (hN _ T₂ rfl) hH
  have hc : d.TorusConj T₂ T₁ := ⟨t, by rw [← (hyOf T₁).2, ← (hyOf T₂).2]; exact ht⟩
  rw [← Quot.out_eq c₁, ← Quot.out_eq c₂]
  exact (Quot.sound hc).symm


end GSpinGGP
