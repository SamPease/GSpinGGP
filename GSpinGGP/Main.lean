import GSpinGGP.GGP.Triple
import GSpinGGP.TraceFormula.Spine
import GSpinGGP.Literature.HarishChandra
import GSpinGGP.Literature.GSpin
import GSpinGGP.Literature.Kottwitz
import GSpinGGP.Literature.Hilbert90
import GSpinGGP.GGP.TwistDescent
import GSpinGGP.GGP.QuadClassify

/-!
# The main theorem: the local GGP conjecture for general spin groups

Layer 3.  The deduction of the main theorem (Thesis Thm. 6.4.1 (= Thm. 1.0.1))
from the multiplicity formula (Thesis Thm. 7.2.2 (= Thm. 1.0.2)), following
Thesis §6.6–6.7, with the inner forms indexed by `H¹(F, SO(W))` and the Kottwitz-sign
cancellation of Thesis §6.7 replaced by `signed_count`.

## The argument

For a family of tempered packets `Π_α` on the inner forms `G_α` (STAB, TRANS, WHITT):

1. `packet_sum_mult`: `Σ_{π ∈ Π_α} m(π) = m_geom(θ_α)`, `θ_α = Σ_{π∈Π_α} θ_π`
   (multiplicity formula + linearity of `m_geom`);
2. `packet_germ_transfer`: germs of `θ_α` at `y` equal `e(G_α)` times germs of `θ_1` at any
   strongly stably conjugate `x` (STAB, TRANS, BP (12.1.2));
3. `gammaIntegrand_eq_zero_of_not_qd`: only classes with `G_x` quasi-split contribute
   (BP Prop. 4.5.1(i), via the GSpin regular-orbit criterion);
4. `stable_rearrangement` (Thesis (6.7.5)): `Σ_α m_geom(θ_α)` is the
   `Γ(G,H)`-integral of `c_{θ_1}` weighted by `Σ_α e(G_α) n_α(x) / n_1(x)` (Prop. 6.6.1(i),(ii));
5. `signed_count`: `Σ_α e(G_α) n_α(x) = [x central]` (replaces the Kottwitz-sign
   cancellation of Thesis §6.7; Galois cohomology is not modelled);
6. `sum_mult_eq_germ_one` (Thesis (6.7.7)): `Σ_α Σ_π m(π) = c_{θ_1, O_1}(1)`;
7. `sum_mult_eq_one` (Thesis (6.7.1)): `= 1`, by Rodier (BP Prop. 4.8.1(i)) and WHITT;
8. `local_ggp`: exactly one member has `m(π) = 1`, all others `0` (a genuine proof from 7 and
   `m(π) ≠ ∞`).

Own-work statements that are not yet proved are `sorry`; cited results are the axioms of
`Literature/`.
-/

noncomputable section

open MeasureTheory Filter Topology Module
open CliffordAlgebra (ι_injective)
open scoped Classical

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (ψ : NontrivialAddChar F)

/-! ## 1. The multiplicity formula (the dissertation's own result) -/

/-- **The multiplicity formula** (Thesis Thm. 7.2.2 (= Thm. 1.0.2)): for every GGP
triple of general spin groups and every irreducible tempered `π` with central character trivial
on `Z_{G,H}(F)`, `m(π) < ∞` and `m(π) = m_geom(θ_π)`.  This is the dissertation's own result; its
proof is the local trace formula (Thesis Ch. 7–12): `multiplicityFormula_of_traceFormula`
(`TraceFormula/Spine.lean`) proves it by the strong induction on `dim G` of Thesis §7.2, from
the geometric expansion (Thesis Thm 12.2.1), the elliptic form of Thesis Prop 7.4.1(ii), and
elliptic isolation (BP Cor 5.7.2(i)), which are stated there and not yet proved. -/
theorem multiplicity_formula : MultiplicityFormula F ψ := multiplicityFormula_of_traceFormula ψ

/-- `m(π) ≠ ∞` for the members of a packet (first half of `multiplicity_formula`). -/
theorem mult_ne_top {d : GGPData F} {IF : InnerFormSystem d} (P : TemperedPacketFamily d IF)
    (α : IF.Idx) (i : P.ι α) : mult ψ (IF.data α) (P.rep α i) ≠ ⊤ :=
  (multiplicity_formula ψ (IF.data α) (P.rep α i) (P.tempered α i) (P.central_trivial α i)).1

/-! ## 2. Finiteness of the set of inner forms -/

/-- The index set `H¹(F, SO(W))` of the inner forms is finite (it has at most two
elements, `padic_quadratic_classes`).  Proof: `Fin n → IF.Idx`, `i ↦` the unique `α` with
`R_i ≅ W_α`, is surjective by `IF.classify` and the uniqueness in `padic_quadratic_classes`. -/
theorem InnerFormSystem.finite_idx {d : GGPData F} (IF : InnerFormSystem d) : Finite IF.Idx := by
  obtain ⟨n, R, -, -, hR, huniq, -⟩ := padic_quadratic_classes d.QW d.nondeg
  let f : Fin n → IF.Idx := fun i => (IF.classify (R i) (hR i).1 (hR i).2).exists.choose
  refine Finite.of_surjective f fun α => ?_
  obtain ⟨i, hi, -⟩ := huniq (IF.twist α).Q' (IF.twist α).nondeg' (IF.twist α).sameDisc
  refine ⟨i, ?_⟩
  have hspec := (IF.classify (R i) (hR i).1 (hR i).2)
  obtain ⟨e⟩ := hi
  exact hspec.unique hspec.exists.choose_spec ⟨e.symm⟩

/-! ## 3. Strongly stable classes in `Γ(G_α, H_α)` and the counts `n_α(x)` (Thesis §6.6–6.7) -/

section Counts

variable {d : GGPData F}

/-- The elements `y ∈ Γ(G_α, H_α)` (representatives in `GSpin(W_α)(F)`) strongly stably
conjugate to `x ∈ GSpin(W)(F)` (Thesis §6.7, definition of `n_α(x)`). -/
def stableFiber (IF : InnerFormSystem d) (α : IF.Idx) (x : ↥(GSpin d.QW)) :
    Set ↥(GSpin (IF.data α).QW) :=
  {y | (IF.data α).IsGammaElt y ∧ d.StronglyStablyConjW (IF.twist α) x y}

/-- `GSpin(W_α)(F)`-conjugacy on `stableFiber` (by Thesis §6.6, two
elements of `GSpin(W_α)` are `G_α(F)`-conjugate iff they are `GSpin(W_α)(F)`-conjugate). -/
def stableFiberConj (IF : InnerFormSystem d) (α : IF.Idx) (x : ↥(GSpin d.QW))
    (y y' : stableFiber IF α x) : Prop :=
  ∃ g : ↥(GSpin (IF.data α).QW), (y' : ↥(GSpin (IF.data α).QW)) = g * y * g⁻¹

/-- `n_α(x) = |{y ∈ Γ(G_α, H_α) : y ∼_stab x}|` (Thesis §6.7): the number of
`GSpin(W_α)(F)`-conjugacy classes of elements of `Γ(G_α,H_α)` strongly stably conjugate to `x`.
(`Nat.card` is `0` on an infinite set; the set is finite, being in bijection with a subset of
`H¹(F, S_x)`, but this is not used.) -/
def n_alpha (IF : InnerFormSystem d) (α : IF.Idx) (x : ↥(GSpin d.QW)) : ℕ :=
  Nat.card (Quot (stableFiberConj IF α x))

/-- The signed count `Σ_α e(G_α) n_α(x)` of Thesis (6.7.6) (a finite sum,
`InnerFormSystem.finite_idx`). -/
def signedCount (IF : InnerFormSystem d) (x : ↥(GSpin d.QW)) : ℤ :=
  ∑ᶠ α : IF.Idx, kottwitzSign d (IF.twist α) * (n_alpha IF α x : ℤ)

/-- `x ∈ GSpin(W)(F)` is central in `G`, i.e. a scalar `c ∈ F^× = A_{G,H}(F)`: its class is the
atom `1` of `Γ(G,H)`. -/
def IsCentralW (d : GGPData F) (x : ↥(GSpin d.QW)) : Prop :=
  x ∈ (scalarGSpin d.QW).range

/-- `G'_x` is quasi-split: `W'_x` and `V'_x = W'_x ⊕ Z` are quasi-split.  For
`x ∈ Γ(G,H)` the moved part `G''_x` is a torus, so this is equivalent to `G_x` quasi-split
(`isQdAt_iff_nilReg_nonempty`); for general semisimple `x` it is strictly weaker. -/
def IsQdAt (d : GGPData F) (x : ↥(GSpin d.QW)) : Prop :=
  IsQuasiSplitQF (d.QWfix x) ∧ IsQuasiSplitQF (d.QVfix x)

/-! ### Bookkeeping at central elements (own work; used by `mGeomStabS_eq_germ_one` and
`orbitChoice_one_mem_nilReg`) -/

/-- `W'_1 = W`: the identity fixes everything. -/
theorem fixedSub_one_eq_top {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V) :
    fixedSub (1 : GSpin Q) = ⊤ := by
  rw [fixedSub, map_one]
  ext v
  simp

/-- `W'_x = W` when `P(x) = 1`. -/
theorem fixedSub_eq_top_of {V : Type*} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
    (x : GSpin Q) (h : specP Q x = 1) : fixedSub x = ⊤ := by
  rw [fixedSub, h]
  ext v
  simp

/-- `W'_c = W` for central scalars `c` (`P(c) = 1`). -/
theorem fixedSub_scalar (c : Fˣ) : fixedSub (scalarGSpin d.QW c) = ⊤ := by
  rw [fixedSub, specP_scalarGSpin]
  ext v
  simp

/-- Quasi-splitness (`dim V ≤ 2 w(V) + 2`) is invariant under isometries. -/
theorem isQuasiSplitQF_of_isometry {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁]
    [AddCommGroup V₂] [Module F V₂] (Q₁ : QuadraticForm F V₁) (Q₂ : QuadraticForm F V₂)
    (e : V₁ ≃ₗ[F] V₂) (he : ∀ v, Q₂ (e v) = Q₁ v) (h : IsQuasiSplitQF Q₁) :
    IsQuasiSplitQF Q₂ := by
  have hw : wittIndex Q₁ = wittIndex Q₂ := by
    unfold wittIndex
    congr 1
    ext n
    constructor
    · rintro ⟨U, hU, rfl⟩
      refine ⟨U.map (e : V₁ →ₗ[F] V₂), ?_, LinearEquiv.finrank_map_eq e U⟩
      rintro _ ⟨u, hu, rfl⟩
      simpa [he] using hU u hu
    · rintro ⟨U, hU, rfl⟩
      refine ⟨U.map (e.symm : V₂ →ₗ[F] V₁), ?_, LinearEquiv.finrank_map_eq e.symm U⟩
      rintro _ ⟨u, hu, rfl⟩
      have := he (e.symm u)
      simp only [LinearEquiv.apply_symm_apply] at this
      simpa [← this] using hU u hu
  unfold IsQuasiSplitQF at h ⊢
  rw [← LinearEquiv.finrank_eq e, ← hw]
  exact h

/-- If `W'_x = W` (e.g. `x` central) and `G` is quasi-split, then `IsQdAt d x`, since `W'_x ≅ W` and `V'_x ≅ V`. -/
theorem isQdAt_of_fixedSub_eq_top (d : GGPData F) (hqs : d.IsQuasiSplit) (x : ↥(GSpin d.QW))
    (hx : fixedSub x = ⊤) : IsQdAt d x := by
  let e : ↥(fixedSub x) ≃ₗ[F] (Fin d.m → F) := LinearEquiv.ofTop _ hx
  refine ⟨isQuasiSplitQF_of_isometry d.QW _ e.symm (fun v => ?_) hqs.1,
    isQuasiSplitQF_of_isometry d.QV _ (e.symm.prodCongr (LinearEquiv.refl F d.Z))
      (fun v => ?_) hqs.2⟩
  · show d.QW (e (e.symm v)) = d.QW v
    rw [LinearEquiv.apply_symm_apply]
  · show d.QW (e (e.symm v.1)) + d.QZ v.2 = d.QW v.1 + d.QZ v.2
    rw [LinearEquiv.apply_symm_apply]

/-- `MovedPartAbelian` at `x = 1` (the moved part is `0`): an element of `gspin(W)` commuting with all of `ι(W)` commutes with the whole Clifford algebra, which `ι(W)` generates. -/
theorem movedPartAbelian_one (d : GGPData F) : MovedPartAbelian d.QW 1 := by
  intro X _ Y _ hX _
  have hc : ∀ Z : CliffordAlgebra d.QW, X * Z = Z * X := by
    intro Z
    induction Z using CliffordAlgebra.induction with
    | algebraMap r => exact (Algebra.commutes r X).symm
    | ι v =>
      have := hX v (by rw [fixedSub_one_eq_top]; trivial)
      rw [Ring.lie_def, sub_eq_zero] at this
      exact this
    | mul a b ha hb => rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]
    | add a b ha hb => rw [mul_add, add_mul, ha, hb]
  rw [Ring.lie_def, hc Y, sub_self]

/-- `1 ∈ GSpin(W)` is semisimple. -/
theorem isSS_one_W (d : GGPData F) :
    IsSS F (((1 : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) := by
  show Module.End.IsSemisimple (LinearMap.mulLeft F (1 : CliffordAlgebra d.QW))
  rw [LinearMap.mulLeft_one]
  exact Module.End.isSemisimple_id

-- stand-ins for Main's definitions
variable {d : GGPData F}

/-- Central scalars `c ∈ GSpin(W)` are semisimple (left multiplication is `c · id`). -/
theorem isSS_scalar (c : Fˣ) :
    IsSS F (((scalarGSpin d.QW c : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) :
      CliffordAlgebra d.QW) := by
  show Module.End.IsSemisimple (LinearMap.mulLeft F (algebraMap F (CliffordAlgebra d.QW) (c : F)))
  have : LinearMap.mulLeft F (algebraMap F (CliffordAlgebra d.QW) (c : F)) =
      (c : F) • LinearMap.id := by
    ext a; simp [Algebra.smul_def]
  rw [this]
  exact Module.End.IsSemisimple_smul _ Module.End.isSemisimple_id

/-- `T_1 = {g ∈ GSpin(W) | P(g) = 1}` (`= A_{G,H}` by `ker_specP`). -/
theorem mem_torusOf_one_iff (g : ↥(GSpin d.QW)) : g ∈ d.torusOf 1 ↔ specP d.QW g = 1 := by
  rw [GGPData.torusOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  simp only [one_mul, mul_one, true_and]
  constructor
  · intro h
    refine LinearEquiv.ext fun w => ?_
    exact h w (by rw [fixedSub_one_eq_top]; trivial)
  · intro h w _
    rw [h]; rfl

/-- Every central `t = c ∈ F^×` has the torus `T_t = T_1`. -/
theorem torusOf_eq_one_of_central (t : ↥(GSpin d.QW)) (ht : IsCentralW d t) :
    d.torusOf t = d.torusOf 1 := by
  obtain ⟨c, rfl⟩ := ht
  ext g
  rw [GGPData.torusOf, GGPData.torusOf, Subgroup.mem_inf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    fixedSub_scalar, fixedSub_one_eq_top, one_mul, mul_one]
  exact and_congr_left fun _ => iff_of_true (scalarGSpin_commute d.QW c g).eq.symm rfl

/-- `1 ∈ Γ(G,H)`: `T_1 = F^×` (by `ker_specP`) is commutative and `T_1/A_{G,H}` is a point. -/
theorem isGammaElt_one : d.IsGammaElt 1 := by
  have hker : ∀ g ∈ d.torusOf 1, g ∈ (scalarGSpin d.QW).range := by
    intro g hg
    rw [← ker_specP d.nondeg]
    exact (mem_torusOf_one_iff g).1 hg
  refine ⟨isSS_one_W d, fun a ha b hb => ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := hker a ha
    exact scalarGSpin_commute d.QW c b
  · have : Subsingleton (d.TorusQuot (d.torusOf 1)) := by
      refine ⟨fun x y => ?_⟩
      induction x using QuotientGroup.induction_on with | H a => ?_
      induction y using QuotientGroup.induction_on with | H b => ?_
      rw [QuotientGroup.eq]
      obtain ⟨c, hc⟩ := hker _ (a⁻¹ * b).2
      exact Subgroup.mem_subgroupOf.mpr ⟨c, hc⟩
    exact Finite.compactSpace

/-- Central scalars lie in `Γ(G,H)`. -/
theorem isGammaElt_of_central (t : ↥(GSpin d.QW)) (ht : IsCentralW d t) : d.IsGammaElt t := by
  have h1 := (isGammaElt_one (d := d))
  rw [GGPData.IsGammaElt, torusOf_eq_one_of_central t ht]
  obtain ⟨c, rfl⟩ := ht
  exact ⟨isSS_scalar c, h1.2⟩

/-- The atom `[T_1] ∈ GammaClass d` of `Γ(G,H)`. -/
def atomClass (d : GGPData F) : GammaClass d :=
  Quot.mk _ ⟨d.torusOf 1, 1, isGammaElt_one, rfl⟩

/-- `T_1` is normal: a conjugate `gTg⁻¹` equals `T_1` iff `T = T_1`. -/
theorem torusOf_one_conj (g : ↥(GSpin d.QW)) (T : Subgroup ↥(GSpin d.QW)) :
    T.map (MulAut.conj g).toMonoidHom = d.torusOf 1 ↔ T = d.torusOf 1 := by
  have key : ∀ x : ↥(GSpin d.QW), specP d.QW (g * x * g⁻¹) = 1 ↔ specP d.QW x = 1 := by
    intro x
    rw [map_mul, map_mul, map_inv]
    constructor
    · intro h
      have := congrArg (fun y => (specP d.QW g)⁻¹ * y * specP d.QW g) h
      simpa [mul_assoc] using this
    · intro h; rw [h, mul_one, mul_inv_cancel]
  constructor
  · intro h
    ext x
    rw [mem_torusOf_one_iff, ← key, ← mem_torusOf_one_iff, ← h]
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := by
        simpa [MulAut.conj_apply] using hyx
      rw [← this]; exact hy
  · rintro rfl
    ext x
    rw [mem_torusOf_one_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, mem_torusOf_one_iff] at hy
      show specP d.QW (g * y * g⁻¹) = 1
      rw [key]; exact hy
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      rw [SetLike.mem_coe, mem_torusOf_one_iff, ← key]
      simpa [mul_assoc] using hx

/-- The chosen representative of the atom class is `T_1` itself. -/
theorem out_atomClass : (Quot.out (atomClass d)).1 = d.torusOf 1 := by
  have h := Quot.eqvGen_exact (Quot.out_eq (atomClass d))
  suffices H : ∀ T T' : d.GammaTorus, Relation.EqvGen d.TorusConj T T' →
      (T.1 = d.torusOf 1 ↔ T'.1 = d.torusOf 1) from (H _ _ h).2 rfl
  intro T T' hTT'
  induction hTT' with
  | rel T T' hr =>
    obtain ⟨g, hg⟩ := hr
    rw [hg, torusOf_one_conj]
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- The atom is the only class whose representative torus is `T_1`. -/
theorem atomClass_unique (c : GammaClass d) (hc : (Quot.out c).1 = d.torusOf 1) :
    c = atomClass d := by
  have : Quot.out c = Quot.out (atomClass d) := Subtype.ext (hc.trans out_atomClass.symm)
  rw [← Quot.out_eq c, ← Quot.out_eq (atomClass d), this]

/-- `|W(T_1)| = 1`: `T_1 = A_{G,H}` consists of central scalars (`ker_specP`), so every element of
its normalizer centralizes it and `W(T_1) = N(T_1)/Z(T_1)` is trivial. -/
theorem weylCardOf_torusOf_one : weylCardOf d (d.torusOf 1) = 1 := by
  have hcomm : ∀ g : ↥(GSpin d.QW),
      g ∈ Subgroup.centralizer ((d.torusOf 1 : Subgroup ↥(GSpin d.QW)) : Set ↥(GSpin d.QW)) := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hs : h ∈ (scalarGSpin d.QW).range := by
      rw [← ker_specP d.nondeg]
      exact (mem_torusOf_one_iff _).1 hh
    obtain ⟨c, rfl⟩ := hs
    exact (scalarGSpin_commute d.QW c g).eq
  unfold weylCardOf
  refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
  induction a using QuotientGroup.induction_on with | H a => ?_
  induction b using QuotientGroup.induction_on with | H b => ?_
  rw [QuotientGroup.eq]
  exact Subgroup.mem_subgroupOf.mpr (hcomm _)

/-- `T_1(F)/A_{G,H}(F)` is a point (by `ker_specP`). -/
theorem torusQuot_one_subsingleton : Subsingleton (d.TorusQuot (d.torusOf 1)) := by
  refine ⟨fun x y => ?_⟩
  induction x using QuotientGroup.induction_on with | H a => ?_
  induction y using QuotientGroup.induction_on with | H b => ?_
  rw [QuotientGroup.eq]
  have : ((a⁻¹ * b : ↥(d.torusOf 1)) : ↥(GSpin d.QW)) ∈ (scalarGSpin d.QW).range := by
    rw [← ker_specP d.nondeg]
    exact (mem_torusOf_one_iff _).1 (a⁻¹ * b).2
  obtain ⟨c, hc⟩ := this
  exact Subgroup.mem_subgroupOf.mpr ⟨c, hc⟩

/-- The probability-Haar integral over the point `T_1(F)/A_{G,H}(F)` is evaluation. -/
theorem integral_probHaar_torusQuot_one (f : d.TorusQuot (d.torusOf 1) → ℂ) :
    (letI : MeasurableSpace (d.TorusQuot (d.torusOf 1)) := borel _
     haveI : BorelSpace (d.TorusQuot (d.torusOf 1)) := ⟨rfl⟩
     ∫ q, f q ∂(probHaar (d.TorusQuot (d.torusOf 1)))) = f 1 := by
  let _ : MeasurableSpace (d.TorusQuot (d.torusOf 1)) := borel _
  have _ : BorelSpace (d.TorusQuot (d.torusOf 1)) := ⟨rfl⟩
  have := torusQuot_one_subsingleton (d := d)
  have : CompactSpace (d.TorusQuot (d.torusOf 1)) := Finite.compactSpace
  have hf : f = fun _ => f 1 := funext fun q => congrArg f (Subsingleton.elim _ _)
  rw [hf, integral_const]
  have hμ : probHaar (d.TorusQuot (d.torusOf 1)) Set.univ = 1 := by
    unfold probHaar
    rw [dite_eq_left ‹_›]
    exact Measure.haarMeasure_self
  simp [Measure.real, hμ]

/-- A central scalar `c` of `GSpin(W)` embeds diagonally as the scalar `c` of the ambient algebra. -/
theorem diag_central_commute (t : ↥(GSpin d.QW)) (ht : IsCentralW d t) (a : d.ambient) :
    (((d.diag t : d.G) : d.ambientˣ) : d.ambient) * a =
      a * (((d.diag t : d.G) : d.ambientˣ) : d.ambient) := by
  obtain ⟨c, rfl⟩ := ht
  have h : (((d.diag (scalarGSpin d.QW c) : d.G) : d.ambientˣ) : d.ambient) =
      algebraMap F d.ambient (c : F) := by
    refine Prod.ext ?_ ?_
    · rfl
    · show CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
          (algebraMap F (CliffordAlgebra d.QW) (c : F)) = _
      exact AlgHom.commutes _ _
  rw [h]
  exact Algebra.commutes _ _

/-- `D^G(z) = 1` for central `z`: `Ad z = 1`, so the trailing coefficient is that of `X^{dim 𝔤}`. -/
theorem weylDisc_of_central (𝔤 : LieSubalgebra F d.ambient) (x : d.ambientˣ)
    (hx : ∀ a : d.ambient, (x : d.ambient) * a = a * x) : weylDisc 𝔤 x = 1 := by
  have hid : ∀ X, conjAd F x X = X := by
    intro X
    show (x : d.ambient) * X * (↑x⁻¹ : d.ambient) = X
    rw [hx X, mul_assoc, Units.mul_inv, mul_one]
  have hst : ∀ X ∈ 𝔤.toSubmodule, conjAd F x X ∈ 𝔤.toSubmodule := fun X hX => by
    rw [hid]; exact hX
  unfold weylDisc
  rw [dite_eq_left hst]
  have h0 : (1 - (conjAd F x).toLinearEquiv.toLinearMap.restrict hst) = 0 := by
    refine LinearMap.ext fun X => Subtype.ext ?_
    simp only [LinearMap.sub_apply, Module.End.one_apply, Submodule.coe_sub,
      LinearMap.zero_apply, Submodule.coe_zero]
    exact sub_eq_zero.2 (hid X).symm
  have htc : ∀ n : ℕ, (Polynomial.X ^ n : Polynomial F).trailingCoeff = 1 := fun n => by
    rw [← Polynomial.monomial_one_right_eq_X_pow, Polynomial.trailingCoeff,
      Polynomial.natTrailingDegree_monomial one_ne_zero, Polynomial.coeff_monomial_same]
  rw [h0, LinearMap.charpoly_zero, htc, absF_of_ne_zero one_ne_zero]
  simp

/-- At a central `t`, `D^G(t)^{1/2} = Δ(t)^{s-1/2} = 1`, so the `Γ`-integrand on `T_1` is the germ `c_{θ,O_t}(t)`. -/
theorem gammaIntegrand_central (θ : ↥d.G → ℂ) (s : ℝ) (t : ↥(GSpin d.QW))
    (ht : IsCentralW d t) :
    gammaIntegrand ψ d θ (d.torusOf 1) s t = germ d.G d.lie d.bilin ψ θ (d.diag t) (orbitChoice d t) := by
  rw [gammaIntegrand, ite_eq_left ⟨isGammaElt_of_central t ht, torusOf_eq_one_of_central t ht⟩,
    weylDisc_of_central _ _ (diag_central_commute t ht)]
  obtain ⟨c, rfl⟩ := ht
  have hΔ : deltaGGP d (scalarGSpin d.QW c) = 1 := by
    rw [← mul_one (scalarGSpin d.QW c), deltaGGP_scalar_mul, deltaGGP_one]
  rw [hΔ, Real.one_rpow]
  simp

/-- The base change `C(Q) → C(Q_{F̄})` is injective (`F̄` is flat over `F`). -/
theorem bcHom_injective {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V) :
    Function.Injective (bcHom Q) := by
  have h1 : Function.Injective (CliffordAlgebra.ofBaseChange (AlgebraicClosure F) Q) := by
    intro a b hab
    have := congrArg (CliffordAlgebra.toBaseChange (AlgebraicClosure F) Q) hab
    simpa using this
  exact h1.comp (Algebra.TensorProduct.includeRight_injective (algebraMap F _).injective)

/-- Base change sends the scalar `c` to the scalar `c`. -/
theorem bcHom_algebraMap {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)
    (c : F) : bcHom Q (algebraMap F _ c) =
      algebraMap (AlgebraicClosure F) _ (algebraMap F (AlgebraicClosure F) c) := by
  simp only [bcHom, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    ← algebraMap_smul (AlgebraicClosure F) c, ← Algebra.TensorProduct.one_def, map_smul, map_one,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]

/-- Anything stably conjugate (through any `φ`) to a scalar `c` is `c`: after base change, `C(φ)` and
conjugation fix the scalar `c`, and base change is injective. -/
theorem eq_scalar_of_stablyConjVia {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁]
    [AddCommGroup V₂] [Module F V₂] {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}
    (φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F)))
    (c : Fˣ) (y : GSpin Q₂)
    (h : StablyConjVia φ ((scalarGSpin Q₁ c : GSpin Q₁) : (CliffordAlgebra Q₁)ˣ)
      ((y : GSpin Q₂) : (CliffordAlgebra Q₂)ˣ)) :
    y = scalarGSpin Q₂ c := by
  obtain ⟨g, -, hg⟩ := h
  have hval := congrArg Units.val hg
  simp only [Units.val_mul, cliffUnits, bcUnits, Units.coe_map, MonoidHom.coe_ofClass,
    RingHom.toMonoidHom_eq_coe] at hval
  have hs : ((scalarGSpin Q₁ c : GSpin Q₁) : (CliffordAlgebra Q₁)ˣ).val =
      algebraMap F _ (c : F) := rfl
  have hm : ∀ a : AlgebraicClosure F, (CliffordAlgebra.map φ.toIsometry).toRingHom
      (algebraMap (AlgebraicClosure F) _ a) = algebraMap (AlgebraicClosure F) _ a :=
    fun a => AlgHom.commutes _ a
  rw [hs, bcHom_algebraMap, hm, ← Algebra.commutes, mul_assoc, Units.mul_inv,
    mul_one] at hval
  have hs2 : ((scalarGSpin Q₂ c : GSpin Q₂) : (CliffordAlgebra Q₂)ˣ).val =
      algebraMap F _ (c : F) := rfl
  apply Subtype.ext
  apply Units.ext
  apply bcHom_injective Q₂
  rw [hs2, bcHom_algebraMap]
  exact hval.symm

/-- The scalar `c` is strongly stably conjugate to itself through the trivial twist (`g = 1`). -/
theorem scalar_stronglyStablyConjW_refl (τ : InnerTwist d.QW) (hτ : τ = d.reflTwist) (c : Fˣ) :
    d.StronglyStablyConjW τ (scalarGSpin d.QW c) (scalarGSpin (d.twist τ).QW c) := by
  subst hτ
  have hW : CliffordAlgebra.map (d.reflTwist.φ).toIsometry = AlgHom.id _ _ :=
    CliffordAlgebra.map_id _
  have hV : CliffordAlgebra.map (d.twistV d.reflTwist).toIsometry = AlgHom.id _ _ := by
    rw [← CliffordAlgebra.map_id]
    congr 1
    ext v
    show (prodBaseChange d.QW d.QZ).symm ((d.reflTwist.φ.prod
      (QuadraticMap.IsometryEquiv.refl (d.QZ.baseChange (AlgebraicClosure F))))
      (prodBaseChange d.QW d.QZ v)) = v
    exact (prodBaseChange d.QW d.QZ).symm_apply_apply v
  have hcW : ∀ z, cliffUnits d.reflTwist.φ z = z := fun z => Units.ext (by
    simp only [cliffUnits, hW]; rfl)
  have hcV : ∀ z, cliffUnits (d.twistV d.reflTwist) z = z := fun z => Units.ext (by
    simp only [cliffUnits, hV]; rfl)
  refine ⟨⟨1, Subgroup.one_mem _, ?_, fun σ z _ _ => ?_⟩, ⟨1, Subgroup.one_mem _, ?_, fun σ z _ _ => ?_⟩⟩
  · rw [hcW, inv_one, mul_one]; exact one_mul _
  · rw [hcW, hW]
    show galC d.QW σ ((1 * z * 1⁻¹ : (CliffordAlgebra (d.QW.baseChange (AlgebraicClosure F)))ˣ) :
      CliffordAlgebra (d.QW.baseChange (AlgebraicClosure F))) = _
    simp only [mul_one, one_mul, inv_one, Units.val_one]
    rfl
  · rw [hcV, inv_one, mul_one]; exact one_mul _
  · rw [hcV, hV]
    show galC d.QV σ ((1 * z * 1⁻¹ : (CliffordAlgebra (d.QV.baseChange (AlgebraicClosure F)))ˣ) :
      CliffordAlgebra (d.QV.baseChange (AlgebraicClosure F))) = _
    simp only [mul_one, one_mul, inv_one, Units.val_one]
    rfl

/-- **`n_1(c) = 1` for central `c`** (own work; Thesis §6.7, where the atom
contributes with weight `1`): anything strongly stably conjugate to the scalar `c` is `c`
(`eq_scalar_of_stablyConjVia`), and `c` is strongly stably conjugate to itself through the trivial
twist (`scalar_stronglyStablyConjW_refl`). -/
theorem n_alpha_base_of_central (IF : InnerFormSystem d) (t : ↥(GSpin d.QW))
    (ht : IsCentralW d t) : n_alpha IF IF.base t = 1 := by
  obtain ⟨c, rfl⟩ := ht
  have huniq : ∀ y : stableFiber IF IF.base (scalarGSpin d.QW c),
      (y : ↥(GSpin (IF.data IF.base).QW)) = scalarGSpin (IF.data IF.base).QW c :=
    fun y => by
      obtain ⟨g, hg, heq, -⟩ := y.2.2.1
      exact eq_scalar_of_stablyConjVia _ c _ ⟨g, hg, heq⟩
  have hmem : scalarGSpin (IF.data IF.base).QW c ∈ stableFiber IF IF.base (scalarGSpin d.QW c) :=
    ⟨isGammaElt_of_central _ ⟨c, rfl⟩,
      scalar_stronglyStablyConjW_refl (IF.twist IF.base) IF.twist_base c⟩
  unfold n_alpha
  refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => ?_⟩, ⟨Quot.mk _ ⟨_, hmem⟩⟩⟩
  induction a using Quot.ind with | mk a => ?_
  induction b using Quot.ind with | mk b => ?_
  have : a = b := Subtype.ext ((huniq a).trans (huniq b).symm)
  rw [this]

/-! ### The moved part on `Γ(G,H)` (helpers for `movedPartAbelian_of_isGammaElt`)

The exponential of a small element of `gspin(W)` lies in `GSpin(W)(F)`
(`MovedPart.exists_nhds_expA_mem_GSpin`): conjugation by `e^X` is `e^{ad X}` (computed in
`End(F^d)` via left and right multiplication), which preserves the `ad X`-stable closed subspace
`ι(W)`. -/

namespace MovedPart

variable {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A]
  [IsModuleTopology F A]

local notation "VA" => (Fin (Module.finrank F A) → F)

variable (F) in
/-- Right multiplication by `a`, transported to a continuous endomorphism of `F^d`. -/
def rmulPi (a : A) : VA →L[F] VA :=
  LinearMap.toContinuousLinearMap
    ((toPiCLE F A).toLinearEquiv.toLinearMap ∘ₗ LinearMap.mulRight F a ∘ₗ
      (toPiCLE F A).symm.toLinearEquiv.toLinearMap)

lemma rmulPi_apply (a : A) (v : VA) :
    rmulPi F a v = toPiCLE F A ((toPiCLE F A).symm v * a) := rfl

variable (F) in
/-- `a ↦ rmulPi a` as a linear map. -/
def rmulPiₗ : A →ₗ[F] (VA →L[F] VA) where
  toFun := rmulPi F
  map_add' a b := ContinuousLinearMap.ext fun v => by simp [rmulPi_apply, mul_add]
  map_smul' c a := ContinuousLinearMap.ext fun v => by simp [rmulPi_apply]

lemma continuous_rmulPi : Continuous (rmulPi F : A → VA →L[F] VA) :=
  IsModuleTopology.continuous_of_linearMap (rmulPiₗ F)

lemma rmulPi_mul (a b : A) : rmulPi F (a * b) = rmulPi F b * rmulPi F a :=
  ContinuousLinearMap.ext fun v => by simp [rmulPi_apply, mul_assoc]

lemma rmulPi_pow (a : A) (n : ℕ) : rmulPi F (a ^ n) = rmulPi F a ^ n := by
  induction n with
  | zero => ext v; simp [rmulPi_apply]
  | succ n ih => rw [pow_succ', rmulPi_mul, ih, pow_succ]

lemma commute_lmulPi_rmulPi (a b : A) : Commute (lmulPi F a) (rmulPi F b) := by
  ext v
  simp [lmulPi_apply, rmulPi_apply, mul_assoc]

lemma rmulPi_expA_neg_aux {X : A}
    (hs : HasSum (fun n : ℕ ↦ ((n.factorial : F)⁻¹) • (-X) ^ n) (expA F (-X))) :
    rmulPi F (expA F (-X)) = NormedSpace.exp (rmulPi F (-X)) := by
  have h2 := hs.map (rmulPiₗ F) (continuous_rmulPi (F := F))
  have hterm : ((rmulPiₗ F : A →ₗ[F] (VA →L[F] VA)) ∘
      fun n : ℕ ↦ ((n.factorial : F)⁻¹) • (-X) ^ n) =
      fun n ↦ ((n.factorial : F)⁻¹) • rmulPi F (-X) ^ n := by
    funext n
    simp only [Function.comp_apply, map_smul]
    rw [show (rmulPiₗ F) ((-X) ^ n) = rmulPi F ((-X) ^ n) from rfl, rmulPi_pow]
  rw [hterm] at h2
  rw [NormedSpace.exp_eq_tsum F]
  exact h2.tsum_eq.symm

/-- **`e^X r e^{-X}` stays in an `ad X`-stable subspace** for `X` near `0`: in `End(F^d)`,
`L_{e^X} R_{e^{-X}} = e^{L_X} e^{-R_X} = e^{L_X - R_X} = e^{ad X}` (left and right multiplications
commute), and `e^{ad X} r = ∑ (ad X)ⁿ r / n!` lies in the closed subspace `R`. -/
lemma exists_nhds_expA_conj_mem :
    ∃ U ∈ 𝓝 (0 : A), ∀ X ∈ U, ∀ R : Submodule F A, (∀ r ∈ R, X * r - r * X ∈ R) →
      ∀ r ∈ R, expA F X * r * expA F (-X) ∈ R := by
  let _ := isTopologicalRing_of_moduleTopology F A
  have _ := t2Space_of_moduleTopology F A
  obtain ⟨U₀, hU₀, hneg, h⟩ := expA_aux F (A := A)
  set B := Metric.eball (0 : VA →L[F] VA) (NormedSpace.expSeries F (VA →L[F] VA)).radius
  have hB0 : (0 : VA →L[F] VA) ∈ B := by
    rw [Metric.mem_eball, edist_self]
    exact expSeries_radius_pos_of_pAdic F (VA →L[F] VA)
  let adPi : A → (VA →L[F] VA) := fun X => lmulPi F X - rmulPi F X
  have hadc : Continuous adPi := (continuous_lmulPi F).sub (continuous_rmulPi (F := F))
  have hrc : Continuous fun X : A => rmulPi F (-X) := (continuous_rmulPi (F := F)).comp continuous_neg
  refine ⟨U₀ ∩ ((fun X : A => rmulPi F (-X)) ⁻¹' B) ∩ (adPi ⁻¹' B), ?_, ?_⟩
  · refine inter_mem (inter_mem hU₀ ?_) ?_
    · refine (Metric.isOpen_eball.preimage hrc).mem_nhds ?_
      show rmulPi F (-0 : A) ∈ B
      rw [neg_zero, show rmulPi F (0 : A) = 0 from map_zero (rmulPiₗ F)]
      exact hB0
    · refine (Metric.isOpen_eball.preimage hadc).mem_nhds ?_
      show lmulPi F (0 : A) - rmulPi F 0 ∈ B
      rw [show rmulPi F (0 : A) = 0 from map_zero (rmulPiₗ F),
        show lmulPi F (0 : A) = 0 from map_zero (lmulPiₗ F), sub_zero]
      exact hB0
  rintro X ⟨⟨hX0, hXr⟩, hXad⟩ R hR r hr
  obtain ⟨hb, -, he⟩ := h X hX0
  have hρ := rmulPi_expA_neg_aux (h (-X) (hneg X hX0)).2.1
  have hadd : NormedSpace.exp (lmulPi F X) * NormedSpace.exp (rmulPi F (-X)) =
      NormedSpace.exp (adPi X) := by
    rw [← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := F) (commute_lmulPi_rmulPi X (-X)) hb hXr]
    congr 1
    simp only [adPi, sub_eq_add_neg]
    rw [show rmulPi F (-X) = -rmulPi F X from map_neg (rmulPiₗ F) X]
  have hsum := NormedSpace.expSeries_hasSum_exp_of_mem_ball' (𝕂 := F) (adPi X) hXad
  have hsv := hsum.map (ContinuousLinearMap.apply F VA (toPiCLE F A r))
    (ContinuousLinearMap.apply F VA (toPiCLE F A r)).continuous
  set S : Submodule F VA := R.map (toPiCLE F A).toLinearEquiv.toLinearMap
  have hclosed : IsClosed (S : Set VA) := S.closed_of_finiteDimensional
  have hpow : ∀ n : ℕ, ∃ z ∈ R, (adPi X ^ n) (toPiCLE F A r) = toPiCLE F A z := by
    intro n
    induction n with
    | zero => exact ⟨r, hr, by simp⟩
    | succ n ih =>
      obtain ⟨z, hz, hzeq⟩ := ih
      refine ⟨X * z - z * X, hR z hz, ?_⟩
      rw [pow_succ', mul_apply_eq_comp, hzeq]
      simp [adPi, lmulPi_apply, rmulPi_apply, map_sub]
  have hmem : NormedSpace.exp (adPi X) (toPiCLE F A r) ∈ S := by
    refine hclosed.mem_of_tendsto hsv (Eventually.of_forall fun s => ?_)
    refine Submodule.sum_mem _ fun n _ => ?_
    simp only [Function.comp_apply, ContinuousLinearMap.apply_apply,
      smul_apply]
    obtain ⟨z, hz, hzeq⟩ := hpow n
    rw [hzeq]
    exact S.smul_mem _ ⟨z, hz, rfl⟩
  rw [← hadd, ← he, ← hρ, mul_apply_eq_comp, rmulPi_apply, lmulPi_apply] at hmem
  obtain ⟨z, hz, hzeq⟩ := hmem
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hzeq
  have := (toPiCLE F A).injective hzeq
  rw [mul_assoc, ← this]
  exact hz

/-- **`e^X ∈ GSpin(V)` for `X ∈ gspin(V)` near `0`**: `e^X` is a unit (inverse `e^{-X}`), even
(`e^X ∈ F[X] ⊆ C⁺(V)`), and conjugation by `e^{±X}` preserves `ι(V)`, which is `ad X`-stable
(`exists_nhds_expA_conj_mem`). -/
lemma exists_nhds_expA_mem_GSpin {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (Q : QuadraticForm F V) :
    ∃ U ∈ 𝓝 (0 : CliffordAlgebra Q), ∀ X ∈ U, X ∈ gspin Q →
      ∃ g : GSpin Q, (((g : (CliffordAlgebra Q)ˣ)) : CliffordAlgebra Q) = expA F X := by
  obtain ⟨U₁, hU₁, hconj⟩ := exists_nhds_expA_conj_mem (F := F) (A := CliffordAlgebra Q)
  obtain ⟨U₂, hU₂, hinv⟩ := expA_mul_expA_neg F (A := CliffordAlgebra Q)
  obtain ⟨U₃, hU₃, hadj⟩ := exists_nhds_expA_mem_adjoin F (A := CliffordAlgebra Q)
  have hneg : (fun X : CliffordAlgebra Q => -X) ⁻¹' (U₁ ∩ U₂) ∈ 𝓝 (0 : CliffordAlgebra Q) := by
    have hc : ContinuousAt (fun X : CliffordAlgebra Q => -X) 0 := continuous_neg.continuousAt
    exact hc.preimage_mem_nhds (by rw [neg_zero]; exact inter_mem hU₁ hU₂)
  refine ⟨U₁ ∩ U₂ ∩ U₃ ∩ (fun X : CliffordAlgebra Q => -X) ⁻¹' (U₁ ∩ U₂),
    inter_mem (inter_mem (inter_mem hU₁ hU₂) hU₃) hneg, ?_⟩
  rintro X ⟨⟨⟨hX1, hX2⟩, hX3⟩, ⟨hXn1, hXn2⟩⟩ hX
  have hXn : -X ∈ gspin Q := neg_mem hX
  have hR : ∀ Z ∈ gspin Q, ∀ r ∈ LinearMap.range (CliffordAlgebra.ι Q), Z * r - r * Z ∈ LinearMap.range (CliffordAlgebra.ι Q) := by
    rintro Z hZ _ ⟨v, rfl⟩
    rw [← Ring.lie_def]
    exact hZ.2 v
  have h1 : expA F X * expA F (-X) = 1 := hinv X hX2
  have h2 : expA F (-X) * expA F X = 1 := by
    simpa using hinv (-X) hXn2
  let u : (CliffordAlgebra Q)ˣ := ⟨expA F X, expA F (-X), h1, h2⟩
  have heven : expA F X ∈ CliffordAlgebra.even Q :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hX.1) (hadj X hX3)
  refine ⟨⟨u, heven, fun v => ?_, fun v => ?_⟩, rfl⟩
  · exact hconj X hX1 _ (hR X hX) _ ⟨v, rfl⟩
  · have := hconj (-X) hXn1 _ (hR (-X) hXn) _ ⟨v, rfl⟩
    rw [neg_neg] at this
    exact this

end MovedPart

/-- For `x ∈ Γ(G,H)` the moved part `G''_x` is a torus: `T_x(F) = Z(x) ∩ Fix(W'_x)`
is commutative, hence so is its Lie algebra
`so(W''_x)_{x̄} ⊕ F`.  Own work; this is the hypothesis under which
`nilReg_centralizer_nonempty_iff` applies.

Proof (exponential, no Zariski density): for `X, Y` in the moved part and `c ≠ 0` small, `e^{cX}`,
`e^{cY}` lie in `GSpin(W)(F)` (`MovedPart.exists_nhds_expA_mem_GSpin`), commute with `x` and fix
`W'_x` pointwise (`X`, `Y` commute with `x` and with `ι(W'_x)`), so they lie in `T_x(F)` and
commute.  Near `0` the centralizer of `e^Z` is that of `Z`
(`exists_nhds_commute_of_commute_expA`), so `cX` and `cY` commute.  Only the commutativity of
`T_x(F)` is used, not the semisimplicity of `x` or the compactness of `T_x(F)/A(F)`. -/
theorem movedPartAbelian_of_isGammaElt (d : GGPData F) (x : ↥(GSpin d.QW))
    (hx : d.IsGammaElt x) : MovedPartAbelian d.QW x := by
  intro X hX Y hY hXf hYf
  obtain ⟨U, hU, hG⟩ := MovedPart.exists_nhds_expA_mem_GSpin (F := F) d.QW
  obtain ⟨U', hU', hc⟩ := exists_nhds_commute_of_commute_expA F (A := CliffordAlgebra d.QW)
  have ht : ∀ Z : CliffordAlgebra d.QW, Tendsto (fun t : F => t • Z) (𝓝[≠] 0) (𝓝 0) := by
    intro Z
    have : Continuous (fun t : F => t • Z) := continuous_id.smul continuous_const
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨c, ⟨hcX, hcY⟩, hc0⟩ := ((((ht X).eventually (inter_mem hU hU')).and
    ((ht Y).eventually (inter_mem hU hU'))).and self_mem_nhdsWithin).exists
  -- `e^{cZ}` lies in `T_x` for `Z` in the moved part
  have key : ∀ Z ∈ lieCentralizer (gspin d.QW) ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
      (∀ v ∈ fixedSub x, ⁅Z, CliffordAlgebra.ι d.QW v⁆ = 0) → c • Z ∈ U →
      ∃ g ∈ d.torusOf x, (((g : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW) =
        expA F (c • Z) := by
    intro Z hZ hZf hcZ
    rw [mem_lieCentralizer] at hZ
    obtain ⟨g, hg⟩ := hG _ hcZ ((gspin d.QW).smul_mem c hZ.1)
    refine ⟨g, ⟨?_, fun w hw => ?_⟩, hg⟩
    · show g ∈ Subgroup.centralizer {x}
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxc : Commute ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) (c • Z) :=
        (Commute.smul_right hZ.2 c)
      have := commute_expA_of_commute (F := F) hxc
      rw [← hg] at this
      exact Subtype.ext (Units.ext this.eq.symm)
    · apply ι_injective d.QW
      rw [ι_specP]
      have hw0 := hZf w hw
      rw [Ring.lie_def, sub_eq_zero] at hw0
      have hwc : Commute (CliffordAlgebra.ι d.QW w) (c • Z) :=
        Commute.smul_right hw0.symm c
      have := (commute_expA_of_commute (F := F) hwc).eq
      rw [← hg] at this
      rw [← this, mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨g, hg, hge⟩ := key X hX hXf hcX.1
  obtain ⟨h, hh, hhe⟩ := key Y hY hYf hcY.1
  have hgh : Commute (expA F (c • X)) (expA F (c • Y)) := by
    have := congrArg (fun k : ↥(GSpin d.QW) =>
      (((k : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW)) (hx.2.1 g hg h hh).eq
    simp only [Subgroup.coe_mul, Units.val_mul] at this
    rw [hge, hhe] at this
    exact this
  have h1 : Commute (expA F (c • X)) (c • Y) := hc _ hcY.2 _ hgh
  have h2 : Commute (c • Y) (c • X) := hc _ hcX.2 _ h1.symm
  have h3 : c • c • (Y * X) = c • c • (X * Y) := by
    have := h2.eq
    rw [smul_mul_smul_comm, smul_mul_smul_comm] at this
    rw [smul_smul, smul_smul]
    exact this
  rw [Ring.lie_def, sub_eq_zero]
  have hc' : c * c ≠ 0 := mul_ne_zero hc0 hc0
  rw [smul_smul, smul_smul] at h3
  exact (smul_right_injective _ hc' h3).symm

/-- On `Γ(G,H)`, `IsQdAt` is exactly "`G_x` quasi-split", i.e. `Nil_reg(𝔤_x) ≠ ∅`.
Off `Γ(G,H)` only `→` holds (`nilReg_centralizer_nonempty_imp`). -/
theorem isQdAt_iff_nilReg_nonempty (d : GGPData F) (x : ↥(GSpin d.QW)) (hx : d.IsGammaElt x) :
    IsQdAt d x ↔ (NilReg (grpCentralizer d.G ((d.diag x : d.G) : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag x : d.G) : d.ambientˣ) : d.ambient))).Nonempty :=
  (nilReg_centralizer_nonempty_iff d x hx.1 (movedPartAbelian_of_isGammaElt d x hx)).symm

end Counts

/-! ## 4. Thesis Prop. 6.6.1 -/

section Prop1251

variable {d : GGPData F}

/-- **Thesis Prop. 6.6.1(i), Step 1** (own work; `p`-adic classification of quadratic forms):
`W'_{α,y}` embeds isometrically in `W`.  Route: let `2k = dim W''_{α,y}`,
`δ = disc W''_{α,y}`.  If `k ≥ 2`, planes/spaces of dimension `2k` and discriminant `δ` exist
with both Hasse invariants, so `W'_{α,y} ⊕ U ≅ W` for a suitable `U` (Lam, Ch. VI); if `k = 1`,
`W''_{α,y}` is an anisotropic plane and both Hasse invariants occur among the planes `c N_{E/F}`
of discriminant `δ` (if `dim W = 2` then `W'_{α,y} = 0`).  If `k = 0` (`y` central)
`W'_{α,y} = W_α`, and `W_α ≅ W` because both `W_α, W` and `V_α, V` are
quasi-split (`hqs`, `hqd`) and the odd-dimensional one of `W`, `V` of dimension `≥ 3` is
determined by quasi-splitness.  Proved (`GGP/QuadClassify.exists_isometry_fixedSub`)
by a slightly different case split that needs no anisotropy of `W''_{α,y}`: if `W''_{α,y}` is `0`
or a hyperbolic plane, `G_α` is quasi-split and `W_α ≅ W`; `dim W''_{α,y} = 1` is impossible
(`det P(y) = 1`); otherwise a second class of the dimension and discriminant of `W''_{α,y}`
exists. -/
theorem exists_isometry_fixedSub_of_qd (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (α : IF.Idx) (y : ↥(GSpin (IF.data α).QW)) (hy : (IF.data α).IsGammaElt y)
    (hqd : IsQdAt (IF.data α) y) :
    ∃ ι : (IF.data α).QW.comp (fixedSub y).subtype →qᵢ d.QW, Function.Injective ι :=
  QuadClassify.exists_isometry_fixedSub d hqs (IF.twist α).nondeg' (IF.twist α).sameDisc y hy.1
    hqd.1 hqd.2

/-- **Thesis Prop. 6.6.1(i), Steps 2–3** (own work, citing BP (12.1.6)): given an isometric
embedding `W'_{α,y} ↪ W`, some `x ∈ Γ(G,H)` is strongly stably conjugate to `y`.  Route:
let `W''` be the orthogonal complement of the image; its class lies in the image of
`H¹(F, S_y) → H¹(F, SO(W''_{α,y}))` (`k = 1`: `S_y = SO(W''_{α,y})`; `k ≥ 2`: surjective by
BP (12.1.6), `S~_y` being connected as in `exists_twistIdx_kottwitzSign_neg`);
a cocycle `b` in `S_y` with an
isometry `ι'' : W''_{α,y,F̄} ≃ W''_{F̄}`, `ι''⁻¹ σι'' = b_σ`, transports `ȳ''` to a rational regular
`x̄'' ∈ SO(W'')` with anisotropic centralizer; a lift `x₀ ∈ GSpin(W)(F)` of `(1_{W'}, x̄'')` lies
in `Γ(G,H)`; after a rational reflection making `Φ⁻¹ ∘ φ_α` proper, lifting the stable
conjugacy from `SO` to `GSpin` gives
`x = λ x₀`, `λ ∈ F^×`, strongly stably conjugate to `y`. -/
theorem exists_stronglyStablyConj_of_isometry (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (α : IF.Idx) (y : ↥(GSpin (IF.data α).QW)) (hy : (IF.data α).IsGammaElt y)
    (hqd : IsQdAt (IF.data α) y) (ι : (IF.data α).QW.comp (fixedSub y).subtype →qᵢ d.QW)
    (hι : Function.Injective ι) :
    ∃ x : ↥(GSpin d.QW), d.IsGammaElt x ∧ d.StronglyStablyConjW (IF.twist α) x y :=
  sorry

/-- **Thesis Prop. 6.6.1(i)** (own work).
Let `G` be quasi-split, `α` an inner form and `y ∈ Γ(G_α,H_α)` with `G_{α,y}` quasi-split
(i.e. `W'_{α,y}` and `V'_{α,y}` quasi-split).  Then some `x ∈ Γ(G,H)` is strongly stably conjugate
to `y`.  (Proof: embed `W'_{α,y} ↪ W` by the `p`-adic classification, transfer the
anisotropic torus `S_y` into `SO(W'')` by BP (12.1.6), and lift from `SO` to `GSpin`.) -/
theorem prop_12_5_1_i (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d) (α : IF.Idx)
    (y : ↥(GSpin (IF.data α).QW)) (hy : (IF.data α).IsGammaElt y) (hqd : IsQdAt (IF.data α) y) :
    ∃ x : ↥(GSpin d.QW), d.IsGammaElt x ∧ d.StronglyStablyConjW (IF.twist α) x y := by
  obtain ⟨ι, hι⟩ := exists_isometry_fixedSub_of_qd hqs IF α y hy hqd
  exact exists_stronglyStablyConj_of_isometry hqs IF α y hy hqd ι hι

/-- The conclusion of Thesis Prop. 6.6.1(ii) for `x`, `y` (see
`prop_12_5_1_ii`): an `F`-rational isomorphism of topological groups `T_x(F) ≃ T_y(F)`, identity on
`A_{G,H}`, `x ↦ y`, matching `T_♮`, strong stable classes, `D^G` and `Δ`.

No clause `|W(T_y)| = |W(T_x)|`: it is false in general.
`W(T)` (`weylCardOf`: `N_{GSpin(W)(F)}(T)/Z_{GSpin(W)(F)}(T)`, i.e.
`N_{O(W'')(F)}(S)/S(F)` when `W' ≠ 0`) is a group of rational points, which depends on the quadratic
space `W''`, and `W''_x`, `W''_{α,y}` have opposite Hasse invariants when `α ≠ 1` (counterexample
`dim W'' = 4`, `S = U(1)_E²`, `W' = ⟨1⟩`: orders 8 vs 4, or 4 vs 2 for the smaller group
`W(GSpin(W''),T)`). It is not needed:
`W(T)` acts freely on the full-measure subset of `A\T_♮(F)` where `t̄` has distinct eigenvalues on
`W''` (not on all of it: when `W' ≠ 0` a point with a `−1` eigenplane can have stabilizer of
order 2), so near a generic class the factor `|W(T)|⁻¹` of `mGeomS` cancels the
`|W(T)|`-to-1 projection, and the local measure on `Γ` is the probability Haar measure of
`T(F)/A(F)` translated to the point. That measure comparison is implicit here: `e` is a
homeomorphic group isomorphism fixing the scalars, so it induces `T_x(F)/A(F) ≃ T_y(F)/A(F)` and
carries probability Haar to probability Haar (uniqueness of Haar measure). -/
def TorusTransfer (IF : InnerFormSystem d) (α : IF.Idx) (x : ↥(GSpin d.QW))
    (y : ↥(GSpin (IF.data α).QW)) : Prop :=
    ∃ e : ↥(d.torusOf x) ≃* ↥((IF.data α).torusOf y),
      Continuous e ∧ Continuous e.symm ∧
      (∀ c : Fˣ, ((e ⟨scalarGSpin d.QW c, d.scalar_mem_torusOf x c⟩ : ↥((IF.data α).torusOf y)) :
          ↥(GSpin (IF.data α).QW)) = scalarGSpin (IF.data α).QW c) ∧
      (∀ t : ↥(d.torusOf x), (t : ↥(GSpin d.QW)) = x → (e t : ↥(GSpin (IF.data α).QW)) = y) ∧
      (∀ t : ↥(d.torusOf x),
        (d.IsGammaElt t ∧ d.torusOf t = d.torusOf x ↔
          (IF.data α).IsGammaElt (e t) ∧ (IF.data α).torusOf (e t) = (IF.data α).torusOf y)) ∧
      (∀ t : ↥(d.torusOf x), d.IsGammaElt t → d.torusOf t = d.torusOf x →
        d.StronglyStablyConjW (IF.twist α) t (e t)) ∧
      (∀ t : ↥(d.torusOf x), deltaGGP (IF.data α) (e t) = deltaGGP d t ∧
        weylDisc (IF.data α).lie ((IF.data α).diag (e t) : (IF.data α).ambientˣ) =
          weylDisc d.lie (d.diag t : d.ambientˣ))

/-! ### Helpers for `deltaGGP_eq_of_stablyConjVia` (own work, elementary)

`Δ(t) = |det((P(t) − 1)|_{W''_t})|` with `W''_t = Im(P(t) − 1)`: the determinant of a map restricted to
its range is invariant under conjugation and compatible with base change, and over `F̄` stable
conjugacy conjugates `P(t)` to `P(t')` by `P(g) ∘ φ`. -/

section EndElemDelta

open CliffordAlgebra
open scoped TensorProduct

section RangeDet

variable {K : Type*} [Field K] {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N]
  [Module K N]

/-- `A` restricted to its range `A(M)` (the shape of `Δ`, `deltaGGP`). -/
abbrev rangeRestr (A : M →ₗ[K] M) : LinearMap.range A →ₗ[K] LinearMap.range A :=
  A.restrict (p := LinearMap.range A) (q := LinearMap.range A)
    (fun v _ => LinearMap.mem_range_self A v)

/-- Determinants agree for maps intertwined by a linear equivalence (`LinearMap.det_conj`). -/
theorem det_eq_of_intertwine (f : M →ₗ[K] M) (g : N →ₗ[K] N) (e : M ≃ₗ[K] N)
    (h : ∀ v, g (e v) = e (f v)) : LinearMap.det g = LinearMap.det f := by
  have : g = (e : M →ₗ[K] N) ∘ₗ f ∘ₗ (e.symm : N →ₗ[K] M) := by
    ext u
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [← h, e.apply_symm_apply]
  rw [this, LinearMap.det_conj]

/-- `det(A|_{A(M)})` is invariant under conjugation. -/
theorem det_rangeRestr_conj (A : M →ₗ[K] M) (B : N →ₗ[K] N) (e : M ≃ₗ[K] N)
    (h : ∀ v, B (e v) = e (A v)) :
    LinearMap.det (rangeRestr B) = LinearMap.det (rangeRestr A) := by
  have hr : (LinearMap.range A).map (e : M →ₗ[K] N) = LinearMap.range B := by
    ext u
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨e v, h v⟩
    · rintro ⟨v, rfl⟩
      exact ⟨A (e.symm v), ⟨_, rfl⟩, by rw [LinearEquiv.coe_coe, ← h, e.apply_symm_apply]⟩
  refine det_eq_of_intertwine _ _ ((e.submoduleMap _).trans (LinearEquiv.ofEq _ _ hr)) fun v => ?_
  apply Subtype.ext
  show B (e v) = e (A v)
  exact h v

variable [FiniteDimensional K M] (L : Type*) [Field L] [Algebra K L]

/-- `det(A|_{A(M)})` is compatible with base change: `(L ⊗ A)(L ⊗ M) = L ⊗ A(M)` (flatness of `L`
over the field `K`), and `det` commutes with base change (`LinearMap.det_baseChange`). -/
theorem det_rangeRestr_baseChange (A : M →ₗ[K] M) :
    LinearMap.det (M := LinearMap.range (A.baseChange L)) (rangeRestr (A.baseChange L)) =
      algebraMap K L (LinearMap.det (rangeRestr A)) := by
  set R := LinearMap.range A
  have hinj : Function.Injective (R.subtype.baseChange L) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ R.injective_subtype
  have hr : LinearMap.range (R.subtype.baseChange L) = LinearMap.range (A.baseChange L) := by
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      induction u using TensorProduct.inductionOn with
      | tmul z v =>
        obtain ⟨_, w, rfl⟩ := v
        exact ⟨z ⊗ₜ w, by simp⟩
      | add a b ha hb => rw [map_add]; exact add_mem ha hb
    · rintro _ ⟨u, rfl⟩
      induction u using TensorProduct.inductionOn with
      | tmul z w => exact ⟨z ⊗ₜ ⟨A w, LinearMap.mem_range_self A w⟩, by simp⟩
      | add a b ha hb => rw [map_add]; exact add_mem ha hb
  rw [← LinearMap.det_baseChange]
  refine det_eq_of_intertwine _ _ ((LinearEquiv.ofInjective _ hinj).trans
    (LinearEquiv.ofEq _ _ hr)) fun u => ?_
  apply Subtype.ext
  show A.baseChange L (R.subtype.baseChange L u) =
    R.subtype.baseChange L ((rangeRestr A).baseChange L u)
  induction u using TensorProduct.inductionOn with
  | tmul z v => simp
  | add a b ha hb => simp only [map_add, ha, hb]

end RangeDet

section BCConj

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- `t ι(w) t⁻¹ = ι(P(t)_{F̄} w)` in `C(Q_{F̄})`, for `t ∈ GSpin(Q)(F)`. -/
theorem bcUnits_conj_ι (Q : QuadraticForm F V) (t : GSpin Q) (w : AlgebraicClosure F ⊗[F] V) :
    ((bcUnits Q (t : (CliffordAlgebra Q)ˣ) : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) *
      ι (Q.baseChange (AlgebraicClosure F)) w *
      (((bcUnits Q (t : (CliffordAlgebra Q)ˣ))⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
    ι (Q.baseChange (AlgebraicClosure F))
      ((specP Q t : V →ₗ[F] V).baseChange (AlgebraicClosure F) w) := by
  induction w using TensorProduct.inductionOn with
  | tmul z v =>
    rw [LinearMap.baseChange_tmul, ← ofBaseChange_tmul_ι, ← ofBaseChange_tmul_ι, LinearEquiv.coe_coe,
      ι_specP]
    show ofBaseChange (AlgebraicClosure F) Q (1 ⊗ₜ ((t : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) *
      ofBaseChange (AlgebraicClosure F) Q (z ⊗ₜ ι Q v) * ofBaseChange (AlgebraicClosure F) Q
        (1 ⊗ₜ (((t : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) = _
    rw [← map_mul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  | add a b ha hb => rw [map_add, mul_add, add_mul, ha, hb, map_add, map_add]

end BCConj

/-- If `g C(φ)(t_{F̄}) g⁻¹ = t'_{F̄}`, then `H = P(g) ∘ φ` intertwines `P(t)_{F̄}` and `P(t')_{F̄}`
(own work, elementary; the first step of the proof of `deltaGGP_eq_of_stablyConjVia`). -/
theorem specP_baseChange_intertwine (τ : InnerTwist d.QW) (t : ↥(GSpin d.QW))
    (t' : ↥(GSpin (d.twist τ).QW))
    (g : (CliffordAlgebra (τ.Q'.baseChange (AlgebraicClosure F)))ˣ)
    (hg : g ∈ GSpin (τ.Q'.baseChange (AlgebraicClosure F)))
    (h : g * cliffUnits τ.φ (bcUnits d.QW (t : (CliffordAlgebra d.QW)ˣ)) * g⁻¹ =
      bcUnits τ.Q' (t' : (CliffordAlgebra τ.Q')ˣ))
    (w : AlgebraicClosure F ⊗[F] (Fin d.m → F)) :
    (specP τ.Q' t' : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange (AlgebraicClosure F)
        (specP (τ.Q'.baseChange (AlgebraicClosure F)) ⟨g, hg⟩ (τ.φ w)) =
      specP (τ.Q'.baseChange (AlgebraicClosure F)) ⟨g, hg⟩
        (τ.φ ((specP d.QW t : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange (AlgebraicClosure F) w)) := by
  set U := cliffUnits τ.φ (bcUnits d.QW (t : (CliffordAlgebra d.QW)ˣ))
  have hinv : g * U⁻¹ * g⁻¹ = (bcUnits τ.Q' (t' : (CliffordAlgebra τ.Q')ˣ))⁻¹ := by
    rw [← h]; group
  have hU : ∀ u, (U : CliffordAlgebra (τ.Q'.baseChange (AlgebraicClosure F))) *
      ι (τ.Q'.baseChange (AlgebraicClosure F)) (τ.φ u) *
      ((U⁻¹ : (CliffordAlgebra (τ.Q'.baseChange (AlgebraicClosure F)))ˣ) :
        CliffordAlgebra (τ.Q'.baseChange (AlgebraicClosure F))) =
      ι (τ.Q'.baseChange (AlgebraicClosure F)) (τ.φ ((specP d.QW t : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange (AlgebraicClosure F) u)) := by
    intro u
    have e1 : ι (τ.Q'.baseChange (AlgebraicClosure F)) (τ.φ u) =
        CliffordAlgebra.map τ.φ.toIsometry (ι _ u) := by rw [map_apply_ι]; rfl
    have e2 : ι (τ.Q'.baseChange (AlgebraicClosure F)) (τ.φ
        ((specP d.QW t : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange (AlgebraicClosure F) u)) =
        CliffordAlgebra.map τ.φ.toIsometry (ι _
          ((specP d.QW t : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange (AlgebraicClosure F) u)) := by
      rw [map_apply_ι]; rfl
    rw [e1, e2, ← bcUnits_conj_ι, map_mul, map_mul]
    rfl
  apply ι_injective (τ.Q'.baseChange (AlgebraicClosure F))
  rw [← bcUnits_conj_ι, ← hinv, ← h, ι_specP, ι_specP, ← hU]
  simp only [Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]

end EndElemDelta

/-- **`Δ` is invariant under stable conjugacy** (own work, elementary): if `P(t') = h P(t) h⁻¹`
over `F̄` (`h = P(g) ∘ φ`), then `h` maps `W''_t ⊗ F̄` onto `W''_{t'} ⊗ F̄` and conjugates
`(P(t) − 1)|_{W''_t}` to `(P(t') − 1)|_{W''_{t'}}`; the two determinants lie in `F` and agree in
`F̄`, so their absolute values agree. -/
theorem deltaGGP_eq_of_stablyConjVia (τ : InnerTwist d.QW) (t : ↥(GSpin d.QW))
    (t' : ↥(GSpin (d.twist τ).QW))
    (h : StablyConjVia τ.φ (t : (CliffordAlgebra d.QW)ˣ) (t' : (CliffordAlgebra (d.twist τ).QW)ˣ)) :
    deltaGGP (d.twist τ) t' = deltaGGP d t := by
  obtain ⟨g, hg, h⟩ := h
  set H := τ.φ.toLinearEquiv.trans (specP (τ.Q'.baseChange (AlgebraicClosure F)) ⟨g, hg⟩)
  have key : ∀ w, ((specP τ.Q' t' : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) - LinearMap.id).baseChange
      (AlgebraicClosure F) (H w) = H (((specP d.QW t : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) -
        LinearMap.id).baseChange (AlgebraicClosure F) w) := by
    intro w
    rw [LinearMap.baseChange_sub, LinearMap.baseChange_sub, LinearMap.baseChange_id,
      LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.id_apply, map_sub]
    congr 1
    exact specP_baseChange_intertwine τ t t' g hg h w
  have h1 := det_rangeRestr_baseChange (AlgebraicClosure F)
    ((specP τ.Q' t' : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) - LinearMap.id)
  have h2 := det_rangeRestr_baseChange (AlgebraicClosure F)
    ((specP d.QW t : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) - LinearMap.id)
  have h3 := det_rangeRestr_conj _ _ H key
  unfold deltaGGP
  congr 1
  apply (algebraMap F (AlgebraicClosure F)).injective
  exact h1.symm.trans (h3.trans h2)

/-! ### Helpers for `weylDisc_eq_of_stablyConjG` (own work, elementary)

Over `F̄`, `𝔤 ⊗ F̄ = gspin(W_{F̄}) × gspin(V_{F̄})` (`range_gspinProdBC`, from `gspin = span{v w} ⊕ F`,
`gspin_eq_span`), and `ψ = (Ad(g_W) ∘ C(φ), Ad(g_V) ∘ C(φ ⊕ 1_Z))` maps it onto `𝔤_α ⊗ F̄`
intertwining `1 − Ad(t)` and `1 − Ad(t')` (`psiPair_map_gspin`, `psiPair_intertwine`); characteristic
polynomials are unchanged by base change (`LinearMap.charpoly_baseChange`). -/

section EndElemWeyl

open CliffordAlgebra
open scoped TensorProduct

section WD

/-- Characteristic polynomials agree for maps intertwined by a linear equivalence. -/
theorem charpoly_eq_of_intertwine {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (f : M →ₗ[K] M) (g : N →ₗ[K] N) (e : M ≃ₗ[K] N)
    (h : ∀ v, g (e v) = e (f v)) : g.charpoly = f.charpoly := by
  have : g = e.conj f := by
    ext u
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, ← h, e.apply_symm_apply]
  rw [this, LinearEquiv.charpoly_conj]

/-- A nondegenerate form stays nondegenerate over `F̄` (the Gram determinant is unchanged). -/
theorem isNondeg_baseChange {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (Q : QuadraticForm F V) (hQ : IsNondeg Q) :
    IsNondeg (Q.baseChange (AlgebraicClosure F)) := by
  unfold IsNondeg bform at *
  set b := Module.Free.chooseBasis F V
  rw [QuadraticForm.associated_baseChange,
    LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange (AlgebraicClosure F))]
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b] at hQ
  have : LinearMap.BilinForm.toMatrix (b.baseChange (AlgebraicClosure F))
      (LinearMap.BilinForm.baseChange (AlgebraicClosure F) (QuadraticMap.associated Q)) =
      (algebraMap F (AlgebraicClosure F)).mapMatrix
        (LinearMap.BilinForm.toMatrix b (QuadraticMap.associated Q)) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      LinearMap.BilinForm.toMatrix_apply, Module.Basis.baseChange_apply,
      Module.Basis.baseChange_apply, LinearMap.BilinForm.baseChange_tmul, mul_one,
      Algebra.smul_def, mul_one]
  rw [this, ← RingHom.map_det]
  exact (map_ne_zero _).2 hQ

variable {V : Type*} [AddCommGroup V] [Module F V]

theorem ofBaseChange_tmul_eq (Q : QuadraticForm F V) (z : AlgebraicClosure F)
    (X : CliffordAlgebra Q) :
    ofBaseChange (AlgebraicClosure F) Q (z ⊗ₜ X) = algebraMap _ _ z * bcHom Q X := by
  rw [show z ⊗ₜ[F] X = (z ⊗ₜ[F] (1 : CliffordAlgebra Q)) * (1 ⊗ₜ X) by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul, ofBaseChange_tmul_one]
  rfl

theorem bcHom_ι (Q : QuadraticForm F V) (v : V) :
    bcHom Q (ι Q v) = ι (Q.baseChange (AlgebraicClosure F)) (1 ⊗ₜ v) :=
  ofBaseChange_tmul_ι _ _ _ _

theorem bcHom_mem_even (Q : QuadraticForm F V) {X : CliffordAlgebra Q} (hX : X ∈ even Q) :
    bcHom Q X ∈ even (Q.baseChange (AlgebraicClosure F)) := by
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hX ⊢
  induction X, hX using even_induction with
  | algebraMap r =>
    have : bcHom Q (algebraMap F _ r) = algebraMap (AlgebraicClosure F) _
        (algebraMap F (AlgebraicClosure F) r) := by
      show ofBaseChange (AlgebraicClosure F) Q (1 ⊗ₜ algebraMap F _ r) = _
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, ofBaseChange_tmul_one,
        Algebra.smul_def, mul_one]
    rw [this]
    exact SetLike.algebraMap_mem_graded _ _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul, bcHom_ι, bcHom_ι]
    exact zero_add (0 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero _ _ _) ih

theorem ofBaseChange_mem_gspin (Q : QuadraticForm F V) (z : AlgebraicClosure F)
    {X : CliffordAlgebra Q} (hX : X ∈ gspin Q) :
    ofBaseChange (AlgebraicClosure F) Q (z ⊗ₜ X) ∈ gspin (Q.baseChange (AlgebraicClosure F)) := by
  rw [ofBaseChange_tmul_eq, ← Algebra.smul_def]
  refine (gspin _).smul_mem z ⟨bcHom_mem_even Q hX.1, fun w => ?_⟩
  induction w using TensorProduct.inductionOn with
  | tmul c v =>
    obtain ⟨u, hu⟩ := hX.2 v
    refine ⟨c ⊗ₜ u, ?_⟩
    have hc : ι (Q.baseChange (AlgebraicClosure F)) (c ⊗ₜ v) = c • ι _ (1 ⊗ₜ v) := by
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hc' : ι (Q.baseChange (AlgebraicClosure F)) (c ⊗ₜ u) = c • ι _ (1 ⊗ₜ u) := by
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hc, hc', ← bcHom_ι, ← bcHom_ι, hu, Ring.lie_def, Ring.lie_def, mul_smul_comm,
      smul_mul_assoc, ← smul_sub, map_sub, map_mul, map_mul]
  | add a b ha hb =>
    rw [map_add, lie_add]
    exact Submodule.add_mem _ ha hb


/-- `F̄ ⊗ gspin(Q) → C(Q_{F̄})`. -/
def gspinBC (Q : QuadraticForm F V) :
    AlgebraicClosure F ⊗[F] (gspin Q).toSubmodule →ₗ[AlgebraicClosure F]
      CliffordAlgebra (Q.baseChange (AlgebraicClosure F)) :=
  (ofBaseChange (AlgebraicClosure F) Q).toLinearMap ∘ₗ
    (gspin Q).toSubmodule.subtype.baseChange (AlgebraicClosure F)

theorem gspinBC_tmul (Q : QuadraticForm F V) (z : AlgebraicClosure F) (X : (gspin Q).toSubmodule) :
    gspinBC Q (z ⊗ₜ X) = ofBaseChange (AlgebraicClosure F) Q (z ⊗ₜ (X : CliffordAlgebra Q)) := rfl

theorem ofBaseChange_injective (Q : QuadraticForm F V) :
    Function.Injective (ofBaseChange (AlgebraicClosure F) Q) :=
  Function.LeftInverse.injective (toBaseChange_ofBaseChange (AlgebraicClosure F) Q)

theorem baseChange_subtype_injective {M : Type*} [AddCommGroup M] [Module F M] (p : Submodule F M) :
    Function.Injective (p.subtype.baseChange (AlgebraicClosure F)) := by
  rw [LinearMap.baseChange_eq_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ p.injective_subtype

/-- Over `F̄`, `gspin(Q_{F̄})` is spanned by `gspin(Q)` (via `gspin = span{v w} ⊕ F`,
`gspin_eq_span`, for `Q_{F̄}` nondegenerate). -/
theorem range_gspinBC [Module.Finite F V] (Q : QuadraticForm F V)
    (hQ : IsNondeg (Q.baseChange (AlgebraicClosure F))) :
    LinearMap.range (gspinBC Q) = (gspin (Q.baseChange (AlgebraicClosure F))).toSubmodule := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    induction u using TensorProduct.inductionOn with
    | tmul z X => exact ofBaseChange_mem_gspin Q z X.2
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  · rw [gspin_eq_span hQ, sup_le_iff, Submodule.span_le, Submodule.span_le]
    constructor
    · rintro _ ⟨⟨w₁, w₂⟩, rfl⟩
      dsimp only
      induction w₁ using TensorProduct.inductionOn with
      | tmul a v =>
        induction w₂ using TensorProduct.inductionOn with
        | tmul b v' =>
          refine ⟨(a * b) ⊗ₜ ⟨ι Q v * ι Q v', ι_mul_ι_mem_gspin Q v v'⟩, ?_⟩
          rw [gspinBC_tmul, ← Algebra.TensorProduct.tmul_mul_tmul, map_mul,
            ofBaseChange_tmul_ι, ofBaseChange_tmul_ι]
        | add b c hb hc => rw [map_add, mul_add]; exact add_mem hb hc
      | add b c hb hc => rw [map_add, add_mul]; exact add_mem hb hc
    · rintro _ rfl
      exact ⟨1 ⊗ₜ ⟨1, one_mem_gspin Q⟩, by rw [gspinBC_tmul]; exact map_one _⟩

variable {V₂ : Type*} [AddCommGroup V₂] [Module F V₂]

/-- `F̄ ⊗ P → C(Q₁_{F̄}) × C(Q₂_{F̄})` for an `F`-subspace `P ⊆ C(Q₁) × C(Q₂)` (used for
`P = 𝔤 = gspin(W) × gspin(V)`). -/
def gspinProdBC (Q₁ : QuadraticForm F V) (Q₂ : QuadraticForm F V₂)
    (P : Submodule F (CliffordAlgebra Q₁ × CliffordAlgebra Q₂)) :
    AlgebraicClosure F ⊗[F] P →ₗ[AlgebraicClosure F]
      CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F)) ×
        CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)) :=
  ((ofBaseChange (AlgebraicClosure F) Q₁).toLinearMap.prodMap
      (ofBaseChange (AlgebraicClosure F) Q₂).toLinearMap) ∘ₗ
    (TensorProduct.prodRight F (AlgebraicClosure F) (AlgebraicClosure F) _ _).toLinearMap ∘ₗ
      P.subtype.baseChange (AlgebraicClosure F)

theorem gspinProdBC_tmul (Q₁ : QuadraticForm F V) (Q₂ : QuadraticForm F V₂)
    (P : Submodule F (CliffordAlgebra Q₁ × CliffordAlgebra Q₂)) (z : AlgebraicClosure F) (X : P) :
    gspinProdBC Q₁ Q₂ P (z ⊗ₜ X) =
      (ofBaseChange (AlgebraicClosure F) Q₁ (z ⊗ₜ (X : CliffordAlgebra Q₁ × CliffordAlgebra Q₂).1),
        ofBaseChange (AlgebraicClosure F) Q₂
          (z ⊗ₜ (X : CliffordAlgebra Q₁ × CliffordAlgebra Q₂).2)) := rfl

theorem gspinProdBC_injective (Q₁ : QuadraticForm F V) (Q₂ : QuadraticForm F V₂)
    (P : Submodule F (CliffordAlgebra Q₁ × CliffordAlgebra Q₂)) :
    Function.Injective (gspinProdBC Q₁ Q₂ P) := fun _ _ h =>
  baseChange_subtype_injective _ ((TensorProduct.prodRight F (AlgebraicClosure F)
    (AlgebraicClosure F) _ _).injective
      (Prod.map_injective.2 ⟨ofBaseChange_injective Q₁, ofBaseChange_injective Q₂⟩ h))

/-- If `P = gspin(Q₁) × gspin(Q₂)`, then `F̄ ⊗ P ≅ gspin(Q₁_{F̄}) × gspin(Q₂_{F̄})`. -/
theorem range_gspinProdBC [Module.Finite F V] [Module.Finite F V₂] (Q₁ : QuadraticForm F V)
    (Q₂ : QuadraticForm F V₂) (P : Submodule F (CliffordAlgebra Q₁ × CliffordAlgebra Q₂))
    (hP : ∀ x, x ∈ P ↔ x.1 ∈ gspin Q₁ ∧ x.2 ∈ gspin Q₂)
    (h₁ : IsNondeg (Q₁.baseChange (AlgebraicClosure F)))
    (h₂ : IsNondeg (Q₂.baseChange (AlgebraicClosure F))) :
    LinearMap.range (gspinProdBC Q₁ Q₂ P) =
      (gspin (Q₁.baseChange (AlgebraicClosure F))).toSubmodule.prod
        (gspin (Q₂.baseChange (AlgebraicClosure F))).toSubmodule := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    induction u using TensorProduct.inductionOn with
    | tmul z X =>
      rw [gspinProdBC_tmul]
      exact ⟨ofBaseChange_mem_gspin Q₁ z ((hP _).1 X.2).1,
        ofBaseChange_mem_gspin Q₂ z ((hP _).1 X.2).2⟩
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  · rintro ⟨Y₁, Y₂⟩ ⟨hY₁, hY₂⟩
    rw [← range_gspinBC Q₁ h₁] at hY₁
    rw [← range_gspinBC Q₂ h₂] at hY₂
    obtain ⟨u₁, rfl⟩ := hY₁
    obtain ⟨u₂, rfl⟩ := hY₂
    let i₁ : (gspin Q₁).toSubmodule →ₗ[F] P :=
      LinearMap.codRestrict _ (LinearMap.inl F _ _ ∘ₗ (gspin Q₁).toSubmodule.subtype)
        fun X => (hP _).2 ⟨X.2, zero_mem _⟩
    let i₂ : (gspin Q₂).toSubmodule →ₗ[F] P :=
      LinearMap.codRestrict _ (LinearMap.inr F _ _ ∘ₗ (gspin Q₂).toSubmodule.subtype)
        fun X => (hP _).2 ⟨zero_mem _, X.2⟩
    have e₁ : ∀ u, gspinProdBC Q₁ Q₂ P (i₁.baseChange (AlgebraicClosure F) u) =
        (gspinBC Q₁ u, 0) := by
      intro u
      induction u using TensorProduct.inductionOn with
      | tmul z X =>
        rw [LinearMap.baseChange_tmul, gspinProdBC_tmul, gspinBC_tmul]
        simp [i₁]
      | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, Prod.mk_add_mk, add_zero]
    have e₂ : ∀ u, gspinProdBC Q₁ Q₂ P (i₂.baseChange (AlgebraicClosure F) u) =
        (0, gspinBC Q₂ u) := by
      intro u
      induction u using TensorProduct.inductionOn with
      | tmul z X =>
        rw [LinearMap.baseChange_tmul, gspinProdBC_tmul, gspinBC_tmul]
        simp [i₂]
      | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, Prod.mk_add_mk, add_zero]
    refine ⟨i₁.baseChange (AlgebraicClosure F) u₁ + i₂.baseChange (AlgebraicClosure F) u₂, ?_⟩
    rw [map_add, e₁, e₂, Prod.mk_add_mk, add_zero, zero_add]

/-- Componentwise two-sided multiplication on a product of algebras. -/
def adPair {A B : Type*} [Mul A] [Mul B] (a a' : A) (b b' : B) (p : A × B) : A × B :=
  (a * p.1 * a', b * p.2 * b')

/-- `ψ_g = Ad(g) ∘ ψ` intertwines conjugation by `T` and by `g ψ(T) g⁻¹`. -/
theorem conj_intertwine {K : Type*} [Field K] {A B : Type*} [Ring A] [Algebra K A] [Ring B]
    [Algebra K B] (ψ : A →ₐ[K] B) (g U : Bˣ) (T Ti : A) (hU : (U : B) = ψ T)
    (hUi : ((U⁻¹ : Bˣ) : B) = ψ Ti) (x : A) :
    (g : B) * ψ (T * x * Ti) * ((g⁻¹ : Bˣ) : B) =
      ((g * U * g⁻¹ : Bˣ) : B) * ((g : B) * ψ x * ((g⁻¹ : Bˣ) : B)) *
        (((g * U * g⁻¹)⁻¹ : Bˣ) : B) := by
  have : (g * U * g⁻¹)⁻¹ = g * U⁻¹ * g⁻¹ := by group
  rw [this, map_mul, map_mul, ← hU, ← hUi]
  simp only [Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]

/-- `ofBaseChange (z ⊗ a x b) = a_{F̄} ofBaseChange(z ⊗ x) b_{F̄}`. -/
theorem ofBaseChange_tmul_mul3 (Q : QuadraticForm F V) (z : AlgebraicClosure F)
    (a x b : CliffordAlgebra Q) :
    ofBaseChange (AlgebraicClosure F) Q (z ⊗ₜ (a * x * b)) =
      bcHom Q a * ofBaseChange (AlgebraicClosure F) Q (z ⊗ₜ x) * bcHom Q b := by
  rw [show z ⊗ₜ[F] (a * x * b) = (1 ⊗ₜ a) * (z ⊗ₜ x) * (1 ⊗ₜ b) by
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one], map_mul, map_mul]
  rfl

end WD


section GspinMaps

variable {K : Type*} [Field K] [Invertible (2 : K)] {W₁ W₂ : Type*} [AddCommGroup W₁] [Module K W₁]
  [AddCommGroup W₂] [Module K W₂]

/-- `gspin(V)` is stable under conjugation by `GSpin(V)` (copy of `conj_mem_gspin` of
`TraceFormula/ThetaF`, which `Main` does not import). -/
theorem conj_mem_gspin_ofGSpin (Q : QuadraticForm K W₁) (g : GSpin Q) {X : CliffordAlgebra Q}
    (hX : X ∈ gspin Q) :
    ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * X *
      (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ gspin Q := by
  obtain ⟨hX0, hX⟩ := hX
  set u : (CliffordAlgebra Q)ˣ := (g : (CliffordAlgebra Q)ˣ)
  have hg := g.2
  refine ⟨?_, fun v => ?_⟩
  · exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hg.1 hX0) (g⁻¹ : GSpin Q).2.1
  · obtain ⟨w, hw⟩ := hg.2.2 v
    have hv : ι Q v = (u : CliffordAlgebra Q) * ι Q w * ((u⁻¹ : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q) := by
      rw [hw]
      simp [u, mul_assoc]
    obtain ⟨t, ht⟩ := hX w
    obtain ⟨r, hr⟩ := hg.2.1 t
    refine ⟨r, ?_⟩
    rw [hr, hv, Ring.lie_def]
    rw [Ring.lie_def] at ht
    rw [ht]
    simp only [mul_sub, sub_mul, mul_assoc, Units.inv_mul_cancel_left]
    rfl

/-- `C(φ)` maps `gspin` to `gspin` for an isometry `φ`. -/
theorem map_mem_gspin {Q₁ : QuadraticForm K W₁} {Q₂ : QuadraticForm K W₂}
    (φ : Q₁.IsometryEquiv Q₂) {X : CliffordAlgebra Q₁} (hX : X ∈ gspin Q₁) :
    CliffordAlgebra.map φ.toIsometry X ∈ gspin Q₂ := by
  refine ⟨?_, fun w => ?_⟩
  · have h0 := hX.1
    clear hX
    rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at h0 ⊢
    induction X, h0 using even_induction with
    | algebraMap r => rw [AlgHom.commutes]; exact SetLike.algebraMap_mem_graded _ _
    | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
    | ι_mul_ι_mul m₁ m₂ x hx ih =>
      rw [map_mul, map_mul, map_apply_ι, map_apply_ι]
      exact zero_add (0 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero _ _ _) ih
  · obtain ⟨u, hu⟩ := hX.2 (φ.symm w)
    refine ⟨φ u, ?_⟩
    have hw : ι Q₂ w = CliffordAlgebra.map φ.toIsometry (ι Q₁ (φ.symm w)) := by
      rw [map_apply_ι]
      exact congrArg (ι Q₂) (φ.apply_symm_apply w).symm
    rw [hw, Ring.lie_def, ← map_mul, ← map_mul, ← map_sub, ← Ring.lie_def, ← hu, map_apply_ι]
    rfl

/-- Conjugation by a unit as a linear equivalence. -/
def conjLin {A : Type*} [Ring A] [Algebra K A] (g : Aˣ) : A ≃ₗ[K] A :=
  LinearEquiv.ofLinearMap (LinearMap.mulLeft K (g : A) ∘ₗ LinearMap.mulRight K ((g⁻¹ : Aˣ) : A))
    (LinearMap.mulLeft K ((g⁻¹ : Aˣ) : A) ∘ₗ LinearMap.mulRight K (g : A))
    (by ext a; simp [mul_assoc]) (by ext a; simp [mul_assoc])

theorem conjLin_apply {A : Type*} [Ring A] [Algebra K A] (g : Aˣ) (a : A) :
    conjLin (K := K) g a = (g : A) * a * ((g⁻¹ : Aˣ) : A) := by
  simp [conjLin, mul_assoc]

theorem conjLin_symm_apply {A : Type*} [Ring A] [Algebra K A] (g : Aˣ) (a : A) :
    (conjLin (K := K) g).symm a = ((g⁻¹ : Aˣ) : A) * a * (g : A) := by
  simp [conjLin, mul_assoc]

end GspinMaps

section WeylStable

/-- `𝔤 = gspin(W) × gspin(V)` is `Ad(G)`-stable. -/
theorem lie_conj_stable (d : GGPData F) (t : ↥d.G) :
    ∀ X ∈ d.lie.toSubmodule, conjAd F (t : d.ambientˣ) X ∈ d.lie.toSubmodule := fun _ hX =>
  ⟨conj_mem_gspin_ofGSpin d.QW (d.fst t) hX.1, conj_mem_gspin_ofGSpin d.QV (d.snd t) hX.2⟩

/-- `1 − Ad(t)` on `𝔤`. -/
abbrev oneSubAd (d : GGPData F) (t : ↥d.G) : d.lie.toSubmodule →ₗ[F] d.lie.toSubmodule :=
  1 - (conjAd F (t : d.ambientˣ)).toLinearEquiv.toLinearMap.restrict (lie_conj_stable d t)

theorem weylDisc_eq_oneSubAd (d : GGPData F) (t : ↥d.G) :
    weylDisc d.lie (t : d.ambientˣ) = absF (LinearMap.charpoly (oneSubAd d t)).trailingCoeff := by
  rw [weylDisc, dite_eq_left (lie_conj_stable d t)]

theorem gspinProdBC_oneSubAd (d : GGPData F) (t : ↥d.G)
    (u : AlgebraicClosure F ⊗[F] d.lie.toSubmodule) :
    gspinProdBC d.QW d.QV d.lie.toSubmodule ((oneSubAd d t).baseChange (AlgebraicClosure F) u) =
      gspinProdBC d.QW d.QV d.lie.toSubmodule u - adPair (bcHom d.QW ((t : d.ambientˣ) : d.ambient).1)
        (bcHom d.QW (((t : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient).1)
        (bcHom d.QV ((t : d.ambientˣ) : d.ambient).2)
        (bcHom d.QV (((t : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient).2)
        (gspinProdBC d.QW d.QV d.lie.toSubmodule u) := by
  induction u using TensorProduct.inductionOn with
  | tmul z X =>
    rw [LinearMap.baseChange_tmul, gspinProdBC_tmul, gspinProdBC_tmul]
    simp only [adPair, LinearMap.sub_apply, Module.End.one_apply, Submodule.coe_sub,
      Prod.fst_sub, Prod.snd_sub, TensorProduct.tmul_sub, map_sub, Prod.mk_sub_mk]
    refine Prod.ext ?_ ?_ <;> dsimp only <;> congr 1
    · exact ofBaseChange_tmul_mul3 d.QW z _ (X : d.ambient).1 _
    · exact ofBaseChange_tmul_mul3 d.QV z _ (X : d.ambient).2 _
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb, map_add]
    simp only [adPair, Prod.fst_add, Prod.snd_add, mul_add, add_mul]
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> abel


theorem coe_cliffUnits {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂]
    [Module F V₂] {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}
    (φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F)))
    (u : (CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F)))ˣ) :
    ((cliffUnits φ u : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ) :
      CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F))) = CliffordAlgebra.map φ.toIsometry u :=
  rfl

theorem coe_cliffUnits_inv {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂]
    [Module F V₂] {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}
    (φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F)))
    (u : (CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F)))ˣ) :
    (((cliffUnits φ u)⁻¹ : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ) :
      CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F))) =
      CliffordAlgebra.map φ.toIsometry ((u⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) :=
  rfl

/-- `Ad(g) ∘ C(φ)` intertwines `Ad(u_{F̄})` and `Ad(u'_{F̄})` when `g C(φ)(u_{F̄}) g⁻¹ = u'_{F̄}`. -/
theorem conj_intertwine_bc {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂]
    [Module F V₂] {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}
    (φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F)))
    (g : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ) (u : (CliffordAlgebra Q₁)ˣ)
    (u' : (CliffordAlgebra Q₂)ˣ) (e : g * cliffUnits φ (bcUnits Q₁ u) * g⁻¹ = bcUnits Q₂ u')
    (x : CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F))) :
    (g : CliffordAlgebra _) * CliffordAlgebra.map φ.toIsometry
        (bcHom Q₁ u * x * bcHom Q₁ ((u⁻¹ : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁)) *
        ((g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
      bcHom Q₂ u' * ((g : CliffordAlgebra _) * CliffordAlgebra.map φ.toIsometry x *
        ((g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _)) *
        bcHom Q₂ ((u'⁻¹ : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra Q₂) := by
  have key := conj_intertwine (CliffordAlgebra.map φ.toIsometry) g (cliffUnits φ (bcUnits Q₁ u))
    (bcHom Q₁ u) (bcHom Q₁ ((u⁻¹ : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁))
    (coe_cliffUnits φ _) (coe_cliffUnits_inv φ _) x
  rw [e] at key
  exact key


section PsiPair

variable {V₁ V₂ V₁' V₂' : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
  [AddCommGroup V₁'] [Module F V₁'] [AddCommGroup V₂'] [Module F V₂']
  {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂} {Q₁' : QuadraticForm F V₁'}
  {Q₂' : QuadraticForm F V₂'}

/-- `ψ = (Ad(g₁) ∘ C(φ₁), Ad(g₂) ∘ C(φ₂))` on `C(Q₁)_{F̄} × C(Q₂)_{F̄}`. -/
def psiPair
    (φ₁ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₁'.baseChange (AlgebraicClosure F)))
    (φ₂ : (Q₂.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂'.baseChange (AlgebraicClosure F)))
    (g₁ : (CliffordAlgebra (Q₁'.baseChange (AlgebraicClosure F)))ˣ)
    (g₂ : (CliffordAlgebra (Q₂'.baseChange (AlgebraicClosure F)))ˣ) :
    (CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F)) ×
      CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F))) ≃ₗ[AlgebraicClosure F]
    (CliffordAlgebra (Q₁'.baseChange (AlgebraicClosure F)) ×
      CliffordAlgebra (Q₂'.baseChange (AlgebraicClosure F))) :=
  ((CliffordAlgebra.equivOfIsometry φ₁).toLinearEquiv.trans
      (conjLin (K := AlgebraicClosure F) g₁)).prodCongr
    ((CliffordAlgebra.equivOfIsometry φ₂).toLinearEquiv.trans
      (conjLin (K := AlgebraicClosure F) g₂))

variable
    (φ₁ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₁'.baseChange (AlgebraicClosure F)))
    (φ₂ : (Q₂.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂'.baseChange (AlgebraicClosure F)))
    (g₁ : (CliffordAlgebra (Q₁'.baseChange (AlgebraicClosure F)))ˣ)
    (g₂ : (CliffordAlgebra (Q₂'.baseChange (AlgebraicClosure F)))ˣ)

theorem psiPair_apply (p : CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F)) ×
      CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F))) :
    psiPair φ₁ φ₂ g₁ g₂ p =
      ((g₁ : CliffordAlgebra _) * CliffordAlgebra.map φ₁.toIsometry p.1 *
          ((g₁⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _),
        (g₂ : CliffordAlgebra _) * CliffordAlgebra.map φ₂.toIsometry p.2 *
          ((g₂⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _)) := by
  simp only [psiPair, LinearEquiv.prodCongr_apply, LinearEquiv.trans_apply,
    AlgEquiv.toLinearEquiv_apply, CliffordAlgebra.equivOfIsometry_apply, conjLin_apply]

theorem psiPair_symm_apply (p : CliffordAlgebra (Q₁'.baseChange (AlgebraicClosure F)) ×
      CliffordAlgebra (Q₂'.baseChange (AlgebraicClosure F))) :
    (psiPair φ₁ φ₂ g₁ g₂).symm p =
      (CliffordAlgebra.map φ₁.symm.toIsometry (((g₁⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) *
          p.1 * (g₁ : CliffordAlgebra _)),
        CliffordAlgebra.map φ₂.symm.toIsometry (((g₂⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) *
          p.2 * (g₂ : CliffordAlgebra _))) := by
  simp only [psiPair, LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply,
    LinearEquiv.symm_trans_apply, conjLin_symm_apply]
  rfl

/-- `ψ` maps `gspin(Q₁) × gspin(Q₂)` onto `gspin(Q₁') × gspin(Q₂')` (over `F̄`). -/
theorem psiPair_map_gspin (hg₁ : g₁ ∈ GSpin (Q₁'.baseChange (AlgebraicClosure F)))
    (hg₂ : g₂ ∈ GSpin (Q₂'.baseChange (AlgebraicClosure F))) :
    ((gspin (Q₁.baseChange (AlgebraicClosure F))).toSubmodule.prod
        (gspin (Q₂.baseChange (AlgebraicClosure F))).toSubmodule).map
        (psiPair φ₁ φ₂ g₁ g₂ : _ →ₗ[AlgebraicClosure F] _) =
      (gspin (Q₁'.baseChange (AlgebraicClosure F))).toSubmodule.prod
        (gspin (Q₂'.baseChange (AlgebraicClosure F))).toSubmodule := by
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    rw [LinearEquiv.coe_coe, psiPair_apply]
    exact ⟨conj_mem_gspin_ofGSpin _ ⟨g₁, hg₁⟩ (map_mem_gspin φ₁ hp.1),
      conj_mem_gspin_ofGSpin _ ⟨g₂, hg₂⟩ (map_mem_gspin φ₂ hp.2)⟩
  · intro q hq
    refine ⟨(psiPair φ₁ φ₂ g₁ g₂).symm q, ?_, (psiPair φ₁ φ₂ g₁ g₂).apply_symm_apply q⟩
    rw [psiPair_symm_apply]
    refine ⟨map_mem_gspin φ₁.symm ?_, map_mem_gspin φ₂.symm ?_⟩
    · simpa using conj_mem_gspin_ofGSpin _ (⟨g₁, hg₁⟩⁻¹ : GSpin _) hq.1
    · simpa using conj_mem_gspin_ofGSpin _ (⟨g₂, hg₂⟩⁻¹ : GSpin _) hq.2

/-- `ψ` intertwines `1 − Ad(u)` and `1 − Ad(u')` when `ψ(u) = u'` componentwise. -/
theorem psiPair_intertwine (u₁ : (CliffordAlgebra Q₁)ˣ) (u₂ : (CliffordAlgebra Q₂)ˣ)
    (u₁' : (CliffordAlgebra Q₁')ˣ) (u₂' : (CliffordAlgebra Q₂')ˣ)
    (e₁ : g₁ * cliffUnits φ₁ (bcUnits Q₁ u₁) * g₁⁻¹ = bcUnits Q₁' u₁')
    (e₂ : g₂ * cliffUnits φ₂ (bcUnits Q₂ u₂) * g₂⁻¹ = bcUnits Q₂' u₂')
    (p : CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F)) ×
      CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F))) :
    psiPair φ₁ φ₂ g₁ g₂ (p - adPair (bcHom Q₁ u₁)
        (bcHom Q₁ ((u₁⁻¹ : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁)) (bcHom Q₂ u₂)
        (bcHom Q₂ ((u₂⁻¹ : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra Q₂)) p) =
      psiPair φ₁ φ₂ g₁ g₂ p - adPair (bcHom Q₁' u₁')
        (bcHom Q₁' ((u₁'⁻¹ : (CliffordAlgebra Q₁')ˣ) : CliffordAlgebra Q₁')) (bcHom Q₂' u₂')
        (bcHom Q₂' ((u₂'⁻¹ : (CliffordAlgebra Q₂')ˣ) : CliffordAlgebra Q₂'))
        (psiPair φ₁ φ₂ g₁ g₂ p) := by
  rw [map_sub, psiPair_apply, psiPair_apply]
  simp only [adPair]
  rw [conj_intertwine_bc φ₁ g₁ u₁ u₁' e₁, conj_intertwine_bc φ₂ g₂ u₂ u₂' e₂]

end PsiPair

theorem coe_fst_val (d : GGPData F) (g : ↥d.G) :
    (((d.fst g : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) =
      ((g : d.ambientˣ) : d.ambient).1 := rfl

theorem coe_fst_inv_val (d : GGPData F) (g : ↥d.G) :
    ((((d.fst g : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) :
      CliffordAlgebra d.QW) = (((g : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient).1 := rfl

theorem coe_snd_val (d : GGPData F) (g : ↥d.G) :
    (((d.snd g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) =
      ((g : d.ambientˣ) : d.ambient).2 := rfl

theorem coe_snd_inv_val (d : GGPData F) (g : ↥d.G) :
    ((((d.snd g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ)⁻¹ : (CliffordAlgebra d.QV)ˣ) :
      CliffordAlgebra d.QV) = (((g : d.ambientˣ)⁻¹ : d.ambientˣ) : d.ambient).2 := rfl

/-- `gspinProdBC_oneSubAd` with the components of `t` written as `fst t`, `snd t`. -/
theorem gspinProdBC_oneSubAd' (d : GGPData F) (t : ↥d.G)
    (u : AlgebraicClosure F ⊗[F] d.lie.toSubmodule) :
    gspinProdBC d.QW d.QV d.lie.toSubmodule ((oneSubAd d t).baseChange (AlgebraicClosure F) u) =
      gspinProdBC d.QW d.QV d.lie.toSubmodule u -
        adPair (bcHom d.QW ((d.fst t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
          (bcHom d.QW (((d.fst t : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) :
            CliffordAlgebra d.QW))
          (bcHom d.QV ((d.snd t : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV))
          (bcHom d.QV (((d.snd t : (CliffordAlgebra d.QV)ˣ)⁻¹ : (CliffordAlgebra d.QV)ˣ) :
            CliffordAlgebra d.QV))
          (gspinProdBC d.QW d.QV d.lie.toSubmodule u) := by
  rw [gspinProdBC_oneSubAd, coe_fst_val, coe_fst_inv_val, coe_snd_val, coe_snd_inv_val]

set_option maxHeartbeats 400000 in
/-- `D^G` is unchanged under stable conjugacy through isometries `φ_W, φ_V` (general form of
`weylDisc_eq_of_stablyConjG`, stated for two arbitrary GGP data so that nothing is unfolded). -/
theorem weylDisc_eq_of_conj (d d₂ : GGPData F)
    (φW : (d.QW.baseChange (AlgebraicClosure F)).IsometryEquiv
      (d₂.QW.baseChange (AlgebraicClosure F)))
    (φV : (d.QV.baseChange (AlgebraicClosure F)).IsometryEquiv
      (d₂.QV.baseChange (AlgebraicClosure F)))
    (t : ↥d.G) (t' : ↥d₂.G)
    (hW : StablyConjVia φW (d.fst t : (CliffordAlgebra d.QW)ˣ) (d₂.fst t' : (CliffordAlgebra d₂.QW)ˣ))
    (hV : StablyConjVia φV (d.snd t : (CliffordAlgebra d.QV)ˣ) (d₂.snd t' : (CliffordAlgebra d₂.QV)ˣ)) :
    weylDisc d₂.lie (t' : d₂.ambientˣ) = weylDisc d.lie (t : d.ambientˣ) := by
  obtain ⟨g₁, hg₁, e₁⟩ := hW
  obtain ⟨g₂, hg₂, e₂⟩ := hV
  rw [weylDisc_eq_oneSubAd, weylDisc_eq_oneSubAd]
  have hS := range_gspinProdBC d.QW d.QV d.lie.toSubmodule (fun _ => Iff.rfl)
    (isNondeg_baseChange _ d.nondeg) (isNondeg_baseChange _ d.nondeg_QV)
  have hS' := range_gspinProdBC d₂.QW d₂.QV d₂.lie.toSubmodule
    (fun _ => Iff.rfl) (isNondeg_baseChange _ d₂.nondeg)
    (isNondeg_baseChange _ d₂.nondeg_QV)
  set S := (gspin (d.QW.baseChange (AlgebraicClosure F))).toSubmodule.prod
    (gspin (d.QV.baseChange (AlgebraicClosure F))).toSubmodule
  set S' := (gspin (d₂.QW.baseChange (AlgebraicClosure F))).toSubmodule.prod
    (gspin (d₂.QV.baseChange (AlgebraicClosure F))).toSubmodule
  let e := (LinearEquiv.ofInjective _ (gspinProdBC_injective d.QW d.QV d.lie.toSubmodule)).trans
    (LinearEquiv.ofEq _ _ hS)
  let e' := (LinearEquiv.ofInjective _ (gspinProdBC_injective d₂.QW d₂.QV
    d₂.lie.toSubmodule)).trans (LinearEquiv.ofEq _ _ hS')
  have hΨ : S.map ((psiPair φW φV g₁ g₂) : _ →ₗ[AlgebraicClosure F] _) = S' := psiPair_map_gspin φW φV g₁ g₂ hg₁ hg₂
  let E := e.trans (((psiPair φW φV g₁ g₂).ofSubmodules S S' hΨ).trans e'.symm)
  have hEv : ∀ v, ((e' (E v) : S') : _ × _) = (psiPair φW φV g₁ g₂) (gspinProdBC d.QW d.QV d.lie.toSubmodule v) := by
    intro v
    simp only [E, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.ofSubmodules_apply]
    rfl
  have hint := psiPair_intertwine φW φV g₁ g₂ (d.fst t : (CliffordAlgebra d.QW)ˣ)
    (d.snd t : (CliffordAlgebra d.QV)ˣ) (d₂.fst t' : (CliffordAlgebra d₂.QW)ˣ)
    (d₂.snd t' : (CliffordAlgebra d₂.QV)ˣ) e₁ e₂
  have he' : ∀ v, ((e' v : S') : _ × _) =
      gspinProdBC d₂.QW d₂.QV d₂.lie.toSubmodule v := fun v => by
    simp only [e', LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
      LinearEquiv.ofInjective_apply]
  have hE : ∀ v, gspinProdBC d₂.QW d₂.QV d₂.lie.toSubmodule (E v) =
      (psiPair φW φV g₁ g₂) (gspinProdBC d.QW d.QV d.lie.toSubmodule v) := fun v => (he' (E v)).symm.trans (hEv v)
  have hcomm : ∀ u, (oneSubAd d₂ t').baseChange (AlgebraicClosure F) (E u) =
      E ((oneSubAd d t).baseChange (AlgebraicClosure F) u) := by
    intro u
    apply gspinProdBC_injective d₂.QW d₂.QV d₂.lie.toSubmodule
    rw [gspinProdBC_oneSubAd' d₂ t' (E u), hE u,
      hE ((oneSubAd d t).baseChange (AlgebraicClosure F) u), gspinProdBC_oneSubAd' d t u, hint]
  have hc := charpoly_eq_of_intertwine _ _ E hcomm
  rw [LinearMap.charpoly_baseChange, LinearMap.charpoly_baseChange] at hc
  rw [Polynomial.map_injective _ (algebraMap F (AlgebraicClosure F)).injective hc]

end WeylStable

end EndElemWeyl

/-- **`D^G` is invariant under stable conjugacy** (own work, elementary): `ψ_τ ∘ Ad(g)` maps
`𝔤 ⊗ F̄` onto `𝔤_τ ⊗ F̄` (`C(φ)` maps `gspin(W)_{F̄}` onto `gspin(W_τ)_{F̄}`, and likewise for `V`)
and conjugates `1 − Ad(t)` to `1 − Ad(t')`; characteristic polynomials over `F` are unchanged by
base change, so the trailing coefficients agree. -/
theorem weylDisc_eq_of_stablyConjG (τ : InnerTwist d.QW) (t : ↥d.G) (t' : ↥(d.twist τ).G)
    (h : d.StablyConjG τ t t') :
    weylDisc (d.twist τ).lie (t' : (d.twist τ).ambientˣ) = weylDisc d.lie (t : d.ambientˣ) :=
  weylDisc_eq_of_conj d (d.twist τ) τ.φ (d.twistV τ) t t' h.1 h.2

/-- **Thesis Prop. 6.6.1(ii), the torus isomorphism** (own work): the clauses of `TorusTransfer`
other than `Δ`, `D^G`, together with: every `t ∈ T_x(F)` is stably conjugate to `e(t)` (in `G`,
through `ψ_α`).  Route: take `g` (the `W`-component) from `hxy`; `t ↦ g C(φ_α)(t) g⁻¹`
sends `T_x(F)` into `GSpin(W_α)(F̄)`, and its values are Galois-fixed by the rationality clause of
`StronglyStablyConjVia` (`T_x ⊆ Z(x)`), hence rational (Galois descent for `C(W_α) ⊗ F̄`); they
commute with `y` and fix `W'_y = P(g)φ_α(W'_x)`, so lie in `T_y(F)`.  The inverse is built the same
way from `g⁻¹`; continuity: the map is the restriction of an `F`-linear map between
finite-dimensional spaces (the `F`-span of `T_x(F)` in `C(W)` and `C(W_α)`).  Scalars are fixed and
`x ↦ y` by construction; `T_{x,♮} ↔ T_{y,♮}` and strong stable conjugacy on `T_{x,♮}` because
`G_t = G_x` there (`T_y` central in `G_{α,y}`); stable conjugacy of `t` and `e(t)`
uses `g` and its image in `GSpin(V_α)(F̄)`. -/
theorem exists_torusTransfer_core (IF : InnerFormSystem d) (α : IF.Idx)
    (x : ↥(GSpin d.QW)) (y : ↥(GSpin (IF.data α).QW)) (hx : d.IsGammaElt x)
    (hy : (IF.data α).IsGammaElt y) (hxy : d.StronglyStablyConjW (IF.twist α) x y) :
    ∃ e : ↥(d.torusOf x) ≃* ↥((IF.data α).torusOf y),
      Continuous e ∧ Continuous e.symm ∧
      (∀ c : Fˣ, ((e ⟨scalarGSpin d.QW c, d.scalar_mem_torusOf x c⟩ : ↥((IF.data α).torusOf y)) :
          ↥(GSpin (IF.data α).QW)) = scalarGSpin (IF.data α).QW c) ∧
      (∀ t : ↥(d.torusOf x), (t : ↥(GSpin d.QW)) = x → (e t : ↥(GSpin (IF.data α).QW)) = y) ∧
      (∀ t : ↥(d.torusOf x),
        (d.IsGammaElt t ∧ d.torusOf t = d.torusOf x ↔
          (IF.data α).IsGammaElt (e t) ∧ (IF.data α).torusOf (e t) = (IF.data α).torusOf y)) ∧
      (∀ t : ↥(d.torusOf x), d.IsGammaElt t → d.torusOf t = d.torusOf x →
        d.StronglyStablyConjW (IF.twist α) t (e t)) ∧
      (∀ t : ↥(d.torusOf x), d.StablyConjG (IF.twist α) (d.diag t) ((IF.data α).diag (e t))) :=
  sorry

/-- **Thesis Prop. 6.6.1(ii)** (own work).
If `x ∈ Γ(G,H)` and `y ∈ Γ(G_α,H_α)` are strongly stably conjugate, `Ad(g) ∘ ψ_α` restricts to an
isomorphism `T_x ≃ T_y` defined over `F` (so it is an isomorphism of topological groups
`T_x(F) ≃ T_y(F)`), independent of `g`, which is the identity on the central `A_{G,H} = G_m`
(hence induces `S_x ≃ S_y`).  It maps `x ↦ y` and the regular part
`T_{x,♮} = {t ∈ Γ(G,H) | T_t = T_x}` onto `T_{y,♮}`, every `t ∈ T_{x,♮}` being strongly stably
conjugate to its image; and it preserves `D^G` and `Δ`.  So the two `Γ`-integrals over
`T_x(F)/A(F)` and `T_y(F)/A(F)` (probability Haar measures) match locally, which is what
Thesis §6.7 uses.  It does *not* preserve `|W(T)|` in general (see `TorusTransfer`). -/
theorem prop_12_5_1_ii (IF : InnerFormSystem d) (α : IF.Idx)
    (x : ↥(GSpin d.QW)) (y : ↥(GSpin (IF.data α).QW)) (hx : d.IsGammaElt x)
    (hy : (IF.data α).IsGammaElt y) (hxy : d.StronglyStablyConjW (IF.twist α) x y) :
    TorusTransfer IF α x y := by
  obtain ⟨e, h1, h2, h3, h4, h5, h6, hst⟩ := exists_torusTransfer_core IF α x y hx hy hxy
  exact ⟨e, h1, h2, h3, h4, h5, h6, fun t =>
    ⟨deltaGGP_eq_of_stablyConjVia (IF.twist α) t (e t) (hst t).1,
      weylDisc_eq_of_stablyConjG (IF.twist α) _ _ (hst t)⟩⟩

/-! ### `H¹(F, S_x)` and the map `q_x` (Thesis Prop. 6.6.1(iii); Galois cohomology in
`Literature/Kottwitz.lean`) -/

/-- **Thesis Prop. 6.6.1(iii)** (own work): for `x ∈ Γ(G,H)` and every
inner form `α`, the `GSpin(W_α)(F)`-classes of `y ∈ Γ(G_α,H_α)` strongly stably conjugate to `x`
are in bijection with `q_x⁻¹(α) ⊆ H¹(F, S_x)`.  This differs from Thesis Prop. 6.6.1(iii), which
uses `H¹(F, T_x)`.  Proof route:
Galois cohomology parametrizes the `G_α(F)`-classes of all semisimple
`y ∼_stab x` by `Im(H¹(F, Z(Ḡ_x)) → H¹(F, Ḡ_x)) ∩ p_x⁻¹([a_α])`
(here `G_α(F)`-, `Ḡ_α(F)`- and `GSpin(W_α)(F)`-conjugacy agree on diagonal elements, as
`GSpin → SO` is onto on `F`-points by Hilbert 90 for `G_m`); those with `y ∈ Γ(G_α,H_α)` form the
triple intersection, which is `{(1,1,s,s)} ≅ H¹(F, S_x)` by the case analysis on
`dim W'_x` and Witt cancellation, and `p_x = [a_α]` becomes `q_x(s) = α`. -/
theorem n_alpha_eq_card_twistIdx (IF : InnerFormSystem d) (α : IF.Idx) (x : ↥(GSpin d.QW))
    (hx : d.IsGammaElt x) :
    n_alpha IF α x = Nat.card {β : H1 (d.torusBarFbar x) // TwistIdx IF x β α} :=
  sorry

/-- **`q_x` is a function** `H¹(F, S_x) → IF.Idx` (own work; standard descent).  Existence: by
Hilbert 90 for `GL_m` (Serre, *Local Fields*, X §1 Prop. 3) a cocycle `a` with values in
`S_x(F̄) ⊆ SO(W)(F̄)` is `a_σ = M⁻¹ σ(M)`; then `v ↦ Q_{F̄}(M⁻¹ v)` is an `F`-valued nondegenerate
form on `F^m` of the discriminant of `W` (`det a_σ = 1`), isometric to a unique `W_α`
(`IF.classify`).  Uniqueness: if `φ, φ'` have cohomologous cocycles `a`, `a' = c⁻¹ a σ(c)`
(`c ∈ S_x(F̄)`), then `φ' c⁻¹ φ⁻¹ : W_{α,F̄} ≃ W_{α',F̄}` is Galois-invariant, hence defined over
`F`, so `α = α'` (`IF.classify`).  Proved (`GGP/TwistDescent.lean`; the only cited input is
`hilbert90_GL`). -/
theorem existsUnique_twistIdx (IF : InnerFormSystem d) (x : ↥(GSpin d.QW))
    (β : H1 (d.torusBarFbar x)) : ∃! α, TwistIdx IF x β α := by
  have hS := TwistDescent.gram_mem_torusBarFbar d x
  have hSdet := TwistDescent.det_mem_torusBarFbar d x
  -- existence: split a representative by Hilbert 90 and descend
  obtain ⟨M, hM⟩ := hilbert90_GL (Quotient.out β)
  obtain ⟨Q'', hnd, hdisc, htw⟩ :=
    TwistDescent.exists_twist_of_split d.nondeg hS hSdet (Quotient.out β) M hM
  obtain ⟨α, ⟨ψ⟩, -⟩ := IF.classify Q'' hnd hdisc
  refine ⟨α, ⟨Quotient.out β, H1.mk_out β, TwistDescent.isTwistBy_of_isometryEquiv ψ htw⟩, ?_⟩
  -- uniqueness: cohomologous cocycles twist into isometric forms
  rintro α' ⟨a', ha', htw'⟩
  have hrel : GalCocycle.Rel (Quotient.out β) a' :=
    H1.mk_eq_mk.1 ((H1.mk_out β).trans ha'.symm)
  obtain ⟨e⟩ := TwistDescent.nonempty_isometryEquiv_of_rel hS hrel
    (TwistDescent.isTwistBy_of_isometryEquiv ψ htw) htw'
  have hu := IF.classify (IF.twist α).Q' (IF.twist α).nondeg' (IF.twist α).sameDisc
  exact hu.unique ⟨e⟩ ⟨QuadraticMap.IsometryEquiv.refl _⟩

/-! ### Helpers for `galGL_mem_torusBarFbar`: the Galois action on `F̄ ⊗ V` and `C(V)_{F̄}`
(own work, elementary) -/

section EndElemGal

open CliffordAlgebra
open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- The Galois action `σ ⊗ 1` on `F̄ ⊗ V` (an `F`-linear, `σ`-semilinear map). -/
def galV (σ : GalF F) : AlgebraicClosure F ⊗[F] V →ₗ[F] AlgebraicClosure F ⊗[F] V :=
  LinearMap.rTensor V (σ : AlgebraicClosure F →ₐ[F] AlgebraicClosure F).toLinearMap

theorem galV_tmul (σ : GalF F) (z : AlgebraicClosure F) (v : V) :
    galV σ (z ⊗ₜ[F] v) = σ z ⊗ₜ[F] v := rfl

theorem galV_smul (σ : GalF F) (c : AlgebraicClosure F) (w : AlgebraicClosure F ⊗[F] V) :
    galV σ (c • w) = σ c • galV σ w := by
  induction w using TensorProduct.inductionOn with
  | tmul z v => rw [TensorProduct.smul_tmul', galV_tmul, galV_tmul, smul_eq_mul, map_mul,
      TensorProduct.smul_tmul', smul_eq_mul]
  | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]

theorem galV_mul (σ τ : GalF F) (w : AlgebraicClosure F ⊗[F] V) :
    galV σ (galV τ w) = galV (σ * τ) w := by
  induction w using TensorProduct.inductionOn with
  | tmul z v => rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

theorem galV_one (w : AlgebraicClosure F ⊗[F] V) : galV (1 : GalF F) w = w := by
  induction w using TensorProduct.inductionOn with
  | tmul z v => rfl
  | add a b ha hb => rw [map_add, ha, hb]

theorem galV_inv_galV (σ : GalF F) (w : AlgebraicClosure F ⊗[F] V) :
    galV σ⁻¹ (galV σ w) = w := by
  rw [galV_mul, inv_mul_cancel, galV_one]

theorem galV_galV_inv (σ : GalF F) (w : AlgebraicClosure F ⊗[F] V) :
    galV σ (galV σ⁻¹ w) = w := by
  rw [galV_mul, mul_inv_cancel, galV_one]

/-- `σ` preserves `p ⊗ F̄` for an `F`-subspace `p`. -/
theorem galV_mem_baseChange (σ : GalF F) (p : Submodule F V) {w : AlgebraicClosure F ⊗[F] V}
    (hw : w ∈ p.baseChange (AlgebraicClosure F)) : galV σ w ∈ p.baseChange (AlgebraicClosure F) := by
  obtain ⟨u, rfl⟩ := hw
  induction u using TensorProduct.inductionOn with
  | tmul z v => exact Submodule.tmul_mem_baseChange_of_mem _ v.2
  | add a b ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb

/-- The coordinates of `σ w` in the rational basis are `σ` of those of `w`. -/
theorem bcBasis_repr_galV {m : ℕ} (σ : GalF F) (w : AlgebraicClosure F ⊗[F] (Fin m → F))
    (i : Fin m) : (bcBasis F m).repr (galV σ w) i = σ ((bcBasis F m).repr w i) := by
  induction w using TensorProduct.inductionOn with
  | tmul z v =>
    rw [galV_tmul, bcBasis, Module.Basis.baseChange_repr_tmul, Module.Basis.baseChange_repr_tmul,
      Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]
  | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb]

theorem galV_bcBasis {m : ℕ} (σ : GalF F) (j : Fin m) :
    galV σ (bcBasis F m j) = bcBasis F m j := by
  rw [bcBasis, Module.Basis.baseChange_apply, galV_tmul, map_one]

/-- If `f'` is the Galois conjugate of `f` (`f' ∘ σ = σ ∘ f`), its matrix in the rational basis is
`σ` applied entrywise. -/
theorem toMatrix_of_galV_comm {m : ℕ} (σ : GalF F)
    (f f' : (AlgebraicClosure F ⊗[F] (Fin m → F)) →ₗ[AlgebraicClosure F]
      (AlgebraicClosure F ⊗[F] (Fin m → F)))
    (h : ∀ w, f' (galV σ w) = galV σ (f w)) :
    LinearMap.toMatrix (bcBasis F m) (bcBasis F m) f' =
      (LinearMap.toMatrix (bcBasis F m) (bcBasis F m) f).map σ := by
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, ← galV_bcBasis σ j, h,
    bcBasis_repr_galV, galV_bcBasis]

/-! Galois action on the Clifford algebra -/

/-- `σ(ι(w)) = ι(σ w)` in `C(V)_{F̄} ≅ F̄ ⊗ C(V)`. -/
theorem galC_ι (Q : QuadraticForm F V) (σ : GalF F) (w : AlgebraicClosure F ⊗[F] V) :
    galC Q σ (ι (Q.baseChange (AlgebraicClosure F)) w) =
      ι (Q.baseChange (AlgebraicClosure F)) (galV σ w) := by
  induction w using TensorProduct.inductionOn with
  | tmul z v =>
    simp only [galC, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, toBaseChange_ι, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
      ofBaseChange_tmul_ι, galV_tmul]
    rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- `σ` acts on the scalars `F̄ ⊆ C(V)_{F̄}` by `σ`. -/
theorem galC_algebraMap (Q : QuadraticForm F V) (σ : GalF F) (c : AlgebraicClosure F) :
    galC Q σ (algebraMap (AlgebraicClosure F) (CliffordAlgebra (Q.baseChange (AlgebraicClosure F))) c)
      = algebraMap _ _ (σ c) := by
  simp only [galC, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, Algebra.TensorProduct.map_tmul, map_one]
  rw [ofBaseChange_tmul_one]
  rfl

/-- `σ` fixes the rational elements `C(V) ⊆ C(V)_{F̄}`. -/
theorem galC_bcHom (Q : QuadraticForm F V) (σ : GalF F) (a : CliffordAlgebra Q) :
    galC Q σ (bcHom Q a) = bcHom Q a := by
  simp only [galC, bcHom, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply, toBaseChange_ofBaseChange,
    Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq]

/-- `galC` is an action of `Γ_F`. -/
theorem galC_galC (Q : QuadraticForm F V) (σ τ : GalF F)
    (a : CliffordAlgebra (Q.baseChange (AlgebraicClosure F))) :
    galC Q σ (galC Q τ a) = galC Q (σ * τ) a := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => rw [galC_algebraMap, galC_algebraMap, galC_algebraMap]; rfl
  | ι x => rw [galC_ι, galC_ι, galC_ι, galV_mul]
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

theorem galC_one (Q : QuadraticForm F V) (a : CliffordAlgebra (Q.baseChange (AlgebraicClosure F))) :
    galC Q (1 : GalF F) a = a := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => rw [galC_algebraMap]; rfl
  | ι x => rw [galC_ι, galV_one]
  | mul a b ha hb => rw [map_mul, ha, hb]
  | add a b ha hb => rw [map_add, ha, hb]

/-- `σ` preserves the even Clifford algebra. -/
theorem galC_mem_even (Q : QuadraticForm F V) (σ : GalF F)
    {a : CliffordAlgebra (Q.baseChange (AlgebraicClosure F))}
    (ha : a ∈ even (Q.baseChange (AlgebraicClosure F))) :
    galC Q σ a ∈ even (Q.baseChange (AlgebraicClosure F)) := by
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at ha ⊢
  induction a, ha using even_induction with
  | algebraMap r => rw [galC_algebraMap]; exact SetLike.algebraMap_mem_graded _ _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul, galC_ι, galC_ι]
    exact zero_add (0 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero _ _ _) ih

/-- `galC` on units. -/
def galCU (Q : QuadraticForm F V) (σ : GalF F) :
    (CliffordAlgebra (Q.baseChange (AlgebraicClosure F)))ˣ →*
      (CliffordAlgebra (Q.baseChange (AlgebraicClosure F)))ˣ :=
  Units.map (galC Q σ).toMonoidHom

theorem coe_galCU (Q : QuadraticForm F V) (σ : GalF F)
    (g : (CliffordAlgebra (Q.baseChange (AlgebraicClosure F)))ˣ) :
    ((galCU Q σ g : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) = galC Q σ g := rfl

theorem coe_galCU_inv (Q : QuadraticForm F V) (σ : GalF F)
    (g : (CliffordAlgebra (Q.baseChange (AlgebraicClosure F)))ˣ) :
    (((galCU Q σ g)⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
      galC Q σ ((g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) := by
  rw [← map_inv]; rfl

/-- `σ` preserves `GSpin(V)(F̄)`: it preserves `C⁺` and maps `ι(F̄ ⊗ V)` onto itself. -/
theorem galCU_mem_GSpin (Q : QuadraticForm F V) (σ : GalF F)
    {g : (CliffordAlgebra (Q.baseChange (AlgebraicClosure F)))ˣ}
    (hg : g ∈ GSpin (Q.baseChange (AlgebraicClosure F))) :
    galCU Q σ g ∈ GSpin (Q.baseChange (AlgebraicClosure F)) := by
  obtain ⟨h0, h1, h2⟩ := hg
  refine ⟨galC_mem_even Q σ h0, fun v => ?_, fun v => ?_⟩
  · obtain ⟨w, hw⟩ := h1 (galV σ⁻¹ v)
    refine ⟨galV σ w, ?_⟩
    rw [← galC_ι, hw, map_mul, map_mul, galC_ι, galV_galV_inv, coe_galCU_inv, coe_galCU]
  · obtain ⟨w, hw⟩ := h2 (galV σ⁻¹ v)
    refine ⟨galV σ w, ?_⟩
    rw [← galC_ι, hw, map_mul, map_mul, galC_ι, galV_galV_inv, coe_galCU_inv, coe_galCU]

/-- `galC` on `GSpin(Q)(F̄)`. -/
def galGS (Q : QuadraticForm F V) (σ : GalF F) (g : GSpin (Q.baseChange (AlgebraicClosure F))) :
    GSpin (Q.baseChange (AlgebraicClosure F)) :=
  ⟨galCU Q σ g, galCU_mem_GSpin Q σ g.2⟩

/-- `P(σ g) ∘ σ = σ ∘ P(g)`. -/
theorem specP_galGS (Q : QuadraticForm F V) (σ : GalF F)
    (g : GSpin (Q.baseChange (AlgebraicClosure F))) (w : AlgebraicClosure F ⊗[F] V) :
    specP (Q.baseChange (AlgebraicClosure F)) (galGS Q σ g) (galV σ w) =
      galV σ (specP (Q.baseChange (AlgebraicClosure F)) g w) := by
  apply ι_injective (Q.baseChange (AlgebraicClosure F))
  rw [ι_specP, ← galC_ι Q σ (specP _ g w), ι_specP, map_mul, map_mul, galC_ι]
  rfl

/-- `σ(T_x(F̄)) = T_x(F̄)`: `σ` fixes `x` (`galC_bcHom`) and preserves `W'_x ⊗ F̄`. -/
theorem galGS_mem_torusFbar (x : ↥(GSpin d.QW)) (σ : GalF F)
    {g : GSpin (d.QW.baseChange (AlgebraicClosure F))} (hg : g ∈ d.torusFbar x) :
    galGS d.QW σ g ∈ d.torusFbar x := by
  refine ⟨?_, fun w hw => ?_⟩
  · have hc := Units.ext_iff.1 hg.1
    have hb : ((bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ) : (CliffordAlgebra _)ˣ) :
        CliffordAlgebra _) = galC d.QW σ (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ) :
          (CliffordAlgebra _)ˣ) := (galC_bcHom d.QW σ _).symm
    apply Units.ext
    show galC d.QW σ _ * _ = _ * galC d.QW σ _
    simp only [Units.val_mul] at hc
    rw [hb, ← map_mul, ← map_mul, hc]
  · have hw' := galV_mem_baseChange σ⁻¹ _ hw
    rw [← galV_galV_inv σ w, specP_galGS, hg.2 _ hw']

end EndElemGal

/-- **`S_x(F̄)` is commutative** for `x ∈ Γ(G,H)` (own work).  Route: `S_x(F̄) =
Z_{SO(W''_x)}(x̄)⁰(F̄)` is the `F̄`-points of a connected reductive group
whose `F`-points `T_x(F)/A_{G,H}(F)` commute (`IsGammaElt`); `F`-points are Zariski dense
(Borel, *Linear Algebraic Groups*, 18.3), so it is commutative.

Density-free route (not yet formalized): the Lie algebra `L` of the moved part (centralizer of
`x` in `gspin(W)` killing `ι(W'_x)`) is abelian over `F` (`movedPartAbelian_of_isGammaElt`, proved),
hence over `F̄` (`L` is cut out by `F`-linear equations and `gspin` commutes with base change,
`range_gspinBC`); so on `W''_x ⊗ F̄` every eigenvalue `λ ≠ -1` of the semisimple `x̄` is simple and
`-1` has multiplicity `≤ 2` (otherwise `gl(E_λ)` or `so(E_{-1})` would sit in `L ⊗ F̄`). An element
of `S_x(F̄)` preserves the eigenspaces, acts by scalars on the lines and by `SO(E_{-1})` on `E_{-1}`
(the paired lines contribute determinant `1`), and such elements commute. -/
theorem torusBarFbar_commute (x : ↥(GSpin d.QW)) (hx : d.IsGammaElt x) :
    ∀ s ∈ d.torusBarFbar x, ∀ t ∈ d.torusBarFbar x, Commute s t :=
  sorry

/-- **`S_x(F̄)` is Galois-stable** (own work, elementary): `σ` acts on `GSpin(W)(F̄)` by `galC`,
fixes `x` and `W'_x ⊗ F̄` (both are defined over `F`), and `P` is defined over `F`, so the matrix of
`P(σ g)` is `σ` applied to that of `P(g)`. -/
theorem galGL_mem_torusBarFbar (x : ↥(GSpin d.QW)) (σ : GalF F) :
    ∀ s ∈ d.torusBarFbar x, galGL d.m σ s ∈ d.torusBarFbar x := by
  rintro s ⟨g, hg, rfl⟩
  refine ⟨_, galGS_mem_torusFbar x σ hg, ?_⟩
  apply Units.ext
  rw [coe_specMatFbar, coe_galGL, coe_specMatFbar]
  exact toMatrix_of_galV_comm σ _ _ fun w => specP_galGS d.QW σ g w

/-- **Surjectivity of the Kottwitz sign on `H¹(F, S_x)`** (own work on top of
BP (12.1.6)): for `G` quasi-split
and `x ∈ Γ(G,H)` not central, some `β ∈ H¹(F, S_x)` has `e(G_{q_x(β)}) = -1`.  Route: by
BP (12.1.6) ("if" direction, Tate–Nakayama: `H²(F, S~) = 0` for an anisotropic torus) it suffices
that the inverse image `S~_x` of `S_x` in `Ḡ~ = SO(U_ev) × Spin(U_odd)` (Luo §8.1) is connected;
its character group is `X*(S_x) + ℤ r`, `2r = Σ t_i`, torsion free because `t_1, …, t_k` is a
basis of `X*(S_x)` and `k ≥ 1` (`W''_x ≠ 0` as `x` is not central). -/
theorem exists_twistIdx_kottwitzSign_neg (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (x : ↥(GSpin d.QW)) (hx : d.IsGammaElt x) (hc : ¬ IsCentralW d x) :
    ∃ β α, TwistIdx IF x β α ∧ kottwitzSign d (IF.twist α) = -1 :=
  sorry

/-- For `x` central, `S_x(F̄) = 1` (`P` of an element fixing all of `W_{F̄}` is the identity). -/
theorem torusBarFbar_eq_bot_of_central (x : ↥(GSpin d.QW)) (hx : IsCentralW d x) :
    d.torusBarFbar x = ⊥ := by
  obtain ⟨c, rfl⟩ := hx
  rw [eq_bot_iff]
  rintro s ⟨g, hg, rfl⟩
  rw [Subgroup.mem_bot]
  have hP : specP (d.QW.baseChange (AlgebraicClosure F)) g = 1 := by
    refine LinearEquiv.ext fun w => hg.2 w ?_
    rw [fixedSub_scalar, Submodule.baseChange_top]
    trivial
  apply Units.ext
  rw [coe_specMatFbar, hP]
  simp

/-- The trivial class maps to the base point: `q_x(1) = 1` (the trivial cocycle is that of the
identity isometry of the trivial twist). -/
theorem twistIdx_one_base (IF : InnerFormSystem d) (x : ↥(GSpin d.QW)) :
    TwistIdx IF x (H1.mk (GalCocycle.one _)) IF.base := by
  refine ⟨GalCocycle.one _, rfl, ?_⟩
  rw [IF.twist_base]
  refine ⟨QuadraticMap.IsometryEquiv.refl _, fun σ => ?_⟩
  have h1 : ((QuadraticMap.IsometryEquiv.refl
      (d.QW.baseChange (AlgebraicClosure F))).toLinearEquiv).toLinearMap = LinearMap.id := rfl
  have h2 : ((QuadraticMap.IsometryEquiv.refl
      (d.QW.baseChange (AlgebraicClosure F))).toLinearEquiv.symm).toLinearMap =
        LinearMap.id := rfl
  simp only [galoisConj, h1, h2, LinearMap.toMatrix_id, LinearMap.id_comp]
  rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.toLin_one, LinearMap.toMatrix_id]
  rfl

/-- **The signed count** (own work; replaces the Kottwitz-sign cancellation of Thesis §6.7,
after (6.7.6)).  Let `G` be quasi-split and
`x ∈ Γ(G,H)` with `G_x` quasi-split.  Then `Σ_α e(G_α) n_α(x) = 1` if `x` is central and `0`
otherwise.  Proof: `Σ_α e(G_α) n_α(x) = Σ_{β ∈ H¹(F,S_x)} e(G_{q_x(β)})` by
Prop. 6.6.1(iii) (`n_alpha_eq_card_twistIdx`, `existsUnique_twistIdx`, `finite_H1_torusBar`).  If
`x` is central, `S_x = 1` and the sum is `e(G) = 1`.  Otherwise `β ↦ e(G_{q_x(β)})` is multiplicative
(`kottwitzSign_twistIdx_mul`: Kottwitz 1983, BP (12.1.6)) and takes the value `-1`
(`exists_twistIdx_kottwitzSign_neg`), so translating by a class `β₀` with sign `-1` (a bijection of
the finite set `H¹(F, S_x)`) changes the sign of every term, and the sum vanishes.  (`G_x`
quasi-split is not needed.) -/
theorem signed_count (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d) (x : ↥(GSpin d.QW))
    (hx : d.IsGammaElt x) (hqd : IsQdAt d x) :
    signedCount IF x = if IsCentralW d x then 1 else 0 := by
  classical
  have _ := hqd
  have : Finite (H1 (d.torusBarFbar x)) := finite_H1_torusBar d x hx
  let : Fintype (H1 (d.torusBarFbar x)) := Fintype.ofFinite _
  have : Finite IF.Idx := IF.finite_idx
  let : Fintype IF.Idx := Fintype.ofFinite _
  let q : H1 (d.torusBarFbar x) → IF.Idx := fun β => (existsUnique_twistIdx IF x β).exists.choose
  have hq : ∀ β α, TwistIdx IF x β α ↔ q β = α := fun β α =>
    ⟨fun h => (existsUnique_twistIdx IF x β).unique
        (existsUnique_twistIdx IF x β).exists.choose_spec h,
      fun h => h ▸ (existsUnique_twistIdx IF x β).exists.choose_spec⟩
  set e : IF.Idx → ℤ := fun α => kottwitzSign d (IF.twist α) with he
  have hsum : signedCount IF x = ∑ β, e (q β) := by
    unfold signedCount
    rw [finsum_eq_sum_of_fintype, ← Fintype.sum_fiberwise q (fun β => e (q β))]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [n_alpha_eq_card_twistIdx IF α x hx,
      Nat.card_congr (Equiv.subtypeEquivRight fun β => hq β α), Nat.card_eq_fintype_card,
      Finset.sum_congr rfl fun (i : {β // q β = α}) _ => congrArg e i.2, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_comm]
  rw [hsum]
  by_cases hc : IsCentralW d x
  · rw [ite_eq_left hc]
    have hbot := torusBarFbar_eq_bot_of_central x hc
    have hall : ∀ β : H1 (d.torusBarFbar x), β = H1.mk (GalCocycle.one _) := fun β => by
      induction β using H1.ind with
      | h a => exact (H1.mk_eq_mk.2 (GalCocycle.rel_one_of_eq_bot hbot a)).symm
    rw [Fintype.sum_eq_single (H1.mk (GalCocycle.one _)) fun β hβ => absurd (hall β) hβ,
      (hq _ _).1 (twistIdx_one_base IF x), he]
    simp only
    rw [IF.twist_base, kottwitzSign_refl]
  · rw [ite_eq_right hc]
    have hcomm := torusBarFbar_commute x hx
    have hstab : ∀ σ : GalF F, ∀ s ∈ d.torusBarFbar x, galGL d.m σ s ∈ d.torusBarFbar x :=
      fun σ => galGL_mem_torusBarFbar x σ
    obtain ⟨β₀, α₀, h₀, he₀⟩ := exists_twistIdx_kottwitzSign_neg hqs IF x hx hc
    set a₀ := Quotient.out β₀
    have ha₀ : TwistIdx IF x (H1.mk a₀) α₀ := by rw [H1.mk_out]; exact h₀
    set T := H1.translate hcomm hstab a₀
    have hT : Function.Bijective T :=
      Finite.injective_iff_bijective.1 (H1.translate_injective hcomm hstab a₀)
    have hneg : ∀ β, e (q (T β)) = - e (q β) := fun β => by
      induction β using H1.ind with
      | h b =>
        have h := kottwitzSign_twistIdx_mul hqs IF x hx a₀ b (GalCocycle.mulOf hcomm hstab a₀ b)
          (fun σ => rfl) α₀ (q (H1.mk b)) (q (T (H1.mk b))) ha₀ ((hq _ _).2 rfl) ((hq _ _).2 rfl)
        simp only [he]
        rw [h, he₀, neg_one_mul]
    have hS : ∑ β, e (q β) = ∑ β, e (q (T β)) :=
      (Equiv.sum_comp (Equiv.ofBijective T hT) fun β => e (q β)).symm
    simp only [hneg, Finset.sum_neg_distrib] at hS
    linarith

end Prop1251

/-! ## 5. Transport along the base point `IF.data IF.base = d` -/

section Transport

/-- Transport `θ : G_{base}(F) → ℂ` to `G(F)` along an equality of GGP data. -/
def transportFn {d d' : GGPData F} (h : d' = d) (θ : ↥d'.G → ℂ) : ↥d.G → ℂ :=
  fun x => θ (cast (congrArg (fun e : GGPData F => (↥e.G : Type _)) h.symm) x)

theorem transportFn_isQuasiCharacter {d d' : GGPData F} (h : d' = d) (θ : ↥d'.G → ℂ)
    (hθ : IsQuasiCharacter d'.G d'.lie d'.bilin ψ θ) :
    IsQuasiCharacter d.G d.lie d.bilin ψ (transportFn h θ) := by
  subst h
  exact hθ

theorem transportFn_isStableFn {d d' : GGPData F} (h : d' = d) (θ : ↥d'.G → ℂ)
    (hθ : IsStableFn d' θ) : IsStableFn d (transportFn h θ) := by
  subst h
  exact hθ

/-- Germs at `1` with the orbit `O_1` are transported. -/
theorem germ_transportFn_one {d d' : GGPData F} (h : d' = d) (θ : ↥d'.G → ℂ) :
    germ d.G d.lie d.bilin ψ (transportFn h θ) (d.diag 1) (orbitChoice d 1) =
      germ d'.G d'.lie d'.bilin ψ θ (d'.diag 1) (orbitChoice d' 1) := by
  subst h
  rfl

theorem transportFn_apply_toBase {d : GGPData F} (IF : InnerFormSystem d)
    (θ : ↥(IF.data IF.base).G → ℂ) (x : ↥d.G) :
    transportFn IF.data_base θ x = θ (IF.toBase x) := rfl

/-- The base stable character `θ_1 = θ_φ` as a function on `G(F)` (Thesis §6.7: `c_φ = c_{φ,1}`). -/
def TemperedPacketFamily.baseChar {d : GGPData F} {IF : InnerFormSystem d}
    (P : TemperedPacketFamily d IF) : ↥d.G → ℂ :=
  transportFn IF.data_base (P.packetChar IF.base)

end Transport

/-! ## 6. Packet characters: quasi-characters, sums, germ transfer -/

section Packets

variable {d : GGPData F} {IF : InnerFormSystem d}

theorem TemperedPacketFamily.packetChar_eq_sum (P : TemperedPacketFamily d IF) (α : IF.Idx) :
    P.packetChar α = ∑ i ∈ Finset.univ, charG (IF.data α) (P.rep α i) := by
  funext y
  simp only [TemperedPacketFamily.packetChar, Finset.sum_apply]

/-- `θ_α` is a quasi-character (Harish-Chandra, `hc_character_isQuasiCharacter`). -/
theorem TemperedPacketFamily.packetChar_isQuasiCharacter (P : TemperedPacketFamily d IF)
    (α : IF.Idx) :
    IsQuasiCharacter (IF.data α).G (IF.data α).lie (IF.data α).bilin ψ (P.packetChar α) := by
  rw [P.packetChar_eq_sum]
  exact isQuasiCharacter_finset_sum (IF.data α) ψ _ _ fun i _ =>
    hc_character_isQuasiCharacter (IF.data α) ψ (P.rep α i) (P.tempered α i)

theorem TemperedPacketFamily.baseChar_isQuasiCharacter (P : TemperedPacketFamily d IF) :
    IsQuasiCharacter d.G d.lie d.bilin ψ P.baseChar :=
  transportFn_isQuasiCharacter ψ IF.data_base _ (P.packetChar_isQuasiCharacter ψ IF.base)

theorem TemperedPacketFamily.baseChar_isStableFn (P : TemperedPacketFamily d IF) :
    IsStableFn d P.baseChar :=
  transportFn_isStableFn IF.data_base _ (P.stab IF.base)

/-- **Linearity of `m_geom`** on finite sums of characters of tempered representations with
central character trivial on `A_{G,H}(F)` (Thesis Prop. 12.1.1: absolute
convergence of `m_{geom,s}` for `s > 0` and existence of the limit `s → 0⁺`).  Used in Thesis
(6.7.2).  Proved from `TraceFormula/MGeom.lean`: each
`θ_{π_i}` lies in `QC(G, η_i)` for its central character `η_i` (`charG_mem_QC`), and `m_geom` is
linear on the span of these spaces (`mGeom_finset_sum_of_mem`). -/
theorem mGeom_finset_sum (d : GGPData F) {ι : Type} (s : Finset ι)
    (π : ι → UnitaryRep ↥d.G) (hπ : ∀ i, IsTempered (π i))
    (hc : ∀ i, IsTrivialOn (π i) (d.AGH : Set ↥d.G)) :
    mGeom ψ d (∑ i ∈ s, charG d (π i)) = ∑ i ∈ s, mGeom ψ d (charG d (π i)) :=
  mGeom_finset_sum_of_mem ψ d s _ fun i _ =>
    mem_QCfin_of_mem_QC d (charG_mem_QC d (centralCharOf_spec d (π i) (hπ i) (hc i)))

/-- **Thesis (6.7.2)**: `Σ_{π ∈ Π_α} m(π) = m_geom(θ_α)`, by the
multiplicity formula for `(G_α,H_α,ξ_α)` and linearity of `m_geom`. -/
theorem packet_sum_mult (P : TemperedPacketFamily d IF) (α : IF.Idx) :
    ∑ i, ((mult ψ (IF.data α) (P.rep α i)).toNat : ℂ) = mGeom ψ (IF.data α) (P.packetChar α) := by
  rw [P.packetChar_eq_sum, mGeom_finset_sum ψ (IF.data α) _ _ (P.tempered α)
    (P.central_trivial α)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (multiplicity_formula ψ (IF.data α) (P.rep α i) (P.tempered α i)
    (P.central_trivial α i)).2

/-- **Germ transfer for packets** (Thesis §6.7 after (6.7.4)):
if `x ∈ GSpin(W)(F)`, `y ∈ GSpin(W_α)(F)` are semisimple and strongly stably conjugate, then
`c_{θ_α,O'}(y) = e(G_α) c_{θ_1,O}(x)` for all regular `O`, `O'`.  From STAB, TRANS and
BP (12.1.2) (`bp_germ_transfer`) applied to `θ = e(G_α) θ_1`, `θ' = θ_α`.  (Taking `α = base`
and `x`, `y` both in `G` gives the stability of `y ↦ c_{θ_α}(y)` on stable classes, Thesis
(6.7.3).) -/
theorem packet_germ_transfer (hqs : d.IsQuasiSplit) (P : TemperedPacketFamily d IF)
    (α : IF.Idx) (x : ↥(GSpin d.QW)) (y : ↥(GSpin (IF.data α).QW))
    (hx : IsSS F (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient))
    (hy : IsSS F ((((IF.data α).diag y : ↥(IF.data α).G) : (IF.data α).ambientˣ) :
      (IF.data α).ambient))
    (hxy : d.StronglyStablyConjW (IF.twist α) x y)
    (O) (hO : O ∈ NilReg (grpCentralizer d.G (d.diag x))
        (lieCentralizer d.lie (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient)))
    (O') (hO' : O' ∈ NilReg (grpCentralizer (IF.data α).G ((IF.data α).diag y))
        (lieCentralizer (IF.data α).lie
          ((((IF.data α).diag y : ↥(IF.data α).G) : (IF.data α).ambientˣ) :
            (IF.data α).ambient))) :
    germ (IF.data α).G (IF.data α).lie (IF.data α).bilin ψ (P.packetChar α)
        ((IF.data α).diag y) O' =
      (kottwitzSign d (IF.twist α) : ℂ) * germ d.G d.lie d.bilin ψ P.baseChar (d.diag x) O := by
  set e : ℂ := (kottwitzSign d (IF.twist α) : ℂ)
  have hθ : IsQuasiCharacter d.G d.lie d.bilin ψ (e • P.baseChar) :=
    isQuasiCharacter_smul d ψ e (P.baseChar_isQuasiCharacter ψ)
  have hstab : ∀ x ∈ regularSet d.G d.lie, ∀ x' ∈ regularSet d.G d.lie,
      d.StablyConj x x' → (e • P.baseChar) x = (e • P.baseChar) x' := by
    intro x hx x' hx' hc
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [P.baseChar_isStableFn x x' hx hx' hc]
  have htrans : ∀ x ∈ regularSet d.G d.lie,
      ∀ y ∈ regularSet (d.twist (IF.twist α)).G (d.twist (IF.twist α)).lie,
      d.StablyConjG (IF.twist α) x y → P.packetChar α y = (e • P.baseChar) x := by
    intro x hx y hy hc
    simp only [Pi.smul_apply, smul_eq_mul]
    exact P.trans α x y hx hy hc
  have h := bp_germ_transfer d hqs ψ (IF.twist α) (e • P.baseChar) (P.packetChar α) hθ
    (P.packetChar_isQuasiCharacter ψ α) hstab (fun y hy y' hy' hc => P.stab α y y' hy hy' hc) htrans x y hx hy hxy O hO O' hO'
  rw [h, germ_smul d ψ hx e ((P.baseChar_isQuasiCharacter ψ).2 _ hx) hO]

/-- The germ-transfer identity of `packet_germ_transfer`, for all strongly stably conjugate
semisimple pairs (used as an input of `stable_rearrangement`). -/
def PacketGermTransfer (P : TemperedPacketFamily d IF) : Prop :=
  ∀ (α : IF.Idx) (x : ↥(GSpin d.QW)) (y : ↥(GSpin (IF.data α).QW)),
    IsSS F (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient) →
    IsSS F ((((IF.data α).diag y : ↥(IF.data α).G) : (IF.data α).ambientˣ) :
      (IF.data α).ambient) →
    d.StronglyStablyConjW (IF.twist α) x y →
    ∀ O ∈ NilReg (grpCentralizer d.G (d.diag x))
        (lieCentralizer d.lie (((d.diag x : ↥d.G) : d.ambientˣ) : d.ambient)),
    ∀ O' ∈ NilReg (grpCentralizer (IF.data α).G ((IF.data α).diag y))
        (lieCentralizer (IF.data α).lie
          ((((IF.data α).diag y : ↥(IF.data α).G) : (IF.data α).ambientˣ) :
            (IF.data α).ambient)),
      germ (IF.data α).G (IF.data α).lie (IF.data α).bilin ψ (P.packetChar α)
          ((IF.data α).diag y) O' =
        (kottwitzSign d (IF.twist α) : ℂ) * germ d.G d.lie d.bilin ψ P.baseChar (d.diag x) O

theorem packetGermTransfer_holds (hqs : d.IsQuasiSplit) (P : TemperedPacketFamily d IF) :
    PacketGermTransfer ψ P :=
  fun α x y hx hy hxy O hO O' hO' => packet_germ_transfer ψ hqs P α x y hx hy hxy O hO O' hO'

end Packets

/-! ## 7. Vanishing off quasi-split classes (BP Prop. 4.5.1(i)) -/

/-- **Only quasi-split classes contribute** (Thesis (6.7.4), BP Prop. 4.5.1(i)):
the integrand `D^G(t)^{1/2} c_{θ,O_t}(t) Δ(t)^{s-1/2}` of `m_geom` vanishes at `t ∈ Γ(G,H)` with
`G_t` not quasi-split, for every `θ`.  Proof: by `nilReg_centralizer_nonempty_imp`,
`Nil_reg(𝔤_t) = ∅`, so the germ is `0` by the convention `germ_of_not_mem`. -/
theorem gammaIntegrand_eq_zero_of_not_qd (d : GGPData F) (θ : ↥d.G → ℂ)
    (T : Subgroup ↥(GSpin d.QW)) (s : ℝ) (t : ↥(GSpin d.QW)) (ht : ¬ IsQdAt d t) :
    gammaIntegrand ψ d θ T s t = 0 := by
  unfold gammaIntegrand
  split_ifs with h
  · have hempty : ¬ (NilReg (grpCentralizer d.G ((d.diag t : d.G) : d.ambientˣ))
        (lieCentralizer d.lie (((d.diag t : d.G) : d.ambientˣ) : d.ambient))).Nonempty :=
      fun hne => ht (nilReg_centralizer_nonempty_imp d t h.1.1 hne)
    have hO : orbitChoice d t ∉ NilReg (grpCentralizer d.G ((d.diag t : d.G) : d.ambientˣ))
        (lieCentralizer d.lie (((d.diag t : d.G) : d.ambientˣ) : d.ambient)) :=
      fun hm => hempty ⟨_, hm⟩
    rw [germ_of_not_mem hO, mul_zero, zero_mul]
  · rfl

/-! ## 8. The stable rearrangement (Thesis (6.7.2)–(6.7.5)) -/

section Stable

variable {d : GGPData F}

/-- The weight `Σ_α e(G_α) n_α(t) / n_1(t)` of Thesis (6.7.5), written on
`Γ(G,H)` rather than on `Γ_stab(G,H)`: an integral over `Γ_stab` of a stable function `f` is the
integral over `Γ` of `f / |p_stab^{-1}|`, and `n_1(t) = |p_stab^{-1}(t)|`. -/
def stableWeight (IF : InnerFormSystem d) (t : ↥(GSpin d.QW)) : ℂ :=
  (signedCount IF t : ℂ) / (n_alpha IF IF.base t : ℂ)

/-- The right-hand side of Thesis (6.7.5) at `s > 0`:
`∫_{Γ(G,H)} (Σ_α e(G_α) n_α(x) / n_1(x)) c_{θ,O_x}(x) D^G(x)^{1/2} Δ(x)^{s-1/2} dx`,
in the normalization of `mGeomS` (Triple). -/
def mGeomStabS (IF : InnerFormSystem d) (θ : ↥d.G → ℂ) (s : ℝ) : ℂ :=
  ∑' c : GammaClass d, ((weylCard d c : ℂ))⁻¹ *
    (letI : MeasurableSpace (d.TorusQuot (Quot.out c).1) := borel _
     haveI : BorelSpace (d.TorusQuot (Quot.out c).1) := ⟨rfl⟩
     ∫ q, stableWeight IF ((Quotient.out q : ↥(Quot.out c).1) : ↥(GSpin d.QW)) *
        gammaIntegrand ψ d θ (Quot.out c).1 s ((Quotient.out q : ↥(Quot.out c).1) : ↥(GSpin d.QW))
       ∂(probHaar (d.TorusQuot (Quot.out c).1)))

/-- Off the centre the stable integrand `(Σ_α e(G_α)n_α(t)/n_1(t)) · D^G(t)^{1/2} c_θ(t) Δ(t)^{s-1/2}` vanishes, given the signed count: on quasi-split classes the weight is `0`; on the others the integrand is `0` (`gammaIntegrand_eq_zero_of_not_qd`). -/
theorem stableTerm_eq_zero_of_not_central (IF : InnerFormSystem d)
    (hsc : ∀ t : ↥(GSpin d.QW), d.IsGammaElt t → IsQdAt d t →
      signedCount IF t = if IsCentralW d t then 1 else 0)
    (θ : ↥d.G → ℂ) (T : Subgroup ↥(GSpin d.QW)) (s : ℝ) (t : ↥(GSpin d.QW))
    (ht : ¬ IsCentralW d t) :
    stableWeight IF t * gammaIntegrand ψ d θ T s t = 0 := by
  by_cases hg : d.IsGammaElt t ∧ d.torusOf t = T
  · by_cases hq : IsQdAt d t
    · rw [stableWeight, hsc t hg.1 hq, ite_eq_right ht]
      simp
    · rw [gammaIntegrand_eq_zero_of_not_qd ψ d θ T s t hq, mul_zero]
  · rw [gammaIntegrand, ite_eq_right hg, mul_zero]

/-- On a torus `T ≠ T_1` the stable integrand vanishes identically. -/
theorem stableTerm_eq_zero_of_ne (IF : InnerFormSystem d)
    (hsc : ∀ t : ↥(GSpin d.QW), d.IsGammaElt t → IsQdAt d t →
      signedCount IF t = if IsCentralW d t then 1 else 0)
    (θ : ↥d.G → ℂ) (T : Subgroup ↥(GSpin d.QW)) (hT : T ≠ d.torusOf 1) (s : ℝ)
    (t : ↥(GSpin d.QW)) :
    stableWeight IF t * gammaIntegrand ψ d θ T s t = 0 := by
  by_cases ht : IsCentralW d t
  · have hg : ¬ (d.IsGammaElt t ∧ d.torusOf t = T) := fun h =>
      hT (h.2.symm.trans (torusOf_eq_one_of_central t ht))
    rw [gammaIntegrand, ite_eq_right hg, mul_zero]
  · exact stableTerm_eq_zero_of_not_central ψ IF hsc θ T s t ht

/-- The sum over `Γ(G,H)` in `mGeomStabS` reduces to the atom class. -/
theorem mGeomStabS_eq_atom (IF : InnerFormSystem d)
    (hsc : ∀ t : ↥(GSpin d.QW), d.IsGammaElt t → IsQdAt d t →
      signedCount IF t = if IsCentralW d t then 1 else 0)
    (θ : ↥d.G → ℂ) (s : ℝ) :
    mGeomStabS ψ IF θ s = ((weylCard d (atomClass d) : ℂ))⁻¹ *
    (letI : MeasurableSpace (d.TorusQuot (Quot.out (atomClass d)).1) := borel _
     haveI : BorelSpace (d.TorusQuot (Quot.out (atomClass d)).1) := ⟨rfl⟩
     ∫ q, stableWeight IF ((Quotient.out q : ↥(Quot.out (atomClass d)).1) : ↥(GSpin d.QW)) *
        gammaIntegrand ψ d θ (Quot.out (atomClass d)).1 s
          ((Quotient.out q : ↥(Quot.out (atomClass d)).1) : ↥(GSpin d.QW))
       ∂(probHaar (d.TorusQuot (Quot.out (atomClass d)).1))) := by
  unfold mGeomStabS
  refine tsum_eq_single (atomClass d) fun c hc => ?_
  have hT : (Quot.out c).1 ≠ d.torusOf 1 := fun h => hc (atomClass_unique c h)
  simp only [stableTerm_eq_zero_of_ne ψ IF hsc θ _ hT, integral_zero, mul_zero]

section CentralTranslate

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- Left translates of test functions are test functions. -/
theorem comp_mul_left_mem_testFunctions [IsTopologicalGroup G] {f : G → ℂ}
    (hf : f ∈ testFunctions G) (z : G) : (fun g => f (z * g)) ∈ testFunctions G :=
  ⟨hf.1.comp_continuous (continuous_const.mul continuous_id),
    hf.2.comp_homeomorph (Homeomorph.mulLeft z)⟩

omit [T2Space G] in
/-- Left translation of a test function by an element `z` with `π(z) = 1` does not change
`π(f)`. -/
theorem opOf_comp_mul_left_of_central (π : UnitaryRep G) {f : G → ℂ} (hf : f ∈ testFunctions G)
    {z : G} (hπz : π.ρ z = 1) :
    opOf π (fun g => f (z⁻¹ * g)) = opOf π f := by
  have hf' := comp_mul_left_mem_testFunctions hf z⁻¹
  ext v
  rw [opOf_apply π (opIntegrable_of_mem_testFunctions π hf'),
    opOf_apply π (opIntegrable_of_mem_testFunctions π hf),
    ← integral_mul_left_eq_self (fun g => f (z⁻¹ * g) • π.ρ g v) z]
  congr 1
  funext g
  simp only [inv_mul_cancel_left, map_mul, hπz, one_mul]

omit [T2Space G] in
theorem traceDatum_comp_mul_left_of_central (π : UnitaryRep G) {f : G → ℂ}
    (hf : f ∈ testFunctions G) {z : G} (hz : ∀ g, z * g = g * z) (hπz : π.ρ z = 1)
    {K : Subgroup G} (hK : TraceDatum π f K) : TraceDatum π (fun g => f (z⁻¹ * g)) K := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hK
  refine ⟨h1, h2, fun k hk g => ⟨?_, ?_⟩, h4, ?_⟩
  · have hz' : z⁻¹ * k = k * z⁻¹ := by
      have := hz k⁻¹
      have h := congrArg (fun u => u⁻¹) this
      simpa [mul_inv_rev] using h.symm
    simp only
    rw [← mul_assoc, hz', mul_assoc]
    exact (h3 k hk _).1
  · simp only
    rw [← mul_assoc]
    exact (h3 k hk _).2
  · intro v hv
    rw [opOf_comp_mul_left_of_central π hf hπz]
    exact h5 v hv

omit [T2Space G] in
/-- `tr π(f(z⁻¹ ·)) = tr π(f)` for `z` central with `π(z) = 1`. -/
theorem traceOf_comp_mul_left_of_central (π : UnitaryRep G) {f : G → ℂ}
    (hf : f ∈ testFunctions G) {z : G} (hz : ∀ g, z * g = g * z) (hπz : π.ρ z = 1) :
    traceOf π (fun g => f (z⁻¹ * g)) = traceOf π f := by
  have hf' := comp_mul_left_mem_testFunctions hf z⁻¹
  have hzi : ∀ g, z⁻¹ * g = g * z⁻¹ := fun g => by
    have h := congrArg (fun u => u⁻¹) (hz g⁻¹)
    simpa [mul_inv_rev] using h.symm
  have hπzi : π.ρ z⁻¹ = 1 := by
    have h := map_mul π.ρ z⁻¹ z
    rw [inv_mul_cancel, map_one, hπz, mul_one] at h
    exact h.symm
  by_cases h : ∃ K, TraceDatum π f K
  · obtain ⟨K, hK⟩ := h
    have hK' := traceDatum_comp_mul_left_of_central π hf hz hπz hK
    rw [traceOf_eq π _ K hK', traceOf_eq π f K hK]
    have key : ∀ (T T' : π.H →L[ℂ] π.H), T = T' → ∀ (h₁ : ∀ v ∈ fixedSpace π K, T v ∈ fixedSpace π K)
        (h₂ : ∀ v ∈ fixedSpace π K, T' v ∈ fixedSpace π K),
        LinearMap.trace ℂ ↥(fixedSpace π K) (T.toLinearMap.restrict h₁) =
          LinearMap.trace ℂ ↥(fixedSpace π K) (T'.toLinearMap.restrict h₂) := by
      rintro T T' rfl h₁ h₂; rfl
    exact key _ _ (opOf_comp_mul_left_of_central π hf hπz) _ _
  · have h' : ¬ ∃ K, TraceDatum π (fun g => f (z⁻¹ * g)) K := by
      rintro ⟨K, hK⟩
      apply h
      refine ⟨K, ?_⟩
      have := traceDatum_comp_mul_left_of_central π hf' hzi hπzi hK
      simpa using this
    unfold traceOf
    rw [dite_eq_right_iff.mpr fun h'' => absurd h'' h, dite_eq_right_iff.mpr fun h'' => absurd h'' h']

omit [T2Space G] in
/-- **Characters are invariant under central elements acting trivially**: if `θ` is a character
of `π`, `z` is central and `π(z) = 1`, then `g ↦ θ(z g)` is also a character of `π`
(Thesis Ch. 1: `tr π(f(z⁻¹·)) = tr(π(z)π(f)) = tr π(f)`). -/
theorem IsCharacterOf.comp_mul_left_of_central {π : UnitaryRep G} {θ : G → ℂ}
    (hθ : IsCharacterOf π θ) {z : G} (hz : ∀ g, z * g = g * z) (hπz : π.ρ z = 1) :
    IsCharacterOf π (fun g => θ (z * g)) := by
  refine ⟨?_, fun f hf => ?_⟩
  · have := (locallyIntegrable_map_homeomorph (Homeomorph.mulLeft z) (f := θ)
      (μ := (Measure.haar : Measure G))).1
    rw [show Measure.map (Homeomorph.mulLeft z) (Measure.haar : Measure G) = Measure.haar from
      map_mul_left_eq_self _ z] at this
    exact this hθ.1
  · rw [← traceOf_comp_mul_left_of_central π hf hz hπz,
      ← hθ.2 _ (comp_mul_left_mem_testFunctions hf z⁻¹),
      ← integral_mul_left_eq_self (fun g => θ g * f (z⁻¹ * g)) z]
    simp only [inv_mul_cancel_left]

end CentralTranslate


/-- `x ↦ c x` preserves regular semisimplicity for a nonzero scalar `c`. -/
theorem isRegularSS_algebraMap_mul {A : Type*} [Ring A] [Algebra F A] (𝔤 : LieSubalgebra F A)
    {a : F} (ha : a ≠ 0) {y : A} (hy : IsRegularSS 𝔤 y) :
    IsRegularSS 𝔤 (algebraMap F A a * y) := by
  rw [← Algebra.smul_def]
  have hL : LinearMap.mulLeft F (a • y) = a • LinearMap.mulLeft F y := by
    ext w; simp
  have hC : lieCentralizer 𝔤 (a • y) = lieCentralizer 𝔤 y := by
    ext X
    rw [mem_lieCentralizer, mem_lieCentralizer, smul_mul_assoc, mul_smul_comm]
    exact and_congr_right fun _ => smul_right_inj ha
  refine ⟨?_, hC ▸ hy.2⟩
  unfold IsSS
  rw [hL]
  exact Module.End.IsSemisimple_smul a hy.1

/-- A scalar is semisimple. -/
theorem isSS_algebraMap {A : Type*} [Ring A] [Algebra F A] (a : F) :
    IsSS F (algebraMap F A a) := by
  have hL : LinearMap.mulLeft F (algebraMap F A a) = a • LinearMap.id := by
    ext w; simp [Algebra.smul_def]
  unfold IsSS
  rw [hL]
  exact Module.End.IsSemisimple_smul a Module.End.isSemisimple_id

/-- The central scalar `c ∈ GSpin(W)` embeds diagonally as the scalar `c` of `C(W) × C(V)`. -/
theorem coe_diag_scalarGSpin (c : Fˣ) :
    (((d.diag (scalarGSpin d.QW c) : d.G) : d.ambientˣ) : d.ambient) =
      algebraMap F d.ambient (c : F) := by
  refine Prod.ext ?_ ?_
  · rfl
  · show CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)
        (algebraMap F (CliffordAlgebra d.QW) (c : F)) = _
    exact AlgHom.commutes _ _

/-- `G_x = G` for `x` central in the ambient algebra. -/
theorem grpCentralizer_eq_of_central {A : Type*} [Ring A] (G : Subgroup Aˣ) {x : Aˣ}
    (hx : ∀ a : A, (x : A) * a = a * x) : grpCentralizer G x = G := by
  ext g
  simp only [grpCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq, and_iff_left_iff_imp]
  exact fun _ => Units.ext (hx g)

/-- `𝔤_x = 𝔤` for `x` central in the ambient algebra. -/
theorem lieCentralizer_eq_of_central {A : Type*} [Ring A] [Algebra F A] (𝔤 : LieSubalgebra F A)
    {x : A} (hx : ∀ a : A, x * a = a * x) : lieCentralizer 𝔤 x = 𝔤 := by
  ext X
  rw [mem_lieCentralizer]
  exact and_iff_left (hx X)

/-- **Characters are invariant under `A_{G,H}(F)` on `G_reg(F)`**: for `π` tempered with
central character trivial on `A_{G,H}(F)` and `c ∈ F^×`, `θ_π(c y) = θ_π(y)` for regular `y`.
`g ↦ θ_π(cg)` is again a character of `π` (`IsCharacterOf.comp_mul_left_of_central`) and is
continuous on `G_reg(F)`, which is stable under `c`; two such characters agree on `G_reg(F)`
(`hc_regularSet_open_conull`). -/
theorem charG_diag_scalar_mul (π : UnitaryRep ↥d.G) (hπ : IsTempered π)
    (hc : IsTrivialOn π (d.AGH : Set ↥d.G)) (c : Fˣ) {y : ↥d.G}
    (hy : y ∈ regularSet d.G d.lie) :
    charG d π (d.diag (scalarGSpin d.QW c) * y) = charG d π y := by
  set z := d.diag (scalarGSpin d.QW c)
  have hz : (((z : d.G) : d.ambientˣ) : d.ambient) = algebraMap F d.ambient (c : F) :=
    coe_diag_scalarGSpin c
  have hzc : ∀ g : ↥d.G, z * g = g * z := fun g => by
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul, hz]
    exact Algebra.commutes _ _
  have hπz : π.ρ z = 1 := hc z ⟨c, rfl⟩
  obtain ⟨hchar, hcont⟩ := hc_character d π hπ
  have hchar' := hchar.comp_mul_left_of_central hzc hπz
  have hreg : ∀ g ∈ regularSet d.G d.lie, z * g ∈ regularSet d.G d.lie := fun g hg => by
    show IsRegularSS d.lie (((z * g : d.G) : d.ambientˣ) : d.ambient)
    simp only [Subgroup.coe_mul, Units.val_mul, hz]
    exact isRegularSS_algebraMap_mul d.lie c.ne_zero hg
  have hcont' : ContinuousOn (fun g => charG d π (z * g)) (regularSet d.G d.lie) :=
    hcont.comp (continuous_const.mul continuous_id).continuousOn hreg
  have : TotallyDisconnectedSpace ↥d.G := totallyDisconnectedSpace_subgroup F d.ambient d.G
  have hae := hchar'.ae_eq hchar
  exact Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae) (hc_regularSet_open_conull d).1
    hcont' hcont hy

theorem transportFn_diag_scalar_mul {d d' : GGPData F} (h : d' = d) (θ : ↥d'.G → ℂ)
    (hθ : ∀ (c : Fˣ), ∀ y ∈ regularSet d'.G d'.lie,
      θ (d'.diag (scalarGSpin d'.QW c) * y) = θ y) :
    ∀ (c : Fˣ), ∀ y ∈ regularSet d.G d.lie,
      transportFn h θ (d.diag (scalarGSpin d.QW c) * y) = transportFn h θ y := by
  subst h
  exact hθ

/-- `θ_1(c y) = θ_1(y)` on `G_reg(F)` for `c ∈ A_{G,H}(F)` (central characters trivial on
`A_{G,H}(F)`, Thesis §6.3). -/
theorem TemperedPacketFamily.baseChar_diag_scalar_mul {IF : InnerFormSystem d}
    (P : TemperedPacketFamily d IF) (c : Fˣ) {y : ↥d.G} (hy : y ∈ regularSet d.G d.lie) :
    P.baseChar (d.diag (scalarGSpin d.QW c) * y) = P.baseChar y :=
  transportFn_diag_scalar_mul IF.data_base _ (fun c _ hy => Finset.sum_congr rfl fun i _ =>
    charG_diag_scalar_mul _ (P.tempered _ i) (P.central_trivial _ i) c hy) c y hy

/-- Transport of germ coefficients along equalities of centralizers. -/
theorem exists_coeff_transport (b : LinearMap.BilinForm F d.ambient)
    (H H' : Subgroup d.ambientˣ) (𝔥 𝔥' : LieSubalgebra F d.ambient) (hH : H = H') (h𝔥 : 𝔥 = 𝔥')
    (c' : NilOrbit H' 𝔥' → ℂ) :
    ∃ c : NilOrbit H 𝔥 → ℂ, ((Function.support c).Finite ↔ (Function.support c').Finite) ∧
      (∀ X, ∑ᶠ O, c O * jHat H 𝔥 b ψ O X = ∑ᶠ O, c' O * jHat H' 𝔥' b ψ O X) ∧
      ∀ O O', HEq O O' → c O = c' O' ∧ (O ∈ NilReg H 𝔥 ↔ O' ∈ NilReg H' 𝔥') := by
  subst hH h𝔥
  refine ⟨c', Iff.rfl, fun _ => rfl, fun O O' hO => ?_⟩
  obtain rfl := eq_of_heq hO
  exact ⟨rfl, Iff.rfl⟩

/-- **Germs only see the local behaviour**: if `x, x'` are semisimple with the same centralizers
and `θ(x e^X) = θ(x' e^X)` for `X ∈ 𝔤_x` small and regular, then the germs of `θ` at `x` and `x'`
agree (via uniqueness of the local expansion, `germ_unique`). -/
theorem germ_eq_germ_of_translate (θ : ↥d.G → ℂ) (x x' : ↥d.G)
    (hx : IsSS F ((x : d.ambientˣ) : d.ambient)) (hx' : IsSS F ((x' : d.ambientˣ) : d.ambient))
    (hH : grpCentralizer d.G x = grpCentralizer d.G x')
    (h𝔥 : lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient) =
      lieCentralizer d.lie ((x' : d.ambientˣ) : d.ambient))
    (hθ : ∃ ω ∈ 𝓝 (0 : d.ambient), ∀ X ∈ ω, X ∈ lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient) →
      IsRegularSS (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) X →
      ∀ y : ↥d.G, ((y : d.ambientˣ) : d.ambient) = ((x : d.ambientˣ) : d.ambient) * expA F X →
        ∃ y' : ↥d.G, ((y' : d.ambientˣ) : d.ambient) = ((x' : d.ambientˣ) : d.ambient) * expA F X ∧
          θ y = θ y')
    (hexp : ∃ c, HasGermExpansion d.G d.lie d.bilin ψ θ x' c)
    (O : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)))
    (O' : NilOrbit (grpCentralizer d.G x') (lieCentralizer d.lie ((x' : d.ambientˣ) : d.ambient)))
    (hO : HEq O O') :
    germ d.G d.lie d.bilin ψ θ x O = germ d.G d.lie d.bilin ψ θ x' O' := by
  obtain ⟨c', hc'⟩ := hexp
  obtain ⟨c, hfin, hsum, hcO⟩ := exists_coeff_transport ψ d.bilin _ _ _ _ hH h𝔥 c'
  obtain ⟨ω₁, hω₁, hθ'⟩ := hθ
  obtain ⟨ω₂, hω₂, hc'e⟩ := hc'.2
  have hc : HasGermExpansion d.G d.lie d.bilin ψ θ x c := by
    refine ⟨hfin.mpr hc'.1, ω₁ ∩ ω₂, inter_mem hω₁ hω₂, fun X hX hXc hXr y hy => ?_⟩
    obtain ⟨y', hy', hθy⟩ := hθ' X hX.1 hXc hXr y hy
    rw [hθy, hsum X]
    exact hc'e X hX.2 (h𝔥 ▸ hXc) (h𝔥 ▸ hXr) y' hy'
  obtain ⟨hcc, hreg⟩ := hcO O O' hO
  by_cases hOr : O ∈ NilReg _ _
  · rw [germ_eq_of_hasGermExpansion d ψ hx hc hOr,
      germ_eq_of_hasGermExpansion d ψ hx' hc' (hreg.mp hOr), hcc]
  · rw [germ_of_not_mem hOr, germ_of_not_mem fun h => hOr (hreg.mpr h)]

/-- The selection rule behind `orbitChoice`, with the centralizers and the condition as
parameters. -/
def pickNilOrbit (H : Subgroup d.ambientˣ) (𝔥 : LieSubalgebra F d.ambient)
    (P : d.ambient → Prop) : NilOrbit H 𝔥 :=
  if h : ∃ O ∈ NilReg H 𝔥, ∃ X ∈ nilOrbitSet O, P (X : d.ambient) then h.choose
  else Quotient.mk (nilSetoid _ _) ⟨0, LieSubalgebra.zero_mem _, IsNilpotent.zero⟩

theorem orbitChoice_eq_pickNilOrbit (x : ↥(GSpin d.QW)) :
    orbitChoice d x = pickNilOrbit _ _ (OrbitSpec d x) := rfl

theorem heq_pickNilOrbit (H H' : Subgroup d.ambientˣ) (𝔥 𝔥' : LieSubalgebra F d.ambient)
    (hH : H = H') (h𝔥 : 𝔥 = 𝔥') (P P' : d.ambient → Prop) (hP : P = P') :
    HEq (pickNilOrbit H 𝔥 P) (pickNilOrbit H' 𝔥' P') := by
  subst hH h𝔥 hP
  rfl

/-- **Central translation of the germ** (own work; Thesis §6.7: `c_{θ_1}(c) = c_{θ_1}(1)`
for `c ∈ A_{G,H}(F)`, the central character being trivial on `Z_{G,H}(F)`).  Proof: (a) `θ_1(cy) = θ_1(y)`
on `G_reg(F)` (`TemperedPacketFamily.baseChar_diag_scalar_mul`: the translate represents the same
character distribution since `π(c) = 1`, and both are continuous on the open conull set `G_reg(F)`,
which is stable under `c`); (b) for `X` small and regular, `e^X` is regular
(`exists_nhds_isRegularSS_expA`, Harish-Chandra's regularity near `1`, proved), so
`θ_1(c e^X) = θ_1(e^X)` and the expansion at `1` is one at `c` (`germ_eq_germ_of_translate`, with
`germ_unique`); (c) `orbitChoice d c` corresponds to `orbitChoice d 1`: both centralizers are `G`
and `𝔤`, and `OrbitSpec d c = OrbitSpec d 1` as `W'_c = W'_1 = W`. -/
theorem germ_baseChar_central {IF : InnerFormSystem d} (P : TemperedPacketFamily d IF)
    (t : ↥(GSpin d.QW)) (ht : IsCentralW d t) :
    germ d.G d.lie d.bilin ψ P.baseChar (d.diag t) (orbitChoice d t) =
      germ d.G d.lie d.bilin ψ P.baseChar (d.diag 1) (orbitChoice d 1) := by
  obtain ⟨c, rfl⟩ := ht
  set z := d.diag (scalarGSpin d.QW c) with hzdef
  have hz : (((z : d.G) : d.ambientˣ) : d.ambient) = algebraMap F d.ambient (c : F) :=
    coe_diag_scalarGSpin c
  have h1 : (((d.diag 1 : d.G) : d.ambientˣ) : d.ambient) = 1 := by rw [map_one]; rfl
  have hzc : ∀ a : d.ambient, (((z : d.G) : d.ambientˣ) : d.ambient) * a =
      a * (((z : d.G) : d.ambientˣ) : d.ambient) := fun a => by
    rw [hz]; exact Algebra.commutes _ _
  have h1c : ∀ a : d.ambient, (((d.diag 1 : d.G) : d.ambientˣ) : d.ambient) * a =
      a * (((d.diag 1 : d.G) : d.ambientˣ) : d.ambient) := fun a => by
    rw [h1, one_mul, mul_one]
  have hH : grpCentralizer d.G (z : d.ambientˣ) = grpCentralizer d.G (d.diag 1 : d.ambientˣ) := by
    rw [grpCentralizer_eq_of_central _ hzc, grpCentralizer_eq_of_central _ h1c]
  have hLz : lieCentralizer d.lie (((z : d.G) : d.ambientˣ) : d.ambient) = d.lie :=
    lieCentralizer_eq_of_central _ hzc
  have h𝔥 : lieCentralizer d.lie (((z : d.G) : d.ambientˣ) : d.ambient) =
      lieCentralizer d.lie (((d.diag 1 : d.G) : d.ambientˣ) : d.ambient) := by
    rw [hLz, lieCentralizer_eq_of_central _ h1c]
  have hssz : IsSS F (((z : d.G) : d.ambientˣ) : d.ambient) := by
    rw [hz]; exact isSS_algebraMap _
  have hss1 : IsSS F (((d.diag 1 : d.G) : d.ambientˣ) : d.ambient) := by
    rw [h1, ← map_one (algebraMap F d.ambient)]; exact isSS_algebraMap _
  have hP : OrbitSpec d (scalarGSpin d.QW c) = OrbitSpec d 1 := by
    funext X
    unfold OrbitSpec
    rw [fixedSub_scalar, fixedSub_one_eq_top]
  refine germ_eq_germ_of_translate ψ P.baseChar _ _ hssz hss1 hH h𝔥 ?_
    ((P.baseChar_isQuasiCharacter ψ).2 _ hss1) _ _ ?_
  · obtain ⟨ω, hω, hreg⟩ := exists_nhds_isRegularSS_expA F d.lie
    refine ⟨ω, hω, fun X hX _ hXr y hy => ⟨z⁻¹ * y, ?_, ?_⟩⟩
    · have : (((z⁻¹ * y : d.G) : d.ambientˣ) : d.ambient) = expA F X := by
        rw [Subgroup.coe_mul, Units.val_mul, hy, ← mul_assoc, InvMemClass.coe_inv,
          Units.inv_mul, one_mul]
      rw [this, h1, one_mul]
    · have hy' : z⁻¹ * y ∈ regularSet d.G d.lie := by
        show IsRegularSS d.lie (((z⁻¹ * y : d.G) : d.ambientˣ) : d.ambient)
        rw [Subgroup.coe_mul, Units.val_mul, hy, ← mul_assoc, InvMemClass.coe_inv,
          Units.inv_mul, one_mul]
        exact hreg X hX (hLz ▸ hXr)
      have := P.baseChar_diag_scalar_mul c hy'
      rw [← hzdef, mul_inv_cancel_left] at this
      exact this
  · rw [orbitChoice_eq_pickNilOrbit, orbitChoice_eq_pickNilOrbit]
    exact heq_pickNilOrbit _ _ _ _ hH h𝔥 _ _ hP

/-- **The atom** (Thesis §6.7 after (6.7.6)): `|W(T_1)| = 1`, `T_1(F)/A(F)` is a point, the weight is `signedCount/n_1 = 1/1`, `D^G = Δ = 1`, and the germ at the central representative equals the germ at `1`.  Stated for any `T = T_1` so that it applies to the chosen representative of the atom class. -/
theorem atom_value (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (P : TemperedPacketFamily d IF)
    (hsc : ∀ t : ↥(GSpin d.QW), d.IsGammaElt t → IsQdAt d t →
      signedCount IF t = if IsCentralW d t then 1 else 0)
    (s : ℝ) (T : Subgroup ↥(GSpin d.QW)) (hT : T = d.torusOf 1) :
    ((weylCardOf d T : ℂ))⁻¹ *
    (letI : MeasurableSpace (d.TorusQuot T) := borel _
     haveI : BorelSpace (d.TorusQuot T) := ⟨rfl⟩
     ∫ q, stableWeight IF ((Quotient.out q : ↥T) : ↥(GSpin d.QW)) *
        gammaIntegrand ψ d P.baseChar T s ((Quotient.out q : ↥T) : ↥(GSpin d.QW))
       ∂(probHaar (d.TorusQuot T))) =
      germ d.G d.lie d.bilin ψ P.baseChar (d.diag 1) (orbitChoice d 1) := by
  subst hT
  rw [weylCardOf_torusOf_one, integral_probHaar_torusQuot_one]
  set t : ↥(GSpin d.QW) := ((Quotient.out (1 : d.TorusQuot (d.torusOf 1)) : ↥(d.torusOf 1)) :
    ↥(GSpin d.QW))
  have ht : IsCentralW d t := by
    have h := (mem_torusOf_one_iff t).1 (Quotient.out (1 : d.TorusQuot (d.torusOf 1))).2
    rw [IsCentralW, ← ker_specP d.nondeg]
    exact h
  have hfix : fixedSub t = ⊤ := by
    obtain ⟨c, hc⟩ := ht
    rw [← hc]; exact fixedSub_scalar c
  rw [gammaIntegrand_central ψ _ s t ht, germ_baseChar_central ψ P t ht, stableWeight,
    hsc t (isGammaElt_of_central t ht) (isQdAt_of_fixedSub_eq_top d hqs t hfix),
    ite_eq_left ht, n_alpha_base_of_central IF t ht]
  simp

/-- `θ_α = Σ_{π ∈ Π_α} θ_π` lies in `QCfin` (each `θ_π` lies in `QC(G_α, η_π)`, `charG_mem_QC`). -/
theorem TemperedPacketFamily.packetChar_mem_QCfin {IF : InnerFormSystem d}
    (P : TemperedPacketFamily d IF) (α : IF.Idx) :
    P.packetChar α ∈ QCfin (IF.data α) := by
  rw [P.packetChar_eq_sum]
  exact Submodule.sum_mem _ fun i _ => mem_QCfin_of_mem_QC _ (charG_mem_QC _
    (centralCharOf_spec _ (P.rep α i) (P.tempered α i) (P.central_trivial α i)))

/-- **The stable rearrangement at `s > 0`** (own work; Thesis (6.7.2)–(6.7.5) before the limit):
for `s > 0`,
`Σ_α m_{geom,s}(θ_α) = ∫_{Γ(G,H)} (Σ_α e(G_α)n_α(x)/n_1(x)) c_{θ_1}(x) D^G(x)^{1/2} Δ(x)^{s-1/2} dx`.
Route, all at fixed `s > 0`, where the integrals converge absolutely (Thesis Prop.
12.1.1):
* in `m_{geom,s}(θ_α)` only quasi-split classes contribute (`hvanish`);
* `c_{θ_α}`, `D^{G_α}`, `Δ` are constant on strongly stable classes (`hgerm` at `α`, `α`), so the
  integral over `Γ(G_α,H_α)` is one over `Γ^qd_stab(G_α,H_α)` weighted by the fibre counts;
* `y ↦ x` with `x ∼_stab y` (`hi`) is a measure-preserving injection
  `Γ^qd_stab(G_α,H_α) ↪ Γ^qd_stab(G,H)`: near a class with distinct eigenvalues on `W''` (full
  measure) the weight `|W(T)|⁻¹` cancels the `|W(T)|`-to-1 projection, and `TorusTransfer` (`hii`)
  identifies the probability Haar measures of `T_x(F)/A(F)`, `T_y(F)/A(F)`, `D^G` and `Δ`;
* `c_{θ_α}(y) = e(G_α) c_{θ_1}(x)` (`hgerm`), and the fibres have `n_α(x)` points;
* finally `∫_{Γ_stab(G,H)} f = ∫_{Γ(G,H)} f / n_1` (fibres of `Γ → Γ_stab` have `n_1` points). -/
theorem stable_rearrangement_pos (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (P : TemperedPacketFamily d IF)
    (hgerm : PacketGermTransfer ψ P)
    (hvanish : ∀ (α : IF.Idx) (θ : ↥(IF.data α).G → ℂ) (T : Subgroup ↥(GSpin (IF.data α).QW))
      (s : ℝ) (t : ↥(GSpin (IF.data α).QW)), ¬ IsQdAt (IF.data α) t →
        gammaIntegrand ψ (IF.data α) θ T s t = 0)
    (hi : ∀ (α : IF.Idx) (y : ↥(GSpin (IF.data α).QW)), (IF.data α).IsGammaElt y →
      IsQdAt (IF.data α) y → ∃ x : ↥(GSpin d.QW), d.IsGammaElt x ∧
        d.StronglyStablyConjW (IF.twist α) x y)
    (hii : ∀ (α : IF.Idx) (x : ↥(GSpin d.QW)) (y : ↥(GSpin (IF.data α).QW)), d.IsGammaElt x →
      (IF.data α).IsGammaElt y → d.StronglyStablyConjW (IF.twist α) x y →
        TorusTransfer IF α x y)
    {s : ℝ} (hs : 0 < s) :
    ∑ᶠ α : IF.Idx, mGeomS ψ (IF.data α) (P.packetChar α) s = mGeomStabS ψ IF P.baseChar s :=
  sorry

/-- **Thesis (6.7.5)** (own work): summing (6.7.2) over the inner forms and
rearranging over strongly stable classes,
`Σ_α m_geom(θ_α) = lim_{s→0⁺} ∫_{Γ(G,H)} (Σ_α e(G_α)n_α(x)/n_1(x)) c_{θ_1}(x) D^G(x)^{1/2}
Δ(x)^{s-1/2} dx`.  Ingredients: STAB + BP (12.1.2) (`packet_germ_transfer`) make `c_{θ_α}`
constant on strongly stable classes; only quasi-split classes contribute
(`gammaIntegrand_eq_zero_of_not_qd`); Prop. 6.6.1(i),(ii) (`prop_12_5_1_i`, `prop_12_5_1_ii`)
give a measure-preserving injection `Γ^qd_stab(G_α,H_α) ↪ Γ^qd_stab(G,H)` (argued locally: near a
class with distinct eigenvalues on `W''` (full measure) the weight `|W(T)|⁻¹` cancels the
`|W(T)|`-to-1 projection, so `|W(T_x)| ≠ |W(T_y)|` is
harmless); TRANS gives
`c_{θ_α}(y) = e(G_α) c_{θ_1}(x)`; and the finite sum over `α` commutes with the limit by absolute
convergence.  These inputs are passed as hypotheses so that the dependency
of the main theorem on them is explicit. -/
theorem stable_rearrangement (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (P : TemperedPacketFamily d IF)
    (hgerm : PacketGermTransfer ψ P)
    (hvanish : ∀ (α : IF.Idx) (θ : ↥(IF.data α).G → ℂ) (T : Subgroup ↥(GSpin (IF.data α).QW))
      (s : ℝ) (t : ↥(GSpin (IF.data α).QW)), ¬ IsQdAt (IF.data α) t →
        gammaIntegrand ψ (IF.data α) θ T s t = 0)
    (hi : ∀ (α : IF.Idx) (y : ↥(GSpin (IF.data α).QW)), (IF.data α).IsGammaElt y →
      IsQdAt (IF.data α) y → ∃ x : ↥(GSpin d.QW), d.IsGammaElt x ∧
        d.StronglyStablyConjW (IF.twist α) x y)
    (hii : ∀ (α : IF.Idx) (x : ↥(GSpin d.QW)) (y : ↥(GSpin (IF.data α).QW)), d.IsGammaElt x →
      (IF.data α).IsGammaElt y → d.StronglyStablyConjW (IF.twist α) x y →
        TorusTransfer IF α x y) :
    ∑ᶠ α : IF.Idx, mGeom ψ (IF.data α) (P.packetChar α) =
      limUnder (𝓝[>] (0 : ℝ)) (mGeomStabS ψ IF P.baseChar) := by
  have : Finite IF.Idx := IF.finite_idx
  let : Fintype IF.Idx := Fintype.ofFinite _
  have hlim : Tendsto (fun s => ∑ α, mGeomS ψ (IF.data α) (P.packetChar α) s) (𝓝[>] (0 : ℝ))
      (𝓝 (∑ α, mGeom ψ (IF.data α) (P.packetChar α))) :=
    tendsto_finsetSum _ fun α _ => tendsto_mGeomS_mGeom ψ (IF.data α) (P.packetChar_mem_QCfin α)
  have heq : (fun s => ∑ α, mGeomS ψ (IF.data α) (P.packetChar α) s) =ᶠ[𝓝[>] (0 : ℝ)]
      mGeomStabS ψ IF P.baseChar :=
    eventually_nhdsWithin_of_forall fun s hs => by
      show ∑ α, _ = _
      rw [← finsum_eq_sum_of_fintype]
      exact stable_rearrangement_pos ψ hqs IF P hgerm hvanish hi hii hs
  rw [finsum_eq_sum_of_fintype]
  exact ((hlim.congr' heq).limUnder_eq).symm

/-- **The atom computation** (own work; Thesis §6.7 after (6.7.6): "only the atom
`x = 1` of `Γ(G,H)` contributes").  If the signed count is `[t central]` on quasi-split classes
(`signed_count`), then for `s > 0` the stable integral reduces to the contribution of the atom
`T = A_{G,H}`: `|W(A)| = 1`, `T(F)/A(F)` is a point, `D^G(1) = Δ(1) = 1`, `n_1(1) = 1`, and
`c_{θ_1}(c) = c_{θ_1}(1)` for `c ∈ A_{G,H}(F)` (central character trivial on `Z_{G,H}(F)`); the
non-quasi-split classes vanish by `gammaIntegrand_eq_zero_of_not_qd`. -/
theorem mGeomStabS_eq_germ_one (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (P : TemperedPacketFamily d IF)
    (hsc : ∀ t : ↥(GSpin d.QW), d.IsGammaElt t → IsQdAt d t →
      signedCount IF t = if IsCentralW d t then 1 else 0)
    (s : ℝ) (hs : 0 < s) :
    mGeomStabS ψ IF P.baseChar s = germ d.G d.lie d.bilin ψ P.baseChar (d.diag 1) (orbitChoice d 1) := by
  have _ := hs -- not needed: the identity holds for every `s` (the atom has `Δ = 1`)
  rw [mGeomStabS_eq_atom ψ IF hsc]
  exact atom_value ψ hqs IF P hsc s _ out_atomClass

/-- **Thesis (6.7.7)**: `Σ_α Σ_{π ∈ Π_α} m(π) = c_{θ_1, O_1}(1)`.  A genuine proof
from `packet_sum_mult`, `stable_rearrangement` (fed with `packet_germ_transfer`,
`gammaIntegrand_eq_zero_of_not_qd`, `prop_12_5_1_i`, `prop_12_5_1_ii`), `signed_count` and
`mGeomStabS_eq_germ_one`. -/
theorem sum_mult_eq_germ_one (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (P : TemperedPacketFamily d IF) :
    ∑ᶠ α : IF.Idx, ∑ i, ((mult ψ (IF.data α) (P.rep α i)).toNat : ℂ) =
      germ d.G d.lie d.bilin ψ P.baseChar (d.diag 1) (orbitChoice d 1) := by
  rw [finsum_congr (packet_sum_mult ψ P), stable_rearrangement ψ hqs IF P
    (packetGermTransfer_holds ψ hqs P)
    (fun α θ T s t ht => gammaIntegrand_eq_zero_of_not_qd ψ (IF.data α) θ T s t ht)
    (fun α y hy hqd => prop_12_5_1_i hqs IF α y hy hqd)
    (fun α x y hx hy hxy => prop_12_5_1_ii IF α x y hx hy hxy)]
  have hsc := fun t ht hqd => signed_count hqs IF t ht hqd
  have hlim : Tendsto (mGeomStabS ψ IF P.baseChar) (𝓝[>] (0 : ℝ))
      (𝓝 (germ d.G d.lie d.bilin ψ P.baseChar (d.diag 1) (orbitChoice d 1))) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs =>
      (mGeomStabS_eq_germ_one ψ hqs IF P hsc s hs).symm)
  exact hlim.limUnder_eq

end Stable

/-! ## 9. The germ at `1` and Whittaker models (Thesis (6.7.1)) -/

/-- `Nil_reg(𝔤) ≠ ∅` for quasi-split `G` (`nilReg_centralizer_nonempty_iff` at `x = 1`, where the moved part is `0`). -/
theorem nilReg_one_nonempty (d : GGPData F) (hqs : d.IsQuasiSplit) :
    (NilReg (grpCentralizer d.G ((d.diag 1 : d.G) : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag 1 : d.G) : d.ambientˣ) : d.ambient))).Nonempty :=
  (nilReg_centralizer_nonempty_iff d 1 (isSS_one_W d) (movedPartAbelian_one d)).2
    (isQdAt_of_fixedSub_eq_top d hqs 1 (fixedSub_one_eq_top d.QW))

/-- `O_x` is regular as soon as some regular orbit satisfies Luo's condition `OrbitSpec`. -/
theorem orbitChoice_mem_nilReg_of_exists (d : GGPData F) (x : ↥(GSpin d.QW))
    (h : ∃ O ∈ NilReg (grpCentralizer d.G (d.diag x : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag x : d.ambientˣ)) : d.ambient)),
      ∃ X ∈ nilOrbitSet O, OrbitSpec d x (X : d.ambient)) :
    orbitChoice d x ∈ NilReg (grpCentralizer d.G (d.diag x : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag x : d.ambientˣ)) : d.ambient)) := by
  have e : orbitChoice d x = h.choose := dite_eq_left h
  rw [e]
  exact h.choose_spec.1

open CliffordAlgebra in
/-- Conjugation by `GSpin(V)` preserves `gspin(V)` (same proof as `conj_mem_gspin` of
`TraceFormula/ThetaF`, which `Main` does not import). -/
private theorem conj_mem_gspin' {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)
    (g : GSpin Q) {X : CliffordAlgebra Q} (hX : X ∈ gspin Q) :
    ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * X *
      (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ gspin Q := by
  obtain ⟨hX0, hX⟩ := hX
  set u : (CliffordAlgebra Q)ˣ := (g : (CliffordAlgebra Q)ˣ)
  have hg := g.2
  refine ⟨?_, fun v => ?_⟩
  · exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hg.1 hX0) (g⁻¹ : GSpin Q).2.1
  · obtain ⟨w, hw⟩ := hg.2.2 v
    have hv : ι Q v = (u : CliffordAlgebra Q) * ι Q w * ((u⁻¹ : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q) := by
      rw [hw]
      simp [u, mul_assoc]
    obtain ⟨t, ht⟩ := hX w
    obtain ⟨r, hr⟩ := hg.2.1 t
    refine ⟨r, ?_⟩
    rw [hr, hv, Ring.lie_def]
    rw [Ring.lie_def] at ht
    rw [ht]
    simp only [mul_sub, sub_mul, mul_assoc, Units.inv_mul_cancel_left]
    rfl

/-- Conjugation by `G(F)` preserves `𝔤`. -/
theorem conj_mem_lie_of_mem_G (d : GGPData F) {g : d.ambientˣ} (hg : g ∈ d.G) {Y : d.ambient}
    (hY : Y ∈ d.lie) : (g : d.ambient) * Y * (↑g⁻¹ : d.ambient) ∈ d.lie :=
  ⟨conj_mem_gspin' d.QW (d.fst ⟨g, hg⟩) hY.1, conj_mem_gspin' d.QV (d.snd ⟨g, hg⟩) hY.2⟩

/-- `dim 𝔤_{gXg⁻¹} = dim 𝔤_X` when conjugation by `g` and `g⁻¹` preserves `𝔤`. -/
theorem finrank_lieCentralizer_conj {A : Type*} [Ring A] [Algebra F A] (𝔤 : LieSubalgebra F A)
    (g : Aˣ) (hg : ∀ Y ∈ 𝔤, (g : A) * Y * (↑g⁻¹ : A) ∈ 𝔤)
    (hg' : ∀ Y ∈ 𝔤, (↑g⁻¹ : A) * Y * (g : A) ∈ 𝔤) (X : A) :
    finrank F ↥(lieCentralizer 𝔤 ((g : A) * X * (↑g⁻¹ : A))) =
      finrank F ↥(lieCentralizer 𝔤 X) := by
  set φ := conjAd F g
  have hmap : (lieCentralizer 𝔤 X).toSubmodule.map φ.toLinearEquiv.toLinearMap =
      (lieCentralizer 𝔤 ((g : A) * X * (↑g⁻¹ : A))).toSubmodule := by
    ext Z
    rw [Submodule.mem_map_equiv, LieSubalgebra.mem_toSubmodule, LieSubalgebra.mem_toSubmodule,
      mem_lieCentralizer, mem_lieCentralizer]
    have hs : φ.toLinearEquiv.symm Z = (↑g⁻¹ : A) * Z * (g : A) := rfl
    rw [hs]
    constructor
    · rintro ⟨hZ, hc⟩
      refine ⟨by simpa [mul_assoc] using hg _ hZ, ?_⟩
      have := congrArg (fun T => (g : A) * T * (↑g⁻¹ : A)) hc
      simpa [mul_assoc] using this
    · rintro ⟨hZ, hc⟩
      refine ⟨hg' _ hZ, ?_⟩
      have := congrArg (fun T => (↑g⁻¹ : A) * T * (g : A)) hc
      simpa [mul_assoc] using this
  show finrank F ↥(lieCentralizer 𝔤 ((g : A) * X * (↑g⁻¹ : A))).toSubmodule =
    finrank F ↥(lieCentralizer 𝔤 X).toSubmodule
  rw [← hmap]
  exact ((φ.toLinearEquiv.submoduleMap (lieCentralizer 𝔤 X).toSubmodule).finrank_eq).symm

/-- The orbit of a regular nilpotent element is a regular orbit (regularity is invariant under
conjugation by `G`, when `G` preserves `𝔤`). -/
theorem mk_mem_nilReg_of_isRegularNil {A : Type*} [Ring A] [Algebra F A] (G : Subgroup Aˣ)
    (𝔤 : LieSubalgebra F A) (hG : ∀ g ∈ G, ∀ Y ∈ 𝔤, (g : A) * Y * (↑g⁻¹ : A) ∈ 𝔤)
    (X : {X : A // X ∈ 𝔤 ∧ IsNilpotent X}) (hX : IsRegularNil 𝔤 X.1) :
    Quotient.mk (nilSetoid G 𝔤) X ∈ NilReg G 𝔤 := by
  show IsRegularNil 𝔤 (Quotient.out (Quotient.mk (nilSetoid G 𝔤) X)).1
  obtain ⟨g, hgG, hgX⟩ := Quotient.exact (Quotient.out_eq (Quotient.mk (nilSetoid G 𝔤) X))
  obtain ⟨hmem, hnil⟩ := (Quotient.out (Quotient.mk (nilSetoid G 𝔤) X)).2
  refine ⟨hmem, hnil, ?_⟩
  have hg' : ∀ Y ∈ 𝔤, (↑g⁻¹ : A) * Y * (g : A) ∈ 𝔤 := fun Y hY => by
    simpa using hG g⁻¹ (G.inv_mem hgG) Y hY
  rw [← finrank_lieCentralizer_conj 𝔤 g (hG g hgG) hg', hgX]
  exact hX.2.2

/-- `𝔤_{(a,b)} = gspin(W)_a × gspin(V)_b`. -/
theorem finrank_lieCentralizer_lie (d : GGPData F) (X : d.ambient) :
    finrank F ↥(lieCentralizer d.lie X) =
      finrank F ↥(lieCentralizer (gspin d.QW) X.1) + finrank F ↥(lieCentralizer (gspin d.QV) X.2) := by
  have h : (lieCentralizer d.lie X).toSubmodule =
      (lieCentralizer (gspin d.QW) X.1).toSubmodule.prod (lieCentralizer (gspin d.QV) X.2).toSubmodule := by
    ext Y
    simp only [LieSubalgebra.mem_toSubmodule, Submodule.mem_prod, mem_lieCentralizer, Prod.ext_iff,
      Prod.fst_mul, Prod.snd_mul]
    exact ⟨fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨h1, h3⟩, h2, h4⟩, fun ⟨⟨h1, h3⟩, h2, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩⟩
  show finrank F ↥(lieCentralizer d.lie X).toSubmodule =
    finrank F ↥(lieCentralizer (gspin d.QW) X.1).toSubmodule +
      finrank F ↥(lieCentralizer (gspin d.QV) X.2).toSubmodule
  rw [h, (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]

/-- A pair of regular nilpotent elements is regular nilpotent in `𝔤 = gspin(W) ⊕ gspin(V)`
(`Nil_reg` of a product is the product). -/
theorem isRegularNil_lie_mk (d : GGPData F) {a : CliffordAlgebra d.QW} {b : CliffordAlgebra d.QV}
    (ha : IsRegularNil (gspin d.QW) a) (hb : IsRegularNil (gspin d.QV) b) :
    IsRegularNil d.lie ((a, b) : d.ambient) := by
  obtain ⟨haL, ⟨n, hn⟩, har⟩ := ha
  obtain ⟨hbL, ⟨k, hk⟩, hbr⟩ := hb
  refine ⟨⟨haL, hbL⟩, ⟨n + k, ?_⟩, ?_⟩
  · rw [Prod.pow_mk, pow_eq_zero_of_le (Nat.le_add_right n k) hn,
      pow_eq_zero_of_le (Nat.le_add_left k n) hk]; rfl
  · apply le_antisymm
    · rw [finrank_lieCentralizer_lie, har, hbr]
      have : Nonempty ↥d.lie := ⟨0⟩
      refine le_ciInf fun Y => ?_
      rw [finrank_lieCentralizer_lie]
      exact add_le_add (ciInf_le (OrderBot.bddBelow _) (⟨(Y : d.ambient).1, Y.2.1⟩ : ↥(gspin d.QW)))
        (ciInf_le (OrderBot.bddBelow _) (⟨(Y : d.ambient).2, Y.2.2⟩ : ↥(gspin d.QV)))
    · exact ciInf_le (OrderBot.bddBelow _) (⟨(a, b), haL, hbL⟩ : ↥d.lie)

/-- **A regular orbit satisfying Luo's condition exists at `x = 1` when `dim V` or `dim W` is even
`≥ 4`** (Luo §7.1).  From the literature axiom
`exists_regularNil_inOrbitNu` (Luo's orbit `O_ν` exists in `gspin(V)`, resp. `O_{−ν}` in
`gspin(W)`: Waldspurger 2010 §7.1, Luo §2.1), paired with a regular nilpotent of the other factor
(`nilReg_nonempty_iff_quasiSplit`); the pair is regular in `𝔤` (`isRegularNil_lie_mk`), and its
orbit is regular (`mk_mem_nilReg_of_isRegularNil`).  At `x = 1`, `W'_1 = W`, `V'_1 = V` and
`𝔤_1 = 𝔤`.  This is not a consequence of `nilReg_nonempty_iff_quasiSplit` /
`nilReg_centralizer_nonempty_iff` alone, which only give *some* regular orbit. -/
theorem exists_orbitSpec_one_of_even (d : GGPData F) (hqs : d.IsQuasiSplit)
    (h : (Even (finrank F ↥((fixedSub (1 : GSpin d.QW)).prod (⊤ : Submodule F d.Z))) ∧
        4 ≤ finrank F ↥((fixedSub (1 : GSpin d.QW)).prod (⊤ : Submodule F d.Z))) ∨
      (Even (finrank F ↥(fixedSub (1 : GSpin d.QW))) ∧ 4 ≤ finrank F ↥(fixedSub (1 : GSpin d.QW)))) :
    ∃ O ∈ NilReg (grpCentralizer d.G (d.diag 1 : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag 1 : d.ambientˣ)) : d.ambient)),
      ∃ X ∈ nilOrbitSet O, OrbitSpec d 1 (X : d.ambient) := by
  have hfix : fixedSub (1 : GSpin d.QW) = ⊤ := fixedSub_one_eq_top d.QW
  have h1 : ((d.diag 1 : d.G) : d.ambientˣ) = 1 := by rw [map_one]; rfl
  have hL : lieCentralizer d.lie (((d.diag 1 : d.ambientˣ)) : d.ambient) = d.lie := by
    ext Y
    rw [mem_lieCentralizer, h1, Units.val_one, one_mul, mul_one]
    simp
  -- an element `X` of `𝔤`, regular nilpotent, satisfying Luo's condition at `x = 1`
  have key : ∃ X : d.ambient, IsRegularNil d.lie X ∧ OrbitSpec d 1 X := by
    obtain ⟨hV1, hW1⟩ := exists_regularNil_inOrbitNu d hqs
    by_cases hV : Even (finrank F ↥((fixedSub (1 : GSpin d.QW)).prod (⊤ : Submodule F d.Z))) ∧
        4 ≤ finrank F ↥((fixedSub (1 : GSpin d.QW)).prod (⊤ : Submodule F d.Z))
    · have hV' := hV
      rw [hfix, Submodule.prod_top, finrank_top] at hV'
      obtain ⟨b, hb, hbν⟩ := hV1 hV'.1 hV'.2
      obtain ⟨O, hO⟩ := (nilReg_nonempty_iff_quasiSplit d.QW d.nondeg).mpr hqs.1
      refine ⟨((Quotient.out O).1, b), isRegularNil_lie_mk d hO hb, ?_⟩
      unfold OrbitSpec
      rw [ite_eq_left_of_eq_true _ _ (eq_true hV), hfix, Submodule.prod_top]
      exact hbν
    · have hW := h.resolve_left hV
      have hW' := hW
      rw [hfix, finrank_top, Module.finrank_fin_fun] at hW'
      obtain ⟨a, ha, haν⟩ := hW1 hW'.1 hW'.2
      obtain ⟨O, hO⟩ := (nilReg_nonempty_iff_quasiSplit d.QV d.nondeg_QV).mpr hqs.2
      refine ⟨(a, (Quotient.out O).1), isRegularNil_lie_mk d ha hO, ?_⟩
      unfold OrbitSpec
      rw [ite_eq_right_of_eq_false _ _ (eq_false hV), ite_eq_left_of_eq_true _ _ (eq_true hW), hfix]
      exact haν
  obtain ⟨X, hX, hspec⟩ := key
  have hX1 : X ∈ lieCentralizer d.lie (((d.diag 1 : d.ambientˣ)) : d.ambient) := by
    rw [hL]; exact hX.1
  refine ⟨Quotient.mk _ ⟨X, hX1, hX.2.1⟩, ?_, ⟨X, hX1⟩, ⟨hX.2.1, rfl⟩, hspec⟩
  refine mk_mem_nilReg_of_isRegularNil _ _ (fun g hg Y hY => ?_) _ (by show IsRegularNil _ X; rw [hL]; exact hX)
  rw [hL] at hY ⊢
  exact conj_mem_lie_of_mem_G d (Subgroup.mem_inf.mp hg).1 hY

/-- A regular orbit satisfying `OrbitSpec d 1` exists: where Luo's recipe imposes no condition, by
`nilReg_one_nonempty`; otherwise by `exists_orbitSpec_one_of_even`. -/
theorem exists_orbitSpec_one (d : GGPData F) (hqs : d.IsQuasiSplit) :
    ∃ O ∈ NilReg (grpCentralizer d.G (d.diag 1 : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag 1 : d.ambientˣ)) : d.ambient)),
      ∃ X ∈ nilOrbitSet O, OrbitSpec d 1 (X : d.ambient) := by
  by_cases hV : Even (finrank F ↥((fixedSub (1 : GSpin d.QW)).prod (⊤ : Submodule F d.Z))) ∧
      4 ≤ finrank F ↥((fixedSub (1 : GSpin d.QW)).prod (⊤ : Submodule F d.Z))
  · exact exists_orbitSpec_one_of_even d hqs (Or.inl hV)
  by_cases hW : Even (finrank F ↥(fixedSub (1 : GSpin d.QW))) ∧
      4 ≤ finrank F ↥(fixedSub (1 : GSpin d.QW))
  · exact exists_orbitSpec_one_of_even d hqs (Or.inr hW)
  obtain ⟨O, hO⟩ := nilReg_one_nonempty d hqs
  refine ⟨O, hO, ⟨(Quotient.out O).1, (Quotient.out O).2.1⟩, ⟨(Quotient.out O).2.2, ?_⟩, ?_⟩
  · exact Quotient.out_eq O
  · unfold OrbitSpec
    rw [ite_eq_right hV, ite_eq_right hW]
    trivial

/-- **The orbit `O_1` is regular** for quasi-split `G` (own work, after Luo §7.1:
Luo's recipe applied to `(G'_1, H'_1) = (G, H)` selects a regular nilpotent orbit of `𝔤`, which
exists since `G` is quasi-split, `nilReg_nonempty_iff_quasiSplit`).  Needed to apply Rodier's
theorem to `c_{θ, O_1}(1)`. -/
theorem orbitChoice_one_mem_nilReg (d : GGPData F) (hqs : d.IsQuasiSplit) :
    orbitChoice d 1 ∈ NilReg (grpCentralizer d.G ((d.diag 1 : d.G) : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag 1 : d.G) : d.ambientˣ) : d.ambient)) :=
  orbitChoice_mem_nilReg_of_exists d 1 (exists_orbitSpec_one d hqs)

/-- `1` is semisimple. -/
theorem isSS_one (d : GGPData F) : IsSS F (((d.diag 1 : d.G) : d.ambientˣ) : d.ambient) := by
  rw [map_one]
  show Module.End.IsSemisimple (LinearMap.mulLeft F (1 : d.ambient))
  rw [LinearMap.mulLeft_one]
  exact Module.End.isSemisimple_id

/-- Generic counting step: if `f` takes values in `{0,1}` and exactly one value is `1`, the sum
of `f` is `1`. -/
theorem sum_ite_unique_eq_one {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (h : ∃! i, P i) : ∑ i, (if P i then (1 : ℂ) else 0) = 1 := by
  obtain ⟨i, hi, huniq⟩ := h
  rw [Finset.sum_eq_single i
    (fun j _ hj => by simp [show ¬ P j from fun hPj => hj (huniq j hPj)]) (by simp)]
  simp [hi]

/-- **Thesis (6.7.1)**: `Σ_α Σ_{π ∈ Π_α} m(π) = 1`, in `ℂ`.  From
(6.7.7) (`sum_mult_eq_germ_one`), linearity of germs, Rodier's theorem (BP Prop. 4.8.1(i),
`rodier_germ_one`: `c_{π,O_1}(1)` is `1` or `0` according as `π` has a Whittaker model of the
type attached to `O_1`) and (WHITT). -/
theorem sum_mult_eq_one_complex {d : GGPData F} (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (P : TemperedPacketFamily d IF) :
    ∑ᶠ α : IF.Idx, ∑ i, ((mult ψ (IF.data α) (P.rep α i)).toNat : ℂ) = 1 := by
  rw [sum_mult_eq_germ_one ψ hqs IF P, TemperedPacketFamily.baseChar,
    germ_transportFn_one ψ IF.data_base]
  have hqs' : (IF.data IF.base).IsQuasiSplit := by rw [IF.data_base]; exact hqs
  have hO := orbitChoice_one_mem_nilReg (IF.data IF.base) hqs'
  rw [P.packetChar_eq_sum, germ_finset_sum (IF.data IF.base) ψ Finset.univ
    (fun i => charG (IF.data IF.base) (P.rep IF.base i)) (isSS_one (IF.data IF.base))
    (fun i _ => (hc_character_isQuasiCharacter (IF.data IF.base) ψ (P.rep IF.base i)
      (P.tempered IF.base i)).2 _ (isSS_one (IF.data IF.base))) hO]
  obtain ⟨w, hw⟩ := rodier_germ_one (IF.data IF.base) hqs' ψ ((IF.data IF.base).diag 1)
    (map_one _) _ hO
  have hval : ∀ i, germ (IF.data IF.base).G (IF.data IF.base).lie (IF.data IF.base).bilin ψ
      (charG (IF.data IF.base) (P.rep IF.base i)) ((IF.data IF.base).diag 1)
      (orbitChoice (IF.data IF.base) 1) =
        if HasModel (P.rep IF.base i) w.U w.χ then 1 else 0 := by
    intro i
    split_ifs with hm
    · exact (hw _ (P.tempered IF.base i)).1 hm
    · exact (hw _ (P.tempered IF.base i)).2 hm
  rw [Finset.sum_congr rfl fun i _ => hval i]
  exact sum_ite_unique_eq_one _ (P.whitt w)

/-- **Thesis (6.7.1)** in `ℕ∞`: `Σ_{(α, π)} m(π) = 1`, the sum over all members
of all packets (finite: `InnerFormSystem.finite_idx`).  Uses `m(π) ≠ ∞` (`mult_ne_top`). -/
theorem sum_mult_eq_one {d : GGPData F} (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (P : TemperedPacketFamily d IF) [Fintype IF.Idx] :
    ∑ p : Σ α : IF.Idx, P.ι α, mult ψ (IF.data p.1) (P.rep p.1 p.2) = 1 := by
  have hC := sum_mult_eq_one_complex ψ hqs IF P
  rw [finsum_eq_sum_of_fintype] at hC
  have hN : ∑ p : Σ α : IF.Idx, P.ι α, (mult ψ (IF.data p.1) (P.rep p.1 p.2)).toNat = 1 := by
    rw [Fintype.sum_sigma]
    exact_mod_cast hC
  have hcoe : ∀ p : Σ α : IF.Idx, P.ι α, mult ψ (IF.data p.1) (P.rep p.1 p.2) =
      ((mult ψ (IF.data p.1) (P.rep p.1 p.2)).toNat : ℕ∞) :=
    fun p => (ENat.natCast_toNat (mult_ne_top ψ P p.1 p.2)).symm
  rw [Finset.sum_congr rfl fun p _ => hcoe p, ← Nat.cast_sum, hN, Nat.cast_one]

/-- Generic counting step: a finite family in `ℕ∞` with sum `1` has exactly one member equal to
`1`, and all members are `0` or `1`. -/
theorem enat_sum_eq_one {ι : Type*} [Fintype ι] (f : ι → ℕ∞) (h : ∑ i, f i = 1) :
    (∃! i, f i = 1) ∧ ∀ i, f i = 1 ∨ f i = 0 := by
  have hle : ∀ i, f i ≤ 1 := fun i => h ▸ Finset.single_le_sum (fun j _ => zero_le)
    (Finset.mem_univ i)
  have hpair : ∀ i j, i ≠ j → f i + f j ≤ 1 := by
    intro i j hij
    rw [← h, ← Finset.sum_pair hij]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => zero_le)
  have h01 : ∀ i, f i = 1 ∨ f i = 0 := by
    intro i
    have := hle i
    rcases lt_or_eq_of_le this with hlt | heq
    · exact Or.inr (Order.lt_one_iff.mp hlt)
    · exact Or.inl heq
  refine ⟨?_, h01⟩
  have hex : ∃ i, f i = 1 := by
    by_contra hne
    push Not at hne
    have : ∀ i, f i = 0 := fun i => (h01 i).resolve_left (hne i)
    simp [this] at h
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, hi, fun j hj => ?_⟩
  by_contra hji
  have := hpair j i hji
  rw [hi, hj] at this
  exact absurd this (by decide)

/-! ## 10. The main theorem -/

/-- **MAIN THEOREM: the local Gan–Gross–Prasad conjecture for general spin groups**
(Thesis Thm. 6.4.1 (= Thm. 1.0.1)), `p`-adic case.  Let `G` be quasi-split
and `{Π_α}` tempered packets on the inner forms `G_α` (`α ∈ H¹(F, SO(W))`) with
central characters trivial on `Z_{G,H}(F)` satisfying (STAB), (TRANS), (WHITT).  Then exactly one
`π ∈ ⊔_α Π_α` has `m(π) = 1`, and `m(π') = 0` for all the others.

The proof (Thesis §6.7) is the count `Σ_α Σ_{π∈Π_α} m(π) = 1` (`sum_mult_eq_one`),
together with `m(π) ∈ ℕ` (`mult_ne_top`); multiplicity one (`emoryTakeda_mult_le_one`) is not
needed for this deduction. -/
theorem local_ggp (d : GGPData F) (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (P : TemperedPacketFamily d IF) :
    (∃! p : Σ α : IF.Idx, P.ι α, mult ψ (IF.data p.1) (P.rep p.1 p.2) = 1) ∧
    ∀ p : Σ α, P.ι α, mult ψ (IF.data p.1) (P.rep p.1 p.2) = 1 ∨
      mult ψ (IF.data p.1) (P.rep p.1 p.2) = 0 := by
  have : Finite IF.Idx := IF.finite_idx
  have : Fintype IF.Idx := Fintype.ofFinite _
  exact enat_sum_eq_one _ (sum_mult_eq_one ψ hqs IF P)

end GSpinGGP
