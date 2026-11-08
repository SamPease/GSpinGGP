import GSpinGGP.GGP.Triple
import GSpinGGP.TraceFormula.Spine
import GSpinGGP.GGP.Germs
import GSpinGGP.GGP.Centralizers
import GSpinGGP.GGP.RegularNilpotentConverse
import GSpinGGP.GGP.KottwitzSign
import GSpinGGP.GGP.Hilbert90
import GSpinGGP.GGP.TwistDescent
import GSpinGGP.GGP.TwistPlaneCocycle
import GSpinGGP.GGP.WittParity
import GSpinGGP.GGP.TorusCommute
import GSpinGGP.GGP.TorusTransport
import GSpinGGP.GGP.QuadClassify
import GSpinGGP.GGP.MovedCentralizer
import GSpinGGP.GGP.GaloisTorus
import GSpinGGP.GGP.TwistIncl
import GSpinGGP.GGP.StableCocycleSurj
import GSpinGGP.GGP.OrbitSpecQd
import GSpinGGP.GGP.TorusIntegral
import GSpinGGP.GGP.TwistMoved
import GSpinGGP.GGP.TwistToForm
import GSpinGGP.GGP.TwistSymm
import GSpinGGP.GGP.MovedAniso

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

/-- **Thesis Prop. 6.6.1(i), Steps 2–3** (own work, citing Kottwitz 1986, Lemma 10.2): given an
isometric embedding `ι : W'_{α,y} ↪ W`, some `x ∈ Γ(G,H)` is strongly stably conjugate to `y`.
Proof: `W` is the twist of `W_α` by a cocycle with values in `S_y(F̄)`
(`exists_isTwistBy_torusBar_of_isometry`: twist `W''_{α,y}` into `ι(W'_{α,y})^⊥` in block
coordinates; the cocycle lies in `SO(W_α)_{W'_y}(F̄)`, and Kottwitz 1986, Lemma 10.2 moves it into
`S_y(F̄)`).  The construction of Prop. 6.6.1(iii) (`exists_stronglyStablyConj_of_isTwistBy`,
`isGammaElt_of_ratAt`) for the datum `G_α` and the inverse twist `τ_α⁻¹ = (W, φ_α⁻¹)`
(`InnerTwist.symm`; `G_α` twisted by it is `G`) gives `x ∈ Γ(G,H)` strongly stably conjugate to `y`
through `τ_α⁻¹`, i.e. `y` to `x` through `τ_α` (`stronglyStablyConjW_of_symm`).  This differs from
Thesis Prop. 6.6.1(i), Steps 2–3, which use quasi-splitness of `GSpin(W'')` and (12.1.1): Kottwitz's
lemma needs no quasi-splitness, so `hqs`, `hqd` are not needed (they are kept for the callers). -/
theorem exists_stronglyStablyConj_of_isometry (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (α : IF.Idx) (y : ↥(GSpin (IF.data α).QW)) (hy : (IF.data α).IsGammaElt y)
    (hqd : IsQdAt (IF.data α) y) (ι : (IF.data α).QW.comp (fixedSub y).subtype →qᵢ d.QW)
    (hι : Function.Injective ι) :
    ∃ x : ↥(GSpin d.QW), d.IsGammaElt x ∧ d.StronglyStablyConjW (IF.twist α) x y := by
  have _ := hqs
  have _ := hqd
  set τ' := (IF.twist α).symm d.nondeg
  obtain ⟨a, ha⟩ := exists_isTwistBy_torusBar_of_isometry (d := IF.data α) hy τ'.sameDisc ι hι
  obtain ⟨x, hst, -⟩ := (IF.data α).exists_stronglyStablyConj_of_isTwistBy τ' hy a ha
  obtain ⟨g, hg, hconj, hrat⟩ := hst.1
  exact ⟨x, (IF.data α).isGammaElt_of_ratAt τ' hy hg hrat hconj,
    d.stronglyStablyConjW_of_symm (IF.twist α) hst⟩

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
    rw [e1, e2, ← TorusTransfer.bcUnits_conj_ι', map_mul, map_mul]
    rfl
  apply ι_injective (τ.Q'.baseChange (AlgebraicClosure F))
  rw [← TorusTransfer.bcUnits_conj_ι', ← hinv, ← h, ι_specP, ι_specP, ← hU]
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


variable {V : Type*} [AddCommGroup V] [Module F V]

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
    exact ⟨conj_mem_gspin _ ⟨g₁, hg₁⟩ (map_mem_gspin φ₁ hp.1),
      conj_mem_gspin _ ⟨g₂, hg₂⟩ (map_mem_gspin φ₂ hp.2)⟩
  · intro q hq
    refine ⟨(psiPair φ₁ φ₂ g₁ g₂).symm q, ?_, (psiPair φ₁ φ₂ g₁ g₂).apply_symm_apply q⟩
    rw [psiPair_symm_apply]
    refine ⟨map_mem_gspin φ₁.symm ?_, map_mem_gspin φ₂.symm ?_⟩
    · simpa using conj_mem_gspin _ (⟨g₁, hg₁⟩⁻¹ : GSpin _) hq.1
    · simpa using conj_mem_gspin _ (⟨g₂, hg₂⟩⁻¹ : GSpin _) hq.2

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



section TorusNat

open CliffordAlgebra Module
open scoped TensorProduct


section Clause6


theorem cliffUnits_symm_cliffUnits {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁]
    [AddCommGroup V₂] [Module F V₂] {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}
    (φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F)))
    (z : (CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F)))ˣ) :
    cliffUnits φ.symm (cliffUnits φ z) = z :=
  Units.ext (TorusTransfer.map_symm_map φ z)

theorem cliffUnits_cliffUnits_symm {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁]
    [AddCommGroup V₂] [Module F V₂] {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}
    (φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F)))
    (z : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ) :
    cliffUnits φ (cliffUnits φ.symm z) = z :=
  Units.ext (TorusTransfer.map_map_symm φ z)

/-- A group identity behind the `V`-component: if `g_V` and `g₂` both conjugate `f(X)` to `B`, and
everything commuting with `X` (pulled back by `f'`) commutes with `T`, then they conjugate `f(T)`
alike. -/
theorem conj_transfer {G H : Type*} [Group G] [Group H] (f : G →* H) (f' : H →* G)
    (hff : ∀ a, f' (f a) = a) (hf'f : ∀ b, f (f' b) = b) (gV g₂ : H) {X T : G} {A B : H}
    (hA : gV * f T * gV⁻¹ = A) (hB : gV * f X * gV⁻¹ = B) (hC : g₂ * f X * g₂⁻¹ = B)
    (hcomm : f' (gV⁻¹ * g₂) * X = X * f' (gV⁻¹ * g₂) →
      f' (gV⁻¹ * g₂) * T = T * f' (gV⁻¹ * g₂)) :
    g₂ * f T * g₂⁻¹ = A := by
  obtain ⟨k, hk⟩ : ∃ k, k = gV⁻¹ * g₂ := ⟨_, rfl⟩
  rw [← hk] at hcomm
  have heq : g₂ * f X * g₂⁻¹ = gV * f X * gV⁻¹ := hC.trans hB.symm
  have hkX : k * f X = f X * k := by
    calc k * f X = gV⁻¹ * (g₂ * f X * g₂⁻¹) * g₂ := by simp [hk, mul_assoc]
      _ = gV⁻¹ * (gV * f X * gV⁻¹) * g₂ := by rw [heq]
      _ = f X * k := by simp [hk, mul_assoc]
  have h1 : f' k * X = X * f' k := by
    have := congrArg f' hkX
    rwa [map_mul, map_mul, hff] at this
  have h2 := hcomm h1
  have hkT : k * f T = f T * k := by
    have := congrArg f h2
    rwa [map_mul, map_mul, hf'f] at this
  have hg₂ : g₂ = gV * k := by simp [hk]
  rw [← hA, hg₂, mul_inv_rev]
  calc gV * k * f T * (k⁻¹ * gV⁻¹) = gV * (k * f T) * k⁻¹ * gV⁻¹ := by simp [mul_assoc]
    _ = gV * f T * gV⁻¹ := by rw [hkT]; simp [mul_assoc]

/-- **Thesis Prop. 6.6.1(ii), strong stable conjugacy on `T_{x,♮}`**: every `t ∈ T_x(F)` with
`t ∈ Γ(G,H)` and `T_t = T_x` is strongly stably conjugate to its transport `e(t)`. The centralizers
of `t̄` and `x̄` agree over `F̄` (on `W` and on `V`), so the rationality clauses for `x` give those
for `t`; on `V` the conjugating element of `hxy` is used, which agrees with the image of `g` up to
an element of `Z(x̄) = Z(t̄)`. -/
theorem stronglyStablyConjW_of_torusOf_eq (IF : InnerFormSystem d) (α : IF.Idx)
    (x : ↥(GSpin d.QW)) (y : ↥(GSpin (IF.data α).QW)) (hx : d.IsGammaElt x)
    (hxy : d.StronglyStablyConjW (IF.twist α) x y)
    {g : (CliffordAlgebra ((IF.data α).QW.baseChange (AlgebraicClosure F)))ˣ}
    (hg : g ∈ GSpin ((IF.data α).QW.baseChange (AlgebraicClosure F)))
    (hconj : g * cliffUnits (IF.twist α).φ (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ)) * g⁻¹ =
      bcUnits (IF.data α).QW (y : (CliffordAlgebra _)ˣ))
    (hrat : TorusTransfer.RatAt (IF.twist α).φ g (x : (CliffordAlgebra d.QW)ˣ))
    (t : ↥(d.torusOf x)) (s : ↥(GSpin (IF.data α).QW))
    (hs : bcUnits (IF.data α).QW (s : (CliffordAlgebra _)ˣ) =
      TorusTransfer.psiU (IF.twist α).φ g
        (bcUnits d.QW ((t : ↥(GSpin d.QW)) : (CliffordAlgebra d.QW)ˣ)))
    (ht : d.IsGammaElt t) (hT : d.torusOf t = d.torusOf x) :
    d.StronglyStablyConjW (IF.twist α) t s := by
  obtain ⟨-, g₂, hg₂, hconj₂, hrat₂⟩ := hxy
  refine ⟨⟨g, hg, hs.symm, fun σ z hz hzt => hrat σ z hz ?_⟩, ⟨g₂, hg₂, ?_, fun σ z hz hzt =>
    hrat₂ σ z hz ?_⟩⟩
  · have h := (d.commute_bc_iff_of_torusOf_eq hx ht t.2 hT ⟨z, hz⟩).mp
      (Subtype.ext hzt.eq)
    exact congrArg Subtype.val h.eq
  · refine conj_transfer (cliffUnits (d.twistV (IF.twist α)))
      (cliffUnits (d.twistV (IF.twist α)).symm) (cliffUnits_symm_cliffUnits _)
      (cliffUnits_cliffUnits_symm _) _ g₂
      (conj_gV (IF.twist α) hg t s hs) (conj_gV (IF.twist α) hg x y hconj.symm) hconj₂
      (fun hk' => ?_)
    have hkG := TorusTransfer.cliffUnits_mem_GSpin (d.twistV (IF.twist α)).symm
      ((GSpin _).mul_mem ((GSpin _).inv_mem
        (GSpin.map (inlBC d (IF.twist α)) (isNondeg_baseChange _ (IF.twist α).nondeg')
          ⟨g, hg⟩).2) hg₂)
    have h := (d.commute_bc_incl_iff_of_torusOf_eq hx ht t.2 hT ⟨_, hkG⟩).mpr (Subtype.ext hk')
    exact congrArg Subtype.val h.eq
  · have h := (d.commute_bc_incl_iff_of_torusOf_eq hx ht t.2 hT ⟨z, hz⟩).mp
      (Subtype.ext hzt.eq)
    exact congrArg Subtype.val h.eq

end Clause6

end TorusNat

/-- **Thesis Prop. 6.6.1(ii), the torus isomorphism** (own work): the clauses of `TorusTransfer`
other than `Δ`, `D^G`, together with: every `t ∈ T_x(F)` is stably conjugate to `e(t)` (in `G`,
through `ψ_α`).  Proved: with `g` the `W`-component of the conjugating element in `hxy`,
`t ↦ g C(φ_α)(t) g⁻¹` restricts to a group isomorphism `e : T_x(F) ≃ T_y(F)`
(`TorusTransfer.transportEquiv`: values are Galois-fixed by the rationality clause, hence rational;
they commute with `y` and fix `W'_y`; the inverse comes from `g⁻¹` and `φ_α⁻¹`); it fixes the
scalars and sends `x ↦ y`; it and its inverse are continuous, being restrictions of `F`-linear
maps `C(W) → C(W_α)` (`TorusTransfer.continuous_of_bcUnits_eq`); `t` and `e(t)` are stably
conjugate in `G` (`stablyConjG_diag_of_psiU`); every `t ∈ T_{x,♮}` is strongly stably conjugate to
`e(t)` (`stronglyStablyConjW_of_torusOf_eq`); and `e` matches `T_{x,♮}` with `T_{y,♮}`: on the regular
parts the centralizers of `t̄` and `x̄` agree over `F̄`, `Ad(g) ∘ C(φ_α)` carries centralizers, fixed
spaces and semisimplicity across (`TorusTransfer.torusSub_eq_of_psiU`, `isSS_of_psiA`), and the
inverse transport gives the converse. -/
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
      (∀ t : ↥(d.torusOf x), d.StablyConjG (IF.twist α) (d.diag t) ((IF.data α).diag (e t))) := by
  obtain ⟨⟨g, hg, hconj, hrat⟩, -⟩ := id hxy
  let e : ↥(d.torusOf x) ≃* ↥((IF.data α).torusOf y) := TorusTransfer.transportEquiv hg hrat hconj
  have he : ∀ t : ↥(d.torusOf x), bcUnits (IF.data α).QW
      (((e t : ↥((IF.data α).torusOf y)) : ↥(GSpin (IF.data α).QW)) : (CliffordAlgebra _)ˣ) =
        TorusTransfer.psiU (IF.twist α).φ g
          (bcUnits d.QW ((t : ↥(GSpin d.QW)) : (CliffordAlgebra d.QW)ˣ)) :=
    TorusTransfer.bcUnits_transportEquiv hg hrat hconj
  have hyc : TorusTransfer.psiU (IF.twist α).φ g (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ)) =
      bcUnits (IF.data α).QW (y : (CliffordAlgebra _)ˣ) := hconj
  have hcomm : ∀ {V' : Type} [AddCommGroup V'] [Module F V'] {Q' : QuadraticForm F V'}
      {a b : GSpin Q'} (z : GSpin (Q'.baseChange (AlgebraicClosure F))),
      (Commute z (bcGSpin Q' a) ↔ Commute z (bcGSpin Q' b)) →
      (Commute (z : (CliffordAlgebra _)ˣ) (bcUnits Q' (a : (CliffordAlgebra Q')ˣ)) ↔
        Commute (z : (CliffordAlgebra _)ˣ) (bcUnits Q' (b : (CliffordAlgebra Q')ˣ))) := by
    intro V' _ _ Q' a b z h
    constructor
    · intro h1; exact congrArg Subtype.val (h.mp (Subtype.ext h1.eq)).eq
    · intro h1; exact congrArg Subtype.val (h.mpr (Subtype.ext h1.eq)).eq
  have c5 : ∀ t : ↥(d.torusOf x),
      (d.IsGammaElt t ∧ d.torusOf t = d.torusOf x ↔
        (IF.data α).IsGammaElt (e t) ∧ (IF.data α).torusOf (e t) = (IF.data α).torusOf y) := by
    intro t
    constructor
    · rintro ⟨ht, hT⟩
      have hs := (he t).symm
      have hT' : (IF.data α).torusOf (e t) = (IF.data α).torusOf y :=
        TorusTransfer.torusSub_eq_of_psiU hg hyc hs
          (fun z hz => hcomm ⟨z, hz⟩ (d.commute_bc_iff_of_torusOf_eq hx ht t.2 hT ⟨z, hz⟩))
          (d.fixedSub_eq_of_torusOf_eq t.2 hT)
      have hs' : bcHom (IF.data α).QW (((e t : ↥(GSpin (IF.data α).QW)) :
          (CliffordAlgebra (IF.data α).QW)ˣ) : CliffordAlgebra (IF.data α).QW) =
          TorusTransfer.psiA (IF.twist α).φ g (bcHom d.QW (((t : ↥(GSpin d.QW)) :
            (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) := by
        have := congrArg Units.val (he t)
        rwa [TorusTransfer.coe_psiU] at this
      refine ⟨⟨TorusTransfer.isSS_of_psiA _ _ hs' ht.1, ?_, ?_⟩, hT'⟩
      · rw [hT']; exact hy.2.1
      · rw [hT']; exact hy.2.2
    · rintro ⟨hst, hT2⟩
      have hg' := TorusTransfer.mem_GSpin_symm (φ := (IF.twist α).φ) (Q₁ := d.QW) hg
      have hx' := TorusTransfer.psiU_symm_bcUnits hyc
      have ht' : TorusTransfer.psiU (IF.twist α).φ.symm (cliffUnits (IF.twist α).φ.symm g⁻¹)
          (bcUnits (IF.data α).QW (((e t : ↥(GSpin (IF.data α).QW)) : (CliffordAlgebra _)ˣ))) =
          bcUnits d.QW ((t : ↥(GSpin d.QW)) : (CliffordAlgebra d.QW)ˣ) := by
        rw [he t, TorusTransfer.psiU_symm_psiU]
      have hT : d.torusOf t = d.torusOf x :=
        TorusTransfer.torusSub_eq_of_psiU hg' hx' ht'
          (fun z hz => hcomm ⟨z, hz⟩
            ((IF.data α).commute_bc_iff_of_torusOf_eq hy hst (e t).2 hT2 ⟨z, hz⟩))
          ((IF.data α).fixedSub_eq_of_torusOf_eq (e t).2 hT2)
      have ht'' : bcHom d.QW (((t : ↥(GSpin d.QW)) : (CliffordAlgebra d.QW)ˣ) :
          CliffordAlgebra d.QW) = TorusTransfer.psiA (IF.twist α).φ.symm
            (cliffUnits (IF.twist α).φ.symm g⁻¹) (bcHom (IF.data α).QW
              (((e t : ↥(GSpin (IF.data α).QW)) : (CliffordAlgebra (IF.data α).QW)ˣ) :
                CliffordAlgebra (IF.data α).QW)) := by
        have := congrArg Units.val ht'
        rw [TorusTransfer.coe_psiU] at this
        exact this.symm
      refine ⟨⟨TorusTransfer.isSS_of_psiA _ _ ht'' hst.1, ?_, ?_⟩, hT⟩
      · rw [hT]; exact hx.2.1
      · rw [hT]; exact hx.2.2
  have c6 : ∀ t : ↥(d.torusOf x), d.IsGammaElt t → d.torusOf t = d.torusOf x →
      d.StronglyStablyConjW (IF.twist α) t (e t) := fun t ht hT =>
    stronglyStablyConjW_of_torusOf_eq IF α x y hx hxy hg hconj hrat t (e t) (he t) ht hT
  have c7 : ∀ t : ↥(d.torusOf x), d.StablyConjG (IF.twist α) (d.diag t) ((IF.data α).diag (e t)) :=
    fun t => stablyConjG_diag_of_psiU (IF.twist α) hg t (e t) (he t)
  have he' : ∀ s : ↥((IF.data α).torusOf y), bcUnits d.QW
      (((e.symm s : ↥(d.torusOf x)) : ↥(GSpin d.QW)) : (CliffordAlgebra _)ˣ) =
        TorusTransfer.psiU (IF.twist α).φ.symm (cliffUnits (IF.twist α).φ.symm g⁻¹)
          (bcUnits (IF.data α).QW ((s : ↥(GSpin (IF.data α).QW)) : (CliffordAlgebra _)ˣ)) := by
    intro s
    conv_rhs => rw [← e.apply_symm_apply s, he]
    rw [TorusTransfer.psiU_symm_psiU]
  have c1 : Continuous e := TorusTransfer.continuous_of_bcUnits_eq e.toMonoidHom he
  have c2 : Continuous e.symm := TorusTransfer.continuous_of_bcUnits_eq e.symm.toMonoidHom he'
  refine ⟨e, c1, c2, fun c => TorusTransfer.transportEquiv_scalar hg hrat hconj c _,
    fun t ht => ?_, c5, c6, c7⟩
  apply TorusTransfer.bcUnits_GSpin_injective
  show bcUnits _ _ = bcUnits _ _
  rw [he, ht]
  exact hconj

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
uses `H¹(F, T_x)`.  Proved: `y` is sent to the class of `σ ↦ ψ⁻¹ ∘ σψ` for any `ψ = P(g) ∘ φ_α` with
`C(ψ) x = y` and cocycle in `S_x` (`GGPData.IsStableIso`; it exists by the case analysis on
`dim W'_x` and Witt cancellation, `GGPData.exists_isStableIso`); the class is well defined and
injective on `GSpin(W_α)(F)`-classes (`IsStableIso.mk_eq`, `IsStableIso.exists_conj_of_mk_eq`), and
every class over `α` arises, since the cocycle lifts to `T_x(F̄)`, which is central in the
centralizer of `x` in `GSpin(W)(F̄)` (`GGPData.exists_of_twistIdx`). -/
theorem n_alpha_eq_card_twistIdx (IF : InnerFormSystem d) (α : IF.Idx) (x : ↥(GSpin d.QW))
    (hx : d.IsGammaElt x) :
    n_alpha IF α x = Nat.card {β : H1 (d.torusBarFbar x) // TwistIdx IF x β α} := by
  classical
  -- the class of `y`, from any witness (`exists_isStableIso`)
  have hex : ∀ y : stableFiber IF α x, ∃ ψ, d.IsStableIso (IF.twist α) x (y : _) ψ :=
    fun y => d.exists_isStableIso (IF.twist α) hx y.2.2
  let cls : stableFiber IF α x → H1 (d.torusBarFbar x) := fun y =>
    H1.mk (Classical.choose_spec (hex y)).cocycle
  have hcls : ∀ y, TwistIdx IF x (cls y) α := fun y =>
    (Classical.choose_spec (hex y)).twistIdx IF
  have hwd : ∀ y y', stableFiberConj IF α x y y' → cls y = cls y' := by
    rintro y y' ⟨g, hg⟩
    exact GGPData.IsStableIso.mk_eq hx g hg _ _
  let Φ : Quot (stableFiberConj IF α x) → {β : H1 (d.torusBarFbar x) // TwistIdx IF x β α} :=
    Quot.lift (fun y => ⟨cls y, hcls y⟩) fun y y' h => Subtype.ext (hwd y y' h)
  have hinj : Function.Injective Φ := by
    rintro ⟨y⟩ ⟨y'⟩ h
    have h' : cls y = cls y' := congrArg Subtype.val h
    obtain ⟨g, hg⟩ := GGPData.IsStableIso.exists_conj_of_mk_eq _ _ h'
    exact Quot.sound ⟨g, hg⟩
  have hsurj : Function.Surjective Φ := by
    rintro ⟨β, hβ⟩
    obtain ⟨y, hyΓ, hyst, ψ, h, hβ'⟩ := GGPData.exists_of_twistIdx IF hx hβ
    refine ⟨Quot.mk _ ⟨y, hyΓ, hyst⟩, Subtype.ext ?_⟩
    change cls ⟨y, hyΓ, hyst⟩ = β
    rw [← hβ']
    exact GGPData.IsStableIso.mk_eq hx 1 (by simp) _ _
  exact Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)

/-- On `T_{x,♮} = {t ∈ T_x ∩ Γ(G,H) : T_t = T_x}` (Thesis §6.5) the tori agree over `F̄`:
`torusFbar t = torusFbar x` as subgroups of `GSpin(W)(F̄)` (`fixedSub_eq_of_torusOf_eq`,
`commute_bc_iff_of_torusOf_eq`). -/
theorem torusFbar_eq_of_torusOf_eq {x t : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    (ht : d.IsGammaElt t) (htx : t ∈ d.torusOf x) (hT : d.torusOf t = d.torusOf x) :
    d.torusFbar t = d.torusFbar x := by
  have hW := d.fixedSub_eq_of_torusOf_eq htx hT
  ext z
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [hW]
  refine and_congr_left' ?_
  have h := d.commute_bc_iff_of_torusOf_eq hx ht htx hT z
  constructor
  · intro hz
    exact congrArg Subtype.val (h.mp (Subtype.ext hz)).eq
  · intro hz
    exact congrArg Subtype.val (h.mpr (Subtype.ext hz)).eq

/-- **`n_α` is constant on `T_{x,♮}`** (Thesis §6.7): for `x ∈ Γ(G,H)` and `t ∈ T_x` with
`t ∈ Γ(G,H)` and `T_t = T_x`, `n_α(t) = n_α(x)` (both are `|q_x⁻¹(α)|`, `n_alpha_eq_card_twistIdx`, and
`S_t = S_x`). -/
theorem n_alpha_eq_of_torusOf_eq (IF : InnerFormSystem d) (α : IF.Idx) {x t : ↥(GSpin d.QW)}
    (hx : d.IsGammaElt x) (ht : d.IsGammaElt t) (htx : t ∈ d.torusOf x)
    (hT : d.torusOf t = d.torusOf x) :
    n_alpha IF α t = n_alpha IF α x := by
  have hS : d.torusBarFbar t = d.torusBarFbar x := by
    unfold GGPData.torusBarFbar
    rw [torusFbar_eq_of_torusOf_eq hx ht htx hT]
  have key : ∀ S S' : Subgroup (GL (Fin d.m) (AlgebraicClosure F)), S = S' →
      Nat.card {β : H1 S // ∃ a : GalCocycle S, H1.mk a = β ∧ IsTwistBy d.QW (IF.twist α).Q' a.toFun} =
        Nat.card {β : H1 S' // ∃ a : GalCocycle S', H1.mk a = β ∧
          IsTwistBy d.QW (IF.twist α).Q' a.toFun} := by
    rintro S _ rfl; rfl
  rw [n_alpha_eq_card_twistIdx IF α t ht, n_alpha_eq_card_twistIdx IF α x hx]
  exact key _ _ hS

/-- **`q_x` is a function** `H¹(F, S_x) → IF.Idx` (own work; standard descent).  Existence: by
Hilbert 90 for `GL_m` (Serre, *Local Fields*, X §1 Prop. 3) a cocycle `a` with values in
`S_x(F̄) ⊆ SO(W)(F̄)` is `a_σ = M⁻¹ σ(M)`; then `v ↦ Q_{F̄}(M⁻¹ v)` is an `F`-valued nondegenerate
form on `F^m` of the discriminant of `W` (`det a_σ = 1`), isometric to a unique `W_α`
(`IF.classify`).  Uniqueness: if `φ, φ'` have cohomologous cocycles `a`, `a' = c⁻¹ a σ(c)`
(`c ∈ S_x(F̄)`), then `φ' c⁻¹ φ⁻¹ : W_{α,F̄} ≃ W_{α',F̄}` is Galois-invariant, hence defined over
`F`, so `α = α'` (`IF.classify`).  Proved (`GGP/TwistDescent.lean`, `GGP/Hilbert90.lean`; no
cited input). -/
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

/-- **The moved space `W''_x = (W'_x)^⊥` of `x ∈ Γ(G,H)`** (own work, elementary): it is not a
line, and if it is a plane it is anisotropic.  Route: `W''_x` is `P(x)`-stable with
`W''_x ∩ W'_x = 0`; on a line `P(x)` would be `−1`, so `det P(x) = −1`, contradicting `det_specP`;
on a hyperbolic plane with hyperbolic pair `f, f'`, the isometries `f ↦ t f`, `f' ↦ t⁻¹ f'`,
`1` on `W'_x` (`t ∈ F^×`) lift to `GSpin(W)(F)` (units of `C⁺(W''_x)`, which commute with `x` since
`x ∈ F^× · C⁺(W''_x)` (`ker_specP`) and `C⁺` of a plane is commutative), hence lie in
`T_x(F)`, and their images under `P` are unbounded, contradicting compactness of `T_x(F)/A(F)`
(`IsGammaElt`).  Proved in `GGP/MovedAniso` (`finrank_orthogonal_fixedSub_ne_one`,
`anisotropic_orthogonal_fixedSub_of_isGammaElt`; the lifts `ι(f+f') ι(f+s f')` commute with `x` up to
a scalar `c` with `c^N = 1`, `N = dim C(W)`, by `detChar`, so their `N`-th powers lie in `T_x(F)`). -/
theorem orthogonal_fixedSub_of_isGammaElt (x : ↥(GSpin d.QW)) (hx : d.IsGammaElt x) :
    finrank F ↥((bform d.QW).orthogonal (fixedSub x)) ≠ 1 ∧
      (finrank F ↥((bform d.QW).orthogonal (fixedSub x)) = 2 →
        (d.QW.comp ((bform d.QW).orthogonal (fixedSub x)).subtype).Anisotropic) :=
  ⟨finrank_orthogonal_fixedSub_ne_one d.nondeg x
    (isCompl_fixedSub_orthogonal d.nondeg x (fixedSub_inf_movedSub_of_isSS x hx.1)),
    anisotropic_orthogonal_fixedSub_of_isGammaElt d x hx⟩

/-- **Statement (S)** (Thesis Prop 6.5.1(iv), first half): for `x ∈ Γ(G,H)` not central, some
`β ∈ H¹(F, S_x)` has `W_{q_x(β)} ≇ W`.  Proof: `W''_x ≠ 0` (else `P(x) = 1` and `x` is a scalar,
`ker_specP`), so by `orthogonal_fixedSub_of_isGammaElt` it has dimension `≥ 3` or is an anisotropic
plane, and `exists_twistIdx_not_isometric_of_moved` applies (Kottwitz 1986, Lemma 10.2, for the
anisotropic maximal torus `S_x` of `SO(W''_x)`). -/
theorem exists_twistIdx_not_isometric_of_isGammaElt (IF : InnerFormSystem d) (x : ↥(GSpin d.QW))
    (hx : d.IsGammaElt x) (hc : ¬ IsCentralW d x) :
    ∃ β α, TwistIdx IF x β α ∧ ¬ Nonempty (d.QW.IsometryEquiv (IF.twist α).Q') := by
  obtain ⟨h1, h2⟩ := orthogonal_fixedSub_of_isGammaElt x hx
  refine exists_twistIdx_not_isometric_of_moved IF hx ?_
  have h0 : finrank F ↥((bform d.QW).orthogonal (fixedSub x)) ≠ 0 := by
    intro h0
    apply hc
    have hbot := Submodule.finrank_eq_zero.mp h0
    have hdisj := fixedSub_inf_movedSub_of_isSS x hx.1
    have hcW := isCompl_fixedSub_orthogonal d.nondeg x hdisj
    rw [hbot] at hcW
    have htop : fixedSub x = ⊤ := by
      have := hcW.sup_eq_top
      rwa [sup_bot_eq] at this
    have hP1 : specP d.QW x = 1 := by
      refine LinearEquiv.ext fun v => ?_
      have hv : v ∈ fixedSub x := htop ▸ Submodule.mem_top
      exact (d.mem_fixedSub_iff).mp hv
    have hker : x ∈ (specP d.QW).ker := hP1
    rw [ker_specP d.nondeg] at hker
    exact hker
  rcases Nat.lt_or_ge (finrank F ↥((bform d.QW).orthogonal (fixedSub x))) 3 with hlt | hge
  · exact Or.inr ⟨by omega, h2 (by omega)⟩
  · exact Or.inl hge

/-- **Some class of `H¹(F, S_x)` twists `W` into a non-isometric form** (statement (S) for
`U = W''_x`; Thesis Prop 6.5.1(iv), first half).  For `G` quasi-split and `x ∈ Γ(G,H)` not central,
some `β ∈ H¹(F, S_x)` has `W_{q_x(β)} ≇ W` (`exists_twistIdx_not_isometric_of_isGammaElt`; `hqs` is
not needed, and is kept for the callers). -/
theorem exists_twistIdx_not_isometric (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (x : ↥(GSpin d.QW)) (hx : d.IsGammaElt x) (hc : ¬ IsCentralW d x) :
    ∃ β α, TwistIdx IF x β α ∧ ¬ Nonempty (d.QW.IsometryEquiv (IF.twist α).Q') := by
  have _ := hqs
  exact exists_twistIdx_not_isometric_of_isGammaElt IF x hx hc

/-- **Surjectivity of the Kottwitz sign on `H¹(F, S_x)`** (Thesis Prop 6.5.1(iv)): for `G`
quasi-split and `x ∈ Γ(G,H)` not central, some `β ∈ H¹(F, S_x)` has `e(G_{q_x(β)}) = -1`.
Proved from `exists_twistIdx_not_isometric` and the sign computation
`WittParity.kottwitzSign_eq_neg_one` (`e(G_α) = −1` whenever `W_α ≇ W`: Witt indices of the two
`p`-adic forms of the same dimension and discriminant). -/
theorem exists_twistIdx_kottwitzSign_neg (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (x : ↥(GSpin d.QW)) (hx : d.IsGammaElt x) (hc : ¬ IsCentralW d x) :
    ∃ β α, TwistIdx IF x β α ∧ kottwitzSign d (IF.twist α) = -1 := by
  obtain ⟨β, α, h, hne⟩ := exists_twistIdx_not_isometric hqs IF x hx hc
  exact ⟨β, α, h, WittParity.kottwitzSign_eq_neg_one d (IF.twist α) hne⟩

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
  exact TwistDescent.isTwistBy_refl d.QW

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

/-- The integrand of `m_{geom,s}` vanishes off `T_♮` (by definition). -/
theorem gammaIntegrand_of_not_mem {d : GGPData F} {θ : ↥d.G → ℂ} {T : Subgroup ↥(GSpin d.QW)}
    {s : ℝ} {t : ↥(GSpin d.QW)} (h : ¬ (d.IsGammaElt t ∧ d.torusOf t = T)) :
    gammaIntegrand ψ d θ T s t = 0 :=
  ite_eq_right h

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


/-- **`O_x` is regular at quasi-split points of `Γ(G,H)`**: for `x ∈ Γ(G,H)` with `G'_x`
quasi-split, Luo's orbit exists (`GGPData.exists_orbitSpec_of_quasiSplit`), so `orbitChoice d x`
is a regular nilpotent orbit of `𝔤_x`. -/
theorem orbitChoice_mem_nilReg_of_qd (d : GGPData F) (x : ↥(GSpin d.QW)) (hx : d.IsGammaElt x)
    (hq : IsQdAt d x) :
    orbitChoice d x ∈ NilReg (grpCentralizer d.G (d.diag x : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag x : d.ambientˣ)) : d.ambient)) :=
  orbitChoice_mem_nilReg_of_exists d x
    (d.exists_orbitSpec_of_quasiSplit x hx.1 (movedPartAbelian_of_isGammaElt d x hx) hq.1 hq.2)

/-- **Strong stable conjugacy preserves `IsQdAt`**: for `x ∈ Γ(G,H)` and `y` strongly stably
conjugate to `x`, `W'_x ≅ W'_y` over `F` (a witness `ψ` of `GGPData.IsStableIso` has cocycle trivial on
`W'_x ⊗ F̄`, so it restricts to a rational isometry, `exists_isometryEquiv_fixedSub`), hence also
`V'_x ≅ V'_y`. -/
theorem isQdAt_iff_of_stronglyStablyConj (IF : InnerFormSystem d) {α : IF.Idx}
    {x : ↥(GSpin d.QW)} {y : ↥(GSpin (IF.data α).QW)} (hx : d.IsGammaElt x)
    (hxy : d.StronglyStablyConjW (IF.twist α) x y) :
    IsQdAt d x ↔ IsQdAt (IF.data α) y := by
  obtain ⟨φ, hφ⟩ := d.exists_isStableIso (IF.twist α) hx hxy
  obtain ⟨θ, -⟩ := exists_isometryEquiv_fixedSub φ hφ.1 (fun σ _ hw => hφ.fix σ hw)
  have θV : (d.QVfix x).IsometryEquiv ((IF.data α).QVfix y) :=
    θ.prod (QuadraticMap.IsometryEquiv.refl d.QZ)
  exact ⟨fun h => ⟨QuadClassify.isQuasiSplitQF_of_isometryEquiv θ h.1,
      QuadClassify.isQuasiSplitQF_of_isometryEquiv θV h.2⟩,
    fun h => ⟨QuadClassify.isQuasiSplitQF_of_isometryEquiv θ.symm h.1,
      QuadClassify.isQuasiSplitQF_of_isometryEquiv θV.symm h.2⟩⟩

/-- `A_{G,H}(F)`-invariance of the integrand of `m_{geom,s}` along a torus `T`, for `θ ∈ QCfin`
(`gammaIntegrand_scalar_mul_of_mem_QCfin`). -/
theorem gammaIntegrand_mul_mem_scalarsIn {d' : GGPData F} {θ : ↥d'.G → ℂ} (hθ : θ ∈ QCfin d')
    (T : Subgroup ↥(GSpin d'.QW)) (s : ℝ) (t a : ↥T) (ha : a ∈ d'.scalarsIn T) :
    gammaIntegrand ψ d' θ T s ((t * a : ↥T) : ↥(GSpin d'.QW)) =
      gammaIntegrand ψ d' θ T s (t : ↥(GSpin d'.QW)) := by
  obtain ⟨c, hc⟩ : ∃ c, scalarGSpin d'.QW c = (a : ↥(GSpin d'.QW)) :=
    Subgroup.mem_subgroupOf.mp ha
  have : ((t * a : ↥T) : ↥(GSpin d'.QW)) = scalarGSpin d'.QW c * t := by
    rw [Subgroup.coe_mul, ← hc]
    exact ((scalarGSpin_commute _ c (t : ↥(GSpin d'.QW))).eq).symm
  rw [this, gammaIntegrand_scalar_mul_of_mem_QCfin ψ d' hθ]

/-- **(R1) Transport of the torus integrals along a torus transfer** (Thesis (6.7.2)–(6.7.5)): for
`x ∈ Γ(G,H)`, `y ∈ Γ(G_α,H_α)` and a `TorusTransfer` `e : T_x ≃ T_y`,
`∫_{T_y/A} D^{1/2} c_{θ_α} Δ^{s-1/2} = e(G_α) ∫_{T_x/A} D^{1/2} c_{θ_1} Δ^{s-1/2}`.
Pointwise on `T_x`: off `T_{x,♮}` both integrands vanish (`TorusTransfer`'s `T_♮` clause); at
non-quasi-split points both vanish (`isQdAt_iff_of_stronglyStablyConj`,
`gammaIntegrand_eq_zero_of_not_qd`); at quasi-split points `O_t`, `O_{e t}` are regular
(`orbitChoice_mem_nilReg_of_qd`), so `hgerm` applies, and `D^G`, `Δ` agree.  Then
`torusIntegral_eq_of_mulEquiv` (the integrand on `T_y` is `A(F)`-invariant,
`gammaIntegrand_scalar_mul_of_mem_QCfin`). -/
theorem torusIntegral_eq_of_torusTransfer {IF : InnerFormSystem d} (P : TemperedPacketFamily d IF)
    (hgerm : PacketGermTransfer ψ P) {α : IF.Idx} {x : ↥(GSpin d.QW)}
    {y : ↥(GSpin (IF.data α).QW)} (hx : d.IsGammaElt x) (hy : (IF.data α).IsGammaElt y)
    (htr : TorusTransfer IF α x y) (s : ℝ) :
    torusIntegral ψ (IF.data α) (P.packetChar α) ((IF.data α).torusOf y) s =
      (kottwitzSign d (IF.twist α) : ℂ) * torusIntegral ψ d P.baseChar (d.torusOf x) s := by
  obtain ⟨e, hc, hcs, hsc, -, hreg, hst, hDΔ⟩ := htr
  have := hx.2.2
  have := hy.2.2
  let E : ↥(d.torusOf x) ≃ₜ* ↥((IF.data α).torusOf y) :=
    { e with continuous_toFun := hc, continuous_invFun := hcs }
  have he : (d.scalarsIn (d.torusOf x)).map E.toMulEquiv.toMonoidHom =
      (IF.data α).scalarsIn ((IF.data α).torusOf y) := by
    ext t'
    simp only [Subgroup.mem_map, GGPData.scalarsIn, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
    constructor
    · rintro ⟨t, ⟨c, hct⟩, rfl⟩
      refine ⟨c, ?_⟩
      have : t = ⟨scalarGSpin d.QW c, d.scalar_mem_torusOf x c⟩ := Subtype.ext hct.symm
      subst this
      exact (hsc c).symm
    · rintro ⟨c, hct⟩
      refine ⟨⟨scalarGSpin d.QW c, d.scalar_mem_torusOf x c⟩, ⟨c, rfl⟩, Subtype.ext ?_⟩
      exact (hsc c).trans hct
  refine GGPData.torusIntegral_eq_of_mulEquiv ψ E he _ (fun t => ?_) (fun t a ha => ?_)
  · change gammaIntegrand ψ (IF.data α) (P.packetChar α) ((IF.data α).torusOf y) s
        ((e t : ↥((IF.data α).torusOf y)) : ↥(GSpin (IF.data α).QW)) = _
    by_cases hT : d.IsGammaElt t ∧ d.torusOf t = d.torusOf x
    · have hT' := (hreg t).mp hT
      have hxy := hst t hT.1 hT.2
      by_cases hq : IsQdAt d t
      · have hq' := (isQdAt_iff_of_stronglyStablyConj IF hT.1 hxy).mp hq
        unfold gammaIntegrand
        rw [ite_eq_left hT, ite_eq_left hT', (hDΔ t).1, (hDΔ t).2,
          hgerm α t (e t) (isSS_diag_of_isGammaElt d hT.1)
            (isSS_diag_of_isGammaElt (IF.data α) hT'.1) hxy _
            (orbitChoice_mem_nilReg_of_qd d t hT.1 hq) _
            (orbitChoice_mem_nilReg_of_qd (IF.data α) (e t) hT'.1 hq')]
        ring
      · have hq' : ¬ IsQdAt (IF.data α) (e t) :=
          fun h => hq ((isQdAt_iff_of_stronglyStablyConj IF hT.1 hxy).mpr h)
        rw [gammaIntegrand_eq_zero_of_not_qd ψ _ _ _ _ _ hq',
          gammaIntegrand_eq_zero_of_not_qd ψ _ _ _ _ _ hq, mul_zero]
    · have hT' : ¬ ((IF.data α).IsGammaElt (e t) ∧
          (IF.data α).torusOf (e t) = (IF.data α).torusOf y) := fun h => hT ((hreg t).mpr h)
      rw [gammaIntegrand_of_not_mem ψ hT, gammaIntegrand_of_not_mem ψ hT', mul_zero]
  · exact gammaIntegrand_mul_mem_scalarsIn ψ (P.packetChar_mem_QCfin α) _ s t a ha

/-- `IsQdAt` is constant on `T_{x,♮}` (`W'_t = W'_x`, `fixedSub_eq_of_torusOf_eq`). -/
theorem isQdAt_iff_of_torusOf_eq {x t : ↥(GSpin d.QW)} (ht : t ∈ d.torusOf x)
    (hT : d.torusOf t = d.torusOf x) : IsQdAt d t ↔ IsQdAt d x := by
  unfold IsQdAt GGPData.QVfix GGPData.QWfix
  rw [d.fixedSub_eq_of_torusOf_eq ht hT]

/-- **Non-quasi-split tori contribute `0`**: for `y ∈ Γ(G,H)` with `G'_y` not quasi-split the
integrand of `m_{geom,s}` vanishes on `T_y` (on `T_{y,♮}` every point has `G'_t ≅ G'_y`,
`isQdAt_iff_of_torusOf_eq`, and `gammaIntegrand_eq_zero_of_not_qd`). -/
theorem torusIntegral_eq_zero_of_not_qd (d' : GGPData F) (θ : ↥d'.G → ℂ) {y : ↥(GSpin d'.QW)}
    (hq : ¬ IsQdAt d' y) (s : ℝ) : torusIntegral ψ d' θ (d'.torusOf y) s = 0 := by
  unfold torusIntegral
  have h0 : (fun q : d'.TorusQuot (d'.torusOf y) =>
      gammaIntegrand ψ d' θ (d'.torusOf y) s ((Quotient.out q : ↥(d'.torusOf y)) :
        ↥(GSpin d'.QW))) = fun _ => 0 := by
    funext q
    set t : ↥(GSpin d'.QW) := ((Quotient.out q : ↥(d'.torusOf y)) : ↥(GSpin d'.QW))
    by_cases hT : d'.IsGammaElt t ∧ d'.torusOf t = d'.torusOf y
    · exact gammaIntegrand_eq_zero_of_not_qd ψ d' θ _ s t
        (fun h => hq ((isQdAt_iff_of_torusOf_eq (Quotient.out q).2 hT.2).mp h))
    · exact gammaIntegrand_of_not_mem ψ hT
  rw [h0, integral_zero]

/-- **The stable weight comes out of the torus integral** (gating lemma (C)): `Σ_α e(G_α)n_α(t)/n_1(t)`
is constant on `T_{x,♮}` (`n_alpha_eq_of_torusOf_eq`), and the integrand vanishes off `T_{x,♮}`. -/
theorem integral_stableWeight_mul (IF : InnerFormSystem d) (θ : ↥d.G → ℂ) {x : ↥(GSpin d.QW)}
    (hx : d.IsGammaElt x) {T : Subgroup ↥(GSpin d.QW)} (hT : d.torusOf x = T) (s : ℝ) :
    (letI : MeasurableSpace (d.TorusQuot T) := borel _
     haveI : BorelSpace (d.TorusQuot T) := ⟨rfl⟩
     ∫ q, stableWeight IF ((Quotient.out q : ↥T) : ↥(GSpin d.QW)) *
        gammaIntegrand ψ d θ T s ((Quotient.out q : ↥T) : ↥(GSpin d.QW))
       ∂(probHaar (d.TorusQuot T))) = stableWeight IF x * torusIntegral ψ d θ T s := by
  subst hT
  unfold torusIntegral
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  set t : ↥(GSpin d.QW) := ((Quotient.out q : ↥(d.torusOf x)) : ↥(GSpin d.QW))
  by_cases hT : d.IsGammaElt t ∧ d.torusOf t = d.torusOf x
  · have hn : ∀ α, n_alpha IF α t = n_alpha IF α x := fun α =>
      n_alpha_eq_of_torusOf_eq IF α hx hT.1 (Quotient.out q).2 hT.2
    change (signedCount IF t : ℂ) / (n_alpha IF IF.base t : ℂ) * _ =
      (signedCount IF x : ℂ) / (n_alpha IF IF.base x : ℂ) * _
    simp only [signedCount, hn]
  · have h0 : gammaIntegrand ψ d θ (d.torusOf x) s t = 0 := gammaIntegrand_of_not_mem ψ hT
    change _ * gammaIntegrand ψ d θ (d.torusOf x) s t = _ * gammaIntegrand ψ d θ (d.torusOf x) s t
    rw [h0, mul_zero, mul_zero]

open Classical in
/-- `F_α(c) = f(T_x)` for some `x ∈ Γ(G,H)` strongly stably conjugate to the generator of the
torus class `c` of `Γ(G_α,H_α)`, and `0` if there is none. -/
noncomputable def stableLift (IF : InnerFormSystem d) (α : IF.Idx)
    (f : Subgroup ↥(GSpin d.QW) → ℂ) (c : GammaClass (IF.data α)) : ℂ :=
  if h : ∃ x : ↥(GSpin d.QW), d.IsGammaElt x ∧
      d.StronglyStablyConjW (IF.twist α) x (gammaGen (IF.data α) c) then
    f (d.torusOf h.choose) else 0

/-- **The torus-class count (R2)** (own work; the regrouping step of Thesis (6.7.2)–(6.7.5)): for
a function `f` of the tori of `Γ(G,H)` that is constant on tori `T_x`, `T_{x'}` with `x`, `x'`
strongly stably conjugate to a common `y` (and `0` on non-quasi-split tori),
`Σ_{[T'] ∈ Γ(G_α,H_α)/conj} |W(T')|⁻¹ F_α(T') = Σ_{[T] ∈ Γ(G,H)/conj} |W(T)|⁻¹ (n_α(x_T)/n_1(x_T)) f(T)`.
Regrouping both sides by stable classes, this says that `N_α = Σ |W(T')|⁻¹` over the classes of
`G_α` stably conjugate to `T_x` is proportional to `n_α(x)` (with the same constant for every `α`).
Expected proof: `n_α(x) = |q_x⁻¹(α)|` (`n_alpha_eq_card_twistIdx`), and the rational classes of tori
over `α` are the orbits of `(N_x/S_x)(F)` on `q_x⁻¹(α) ⊆ H¹(F, S_x)`, with stabilizers `W(T')`
(orbit–stabilizer).  Checks: at `α = 1` both sides agree by the invariance of `f`; for central `x`,
`n_α(x) = [α = 1]`.  (`n_1(x) ≥ 1`, `x` itself being strongly stably conjugate to its image in `G_1`;
`hqs` and `hf0` are not needed for the identity.) -/
theorem torusClass_count (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d) (α : IF.Idx)
    (f : Subgroup ↥(GSpin d.QW) → ℂ)
    (hf : ∀ (β : IF.Idx) (y : ↥(GSpin (IF.data β).QW)) (x x' : ↥(GSpin d.QW)),
      (IF.data β).IsGammaElt y → d.IsGammaElt x → d.IsGammaElt x' →
      d.StronglyStablyConjW (IF.twist β) x y → d.StronglyStablyConjW (IF.twist β) x' y →
      f (d.torusOf x) = f (d.torusOf x'))
    (hf0 : ∀ x : ↥(GSpin d.QW), d.IsGammaElt x → ¬ IsQdAt d x → f (d.torusOf x) = 0) :
    ∑' c : GammaClass (IF.data α), ((weylCard (IF.data α) c : ℂ))⁻¹ * stableLift IF α f c =
      ∑' c : GammaClass d, ((weylCard d c : ℂ))⁻¹ *
        ((n_alpha IF α (gammaGen d c) : ℂ) / (n_alpha IF IF.base (gammaGen d c) : ℂ)) *
          f (Quot.out c).1 :=
  sorry

/-- **The stable rearrangement at `s > 0`** (own work; Thesis (6.7.2)–(6.7.5) before the limit):
for `s > 0`,
`Σ_α m_{geom,s}(θ_α) = ∫_{Γ(G,H)} (Σ_α e(G_α)n_α(x)/n_1(x)) c_{θ_1}(x) D^G(x)^{1/2} Δ(x)^{s-1/2} dx`.
Proof, torus class by torus class:
* a torus `T_y` of `Γ(G_α,H_α)` with `G'_y` not quasi-split contributes `0`
  (`torusIntegral_eq_zero_of_not_qd`); otherwise some `x ∈ Γ(G,H)` is strongly stably conjugate to
  `y` (`hi`), and `∫_{T_y/A} = e(G_α) ∫_{T_x/A}` (`torusIntegral_eq_of_torusTransfer`: `hii`
  identifies the probability Haar measures, `D^G` and `Δ`; `hgerm` the germs);
* regrouping the torus classes of all `G_α` over those of `G` is the torus-class count
  `torusClass_count`;
* `Σ_α e(G_α)n_α/n_1` is constant on `T_{x,♮}` and comes out of the torus integral
  (`integral_stableWeight_mul`).
(The identity holds for every `s`; `s > 0` is where the integrals converge, Thesis Prop. 12.1.1.) -/
theorem stable_rearrangement_pos (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (P : TemperedPacketFamily d IF)
    (hgerm : PacketGermTransfer ψ P)
    (hi : ∀ (α : IF.Idx) (y : ↥(GSpin (IF.data α).QW)), (IF.data α).IsGammaElt y →
      IsQdAt (IF.data α) y → ∃ x : ↥(GSpin d.QW), d.IsGammaElt x ∧
        d.StronglyStablyConjW (IF.twist α) x y)
    (hii : ∀ (α : IF.Idx) (x : ↥(GSpin d.QW)) (y : ↥(GSpin (IF.data α).QW)), d.IsGammaElt x →
      (IF.data α).IsGammaElt y → d.StronglyStablyConjW (IF.twist α) x y →
        TorusTransfer IF α x y)
    {s : ℝ} (hs : 0 < s) :
    ∑ᶠ α : IF.Idx, mGeomS ψ (IF.data α) (P.packetChar α) s = mGeomStabS ψ IF P.baseChar s := by
  classical
  have _ := hs
  have := finite_gammaClass d
  let _ : Fintype (GammaClass d) := Fintype.ofFinite _
  have := IF.finite_idx
  let _ : Fintype IF.Idx := Fintype.ofFinite _
  let f : Subgroup ↥(GSpin d.QW) → ℂ := fun T => torusIntegral ψ d P.baseChar T s
  have he0 : ∀ β : IF.Idx, (kottwitzSign d (IF.twist β) : ℂ) ≠ 0 := fun β => by
    rcases kottwitzSign_eq_one_or d (IF.twist β) with h | h <;> simp [h]
  -- each inner form: transport the quasi-split tori to `G`
  have h1 : ∀ α, mGeomS ψ (IF.data α) (P.packetChar α) s = (kottwitzSign d (IF.twist α) : ℂ) *
      ∑' c : GammaClass (IF.data α), ((weylCard (IF.data α) c : ℂ))⁻¹ * stableLift IF α f c := by
    intro α
    unfold mGeomS
    rw [← tsum_mul_left]
    refine tsum_congr fun c => ?_
    obtain ⟨hy, hyT⟩ := gammaGen_spec (IF.data α) c
    rw [← hyT]
    unfold stableLift
    split_ifs with h
    · obtain ⟨hx, hxy⟩ := h.choose_spec
      rw [torusIntegral_eq_of_torusTransfer ψ P hgerm hx hy (hii α _ _ hx hy hxy) s]
      ring
    · have hq : ¬ IsQdAt (IF.data α) (gammaGen (IF.data α) c) := fun hq => h (hi α _ hy hq)
      rw [torusIntegral_eq_zero_of_not_qd ψ _ _ hq]
      ring
  have hf : ∀ (β : IF.Idx) (y : ↥(GSpin (IF.data β).QW)) (x x' : ↥(GSpin d.QW)),
      (IF.data β).IsGammaElt y → d.IsGammaElt x → d.IsGammaElt x' →
      d.StronglyStablyConjW (IF.twist β) x y → d.StronglyStablyConjW (IF.twist β) x' y →
      f (d.torusOf x) = f (d.torusOf x') := by
    intro β y x x' hy hx hx' hxy hx'y
    have a := torusIntegral_eq_of_torusTransfer ψ P hgerm hx hy (hii β x y hx hy hxy) s
    have b := torusIntegral_eq_of_torusTransfer ψ P hgerm hx' hy (hii β x' y hx' hy hx'y) s
    exact mul_left_cancel₀ (he0 β) (a.symm.trans b)
  have hf0 : ∀ x : ↥(GSpin d.QW), d.IsGammaElt x → ¬ IsQdAt d x → f (d.torusOf x) = 0 :=
    fun x _ hq => torusIntegral_eq_zero_of_not_qd ψ d _ hq s
  have hL : ∀ α, mGeomS ψ (IF.data α) (P.packetChar α) s =
      (kottwitzSign d (IF.twist α) : ℂ) * ∑' c : GammaClass d, ((weylCard d c : ℂ))⁻¹ *
        ((n_alpha IF α (gammaGen d c) : ℂ) / (n_alpha IF IF.base (gammaGen d c) : ℂ)) *
          f (Quot.out c).1 := fun α => by
    rw [h1, torusClass_count hqs IF α f hf hf0]
  -- the stable side
  have hR : mGeomStabS ψ IF P.baseChar s = ∑' c : GammaClass d, ((weylCard d c : ℂ))⁻¹ *
      (stableWeight IF (gammaGen d c) * f (Quot.out c).1) := by
    unfold mGeomStabS
    refine tsum_congr fun c => ?_
    rw [integral_stableWeight_mul ψ IF P.baseChar (gammaGen_spec d c).1 (gammaGen_spec d c).2 s]
  rw [finsum_congr hL, hR, finsum_eq_sum_of_fintype]
  simp only [tsum_fintype]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [stableWeight, signedCount, finsum_eq_sum_of_fintype]
  push_cast
  rw [Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

/-- **Thesis (6.7.5)** (own work): summing (6.7.2) over the inner forms and
rearranging over strongly stable classes,
`Σ_α m_geom(θ_α) = lim_{s→0⁺} ∫_{Γ(G,H)} (Σ_α e(G_α)n_α(x)/n_1(x)) c_{θ_1}(x) D^G(x)^{1/2}
Δ(x)^{s-1/2} dx`.  Ingredients: STAB + BP (12.1.2) (`packet_germ_transfer`) make `c_{θ_α}`
constant on strongly stable classes; only quasi-split classes contribute
(`torusIntegral_eq_zero_of_not_qd`); Prop. 6.6.1(i),(ii) (`prop_12_5_1_i`, `prop_12_5_1_ii`)
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
      exact stable_rearrangement_pos ψ hqs IF P hgerm hi hii hs
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


/-- A regular orbit satisfying `OrbitSpec d 1` exists: `GGPData.exists_orbitSpec_of_quasiSplit` at
`x = 1` (`W'_1 = W`, `V'_1 = V`, `𝔤_1 = 𝔤`). -/
theorem exists_orbitSpec_one (d : GGPData F) (hqs : d.IsQuasiSplit) :
    ∃ O ∈ NilReg (grpCentralizer d.G (d.diag 1 : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag 1 : d.ambientˣ)) : d.ambient)),
      ∃ X ∈ nilOrbitSet O, OrbitSpec d 1 (X : d.ambient) :=
  have hq := isQdAt_of_fixedSub_eq_top d hqs 1 (fixedSub_one_eq_top d.QW)
  d.exists_orbitSpec_of_quasiSplit 1 (isSS_one_W d) (movedPartAbelian_one d) hq.1 hq.2

/-- **The orbit `O_1` is regular** for quasi-split `G` (own work, after Luo §7.1:
Luo's recipe applied to `(G'_1, H'_1) = (G, H)` selects a regular nilpotent orbit of `𝔤`, which
exists since `G` is quasi-split, `nilReg_nonempty_of_quasiSplit`).  Needed to apply Rodier's
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
