/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.ThetaFBP

/-!
# `J_M(x, f)` and `θ_f` for strongly cuspidal `f`: independence of `K`, invariance

For `f ∈ C_c^∞(G(F))` strongly cuspidal (Waldspurger's *très cuspidale*) and
`x ∈ M(F) ∩ G_reg(F)`, Waldspurger (Compos. Math. 146 (2010), Lemme 5.2, pp. 17–18) proves
* (i) `J_M(x, f)` does not depend on `K`;
* (ii) `J_M(x, ^y f) = J_M(x, f)` for every `y ∈ G(F)`;
((i) is Beuzart-Plessis, Astérisque 418, Lemma 5.2.1(ii), p. 109; his (iv),
`J_{y M y⁻¹}(y x y⁻¹, f) = J_M(x, f)`, follows from (i), (ii) by transport of structure).  Both
statements are made there for special maximal compact subgroups `K` in good position relative
to `M`.

**The proof** (Waldspurger, loc. cit.) has two independent parts, which are stated separately
here.
1. *A weight identity* (`exists_vM_sub_eq_sum_isCuspWeight`).  For two compact subgroups
   `K₁`, `K₂` and `y ∈ G(F)`, `v^{K₁}_M(g y) − v^{K₂}_M(g)` is a finite sum of functions of `g` that
   are left invariant under `M(F)` and under the unipotent radical `U_Q(F)` of a proper parabolic
   subgroup `Q ⊇ M` (`IsCuspWeight`).  Waldspurger obtains it from Arthur's product formula for
   `(G,M)`-families (§2.2 (2); Arthur, *The trace formula in invariant form*, Ann. of Math. 114
   (1981), (6.3) and Lemma 6.3): with `Y_P(g) = H^{K₁}_P(g y) − H^{K₂}_P(g)`,
   `v^{K₁}_M(g y) = Σ_{Q ∈ ℱ(M)} v^{K₂,Q}_M(g) u_Q(Y_Q(g))`, `u_G = 1`, and the terms with `Q ≠ G`
   are left `U_Q(F)`-invariant because `H_P(u g) = H_P(g)` for `u ∈ U_Q ⊆ U_P`, `P ⊆ Q`.
2. *Cuspidal vanishing* (`integral_isCuspWeight_eq_zero`).  For such a function `φ`,
   `∫_{G_x(F)\G(F)} f(g⁻¹ x g) φ(g) dg = 0`: by `G = Q K` and `dg = dl du dk`, the integral
   contains `∫_{U(F)} f(k⁻¹ u⁻¹ y u k) du` with `y = l⁻¹ x l ∈ L(F)` regular, which is a multiple
   of `∫_{U(F)} f(k⁻¹ y u k) du = 0`.

Both are `sorry` here.  (1) is the `(G,M)`-family theory, which is not built
(`GGP/WeightVM.lean` defines `v_M` directly as a volume); moreover it is printed for special `K`,
for which `(H_P(g))_P` is a *positive* `(G,M)`-orthogonal family and `v_M` is the volume of the
hull, whereas `GoodK` only carries `G = P K` and good position, and positivity is not proved for it
(see `GoodK`).  So the statement for `GoodK` is true given that positivity, which is open.  (2) is
our own step following Waldspurger's text (it needs the integration formula for `G = Q K` on
`G_x(F)\G(F)`).
From (1) and (2) the theorems below are proved, with no further input.

**Conjugation invariance of `θ_f`.**  Beuzart-Plessis' `θ_f(y x y⁻¹) = θ_f(x)` compares
`J_{M(x)}(x, f)` with `J_{y M(x) y⁻¹}(y x y⁻¹, f)`: by transport of structure the second is
`J_{M(x)}(x, ^{y⁻¹} f)` computed with `y⁻¹ K y`, and then (i), (ii) apply.  The transport step
needs the conjugate Levi datum (flags and bases moved by `y`) and its `GoodK`, which are not built;
what is proved here is the content of (i) and (ii): `thetaFBP_indep` and `thetaFBP_conj_fun`.

## Main definitions

* `ReducedLeviDatum.IsCuspWeight L φ`: `φ` continuous, left `M(F)`-invariant and left
  `U_Q(F)`-invariant for some proper parabolic `Q ⊇ M`.

## Main results

* `exists_vM_sub_eq_sum_isCuspWeight` (`sorry`): the weight identity (1).
* `integral_isCuspWeight_eq_zero` (`sorry`): the cuspidal vanishing (2).
* `weightedOrbitalIntegral_eq_of_isStronglyCuspidal`:
  `J^{K₁}_M(x, f(y · y⁻¹)) = J^{K₂}_M(x, f)`, from (1) and (2).
* `weightedOrbitalIntegral_indep`, `weightedOrbitalIntegral_conj_fun`: Waldspurger Lemme 5.2 (i),
  (ii).
* `thetaFBP_indep`, `thetaFBP_conj_fun`: the same for `thetaFBP`.
* `weightedOrbitalIntegral_indep_of_aG_eq_top`, `weightedOrbitalIntegral_conj_fun_of_aG_eq_top`:
  for `a_M = a_G` both hold for every `f`, with no `sorry`.
-/

noncomputable section

open MeasureTheory Topology Module

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable {d : GGPData F}

namespace ReducedLeviDatum

variable (L : d.ReducedLeviDatum)

/-! ## 2. The two ingredients of Waldspurger's proof -/

/-- **A weight killed by strongly cuspidal functions**: `φ : G(F) → ℝ` is continuous, left
`M(F)`-invariant, and left `U_Q(F)`-invariant for some proper parabolic subgroup `Q ⊇ M`
(`Q = P_{F_W} × P_{F_V}` with `U_Q = N_{F_W} × N_{F_V}`).  In Waldspurger 2010, Lemme 5.2, these
are the functions `g ↦ v^Q_M(g) u_Q(Y_Q(g))`, `Q ∈ ℱ(M)`, `Q ≠ G`. -/
structure IsCuspWeight (φ : ↥d.G → ℝ) : Prop where
  continuous : Continuous φ
  mul_left : ∀ m ∈ L.M, ∀ g, φ (m * g) = φ g
  unip : ∃ (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV), d.IsProperFlagPair FW FV ∧
    L.M ≤ d.whittB FW FV ∧ ∀ u ∈ d.whittU FW FV, ∀ g, φ (u * g) = φ g

variable {L}

/-- `0` is such a weight once a proper parabolic subgroup contains `M`. -/
theorem isCuspWeight_zero {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV}
    (h : d.IsProperFlagPair FW FV) (hM : L.M ≤ d.whittB FW FV) : L.IsCuspWeight 0 :=
  ⟨continuous_const, fun _ _ _ => rfl, ⟨FW, FV, h, hM, fun _ _ _ => rfl⟩⟩

theorem IsCuspWeight.smul {φ : ↥d.G → ℝ} (h : L.IsCuspWeight φ) (c : ℝ) :
    L.IsCuspWeight (c • φ) := by
  obtain ⟨hc, hm, FW, FV, hp, hM, hu⟩ := h
  exact ⟨hc.const_smul c, fun m hm' g => by simp [hm m hm' g],
    ⟨FW, FV, hp, hM, fun u hu' g => by simp [hu u hu' g]⟩⟩

variable (L)

/-- **The weight identity behind Waldspurger 2010, Lemme 5.2 (i), (ii)** (pp. 17–18), as a
statement about our `v_M`: for good compact subgroups `K₁`, `K₂` and `y ∈ G(F)`,
`g ↦ v^{K₁}_M(g y) − v^{K₂}_M(g)` is a finite sum of `IsCuspWeight` functions.

*Source.*  Waldspurger's proof of Lemme 5.2 writes, for `K`, `K̃` special in good position,
`v_M(g) = Σ_{Q ∈ ℱ(M)} ṽ^Q_M(g) u_Q(H_Q(g) − H̃_Q(g))` (from §2.2 (2), i.e. Arthur 1981, (6.3) and
Lemma 6.3, applied to the `(G,M)`-families `ṽ_P(g)` and `d_P(g) = v_P(g) ṽ_P(g)⁻¹`), with
`u_G = 1`; for (ii) the same relation expresses `v_M(g y⁻¹)` through the `v^Q_M(g)`.  Here both
are combined (`Y_P(g) = H^{K₁}_P(g y) − H^{K₂}_P(g)`).  For `Q = L U ≠ G` the term is left
`U(F)`-invariant (`H_P(u g) = H_P(g)` for `P ⊆ Q`, `u ∈ U(F) ⊆ U_P(F)`), left `M(F)`-invariant
(both families are translated by `H_M(m)`) and locally constant.

*Status.*  Not proved: it needs the `(G,M)`-family formalism, which is not built here.  It is not
an axiom either: the source states it for special `K` and for Arthur's `v_M`, which is the volume
of the hull of the `H_P(g)` (our `vM`) when that family is positive; positivity is printed for
special `K` (Beuzart-Plessis §1.10; Waldspurger §2.3) but not proved for `GoodK`. -/
theorem exists_vM_sub_eq_sum_isCuspWeight (K₁ K₂ : d.GoodK L.toFlagLeviDatum) (y : ↥d.G) :
    ∃ (n : ℕ) (φ : Fin n → ↥d.G → ℝ), (∀ i, L.IsCuspWeight (φ i)) ∧
      ∀ g, L.vM K₁ (g * y) - L.vM K₂ g = ∑ i, φ i g := by
  sorry

/-- **Strongly cuspidal functions kill `IsCuspWeight` weights** (Waldspurger 2010, proof of
Lemme 5.2 (i), p. 18, "l'intégrale intérieure sur `U(F)` est nulle puisque `f` est très
cuspidale"): for `f ∈ C_c^∞(G(F))` strongly cuspidal, `x ∈ M(F) ∩ G_reg(F)` and `φ` left
`M(F)`- and `U_Q(F)`-invariant,
`∫_{G_x(F)\G(F)} f(g⁻¹ x g) φ(g) dg = 0`.

*Proof sketch* (our step, following Waldspurger's text).  Let `L_Q ⊇ M` be the Levi factor of
`Q` containing `M` and `K` compact open with `G = Q K`.  Since `G_x ⊆ M ⊆ L_Q`,
`∫_{G_x\G} F(g) dg = ∫_{G_x\L_Q} ∫_{U} ∫_{K} F(l u k) δ_Q(l)⁻¹ dk du dl`.  With
`φ(l u k) = φ((l u l⁻¹) l k) = φ(l k)` the `u`-integral is
`∫_U f(k⁻¹ u⁻¹ z u k) du` with `z = l⁻¹ x l ∈ L_Q(F)` regular in `G`; `u ↦ z⁻¹ u⁻¹ z u` is a
bijection of `U(F)` with constant Jacobian (`Ad(z) − 1` is invertible on `𝔲`), so it is a
multiple of `∫_U f(k⁻¹ z u k) du = ∫_{U} f^k(z u) du = 0`, `f^k = f(k⁻¹ · k)` being strongly
cuspidal for the parabolic `k Q k⁻¹`.  A proof needs a compact open `K` with `G = Q K` for the
given proper `Q` (e.g. a `GoodK`, since `Q ⊇ M` contains some `P ∈ 𝒫(M)`, which is itself to be
proved for flag parabolics).  Not yet proved. -/
theorem integral_isCuspWeight_eq_zero {f : ↥d.G → ℂ} (hf : f ∈ testFunctions ↥d.G)
    (hcusp : IsStronglyCuspidalInline d f) {x : ↥d.G} (hx : x ∈ regularSet d.G d.lie)
    (hxM : x ∈ L.M) (μ : Measure ↥(d.centG x)) [μ.IsHaarMeasure] {φ : ↥d.G → ℝ}
    (hφ : L.IsCuspWeight φ) :
    ∫ q, f ((CosetSpace.out _ q)⁻¹ * x * CosetSpace.out _ q) * (φ (CosetSpace.out _ q) : ℂ)
      ∂d.orbQuotMeasure x μ = 0 := by
  sorry

/-! ## 3. Waldspurger 2010, Lemme 5.2 (i), (ii) -/

variable {L}

/-- **`J^{K₁}_M(x, f(y · y⁻¹)) = J^{K₂}_M(x, f)`** for `f ∈ C_c^∞(G(F))` strongly cuspidal,
`x ∈ M(F) ∩ G_reg(F)`, good compact subgroups `K₁`, `K₂` and `y ∈ G(F)` (Waldspurger 2010,
Lemme 5.2 (i) and (ii) at once), from the weight identity `exists_vM_sub_eq_sum_isCuspWeight` and
the cuspidal vanishing `integral_isCuspWeight_eq_zero`.  Any Haar measure `μ` on `G_x(F)`. -/
theorem weightedOrbitalIntegral_eq_of_isStronglyCuspidal (K₁ K₂ : d.GoodK L.toFlagLeviDatum)
    (y : ↥d.G) {f : ↥d.G → ℂ} (hf : f ∈ testFunctions ↥d.G)
    (hcusp : IsStronglyCuspidalInline d f) {x : ↥d.G} (hx : x ∈ regularSet d.G d.lie)
    (hxM : x ∈ L.M) (μ : Measure ↥(d.centG x)) [μ.IsHaarMeasure] :
    d.weightedOrbitalIntegral L K₁ x μ (fun g => f (y * g * y⁻¹)) =
      d.weightedOrbitalIntegral L K₂ x μ f := by
  have := isMulRightInvariant_of_mem_regularSet hx μ
  have hM : d.centG x ≤ L.M := centG_le_M L.toFlagLeviDatum hx hxM
  have hfc : Continuous f := hf.1.continuous
  set ι := (d.centG x).subtype
  set m := d.orbQuotMeasure x μ
  -- step 1: move `y` from `f` to the weight
  have h1 : ∫ q, d.weightedIntegrand L K₁ x (fun g => f (y * g * y⁻¹)) (CosetSpace.out ι q) ∂m =
      ∫ q, f ((CosetSpace.out ι q)⁻¹ * x * CosetSpace.out ι q) *
        (L.vM K₁ (CosetSpace.out ι q * y) : ℂ) ∂m := by
    set Φ : ↥d.G → ℂ := fun g => f (g⁻¹ * x * g) * (L.vM K₁ (g * y) : ℂ)
    have hΦ : ∀ c ∈ d.centG x, ∀ g, Φ (c * g) = Φ g := by
      intro c hc g
      simp only [Φ, d.conj_mul_of_mem_centG x hc, mul_assoc c g y,
        show c * (g * y) = ((⟨c, hM hc⟩ : ↥L.M) : ↥d.G) * (g * y) from rfl, L.vM_mul_left]
    refine Eq.trans ?_ (d.integral_out_mulRight μ hΦ y⁻¹)
    congr 1
    funext q
    simp only [Φ, ι, weightedIntegrand, inv_mul_cancel_right]
    congr 2
    group
  -- step 2: the difference of the weights
  obtain ⟨n, φ, hφ, hsum⟩ := exists_vM_sub_eq_sum_isCuspWeight L K₁ K₂ y
  have hint : ∀ ψ : ↥d.G → ℝ, Continuous ψ → (∀ m ∈ L.M, ∀ g, ψ (m * g) = ψ g) →
      Integrable (fun q => f ((CosetSpace.out ι q)⁻¹ * x * CosetSpace.out ι q) *
        (ψ (CosetSpace.out ι q) : ℂ)) m :=
    fun ψ hψ hψM => integrable_weight hx.1 hM hfc hf.2 hψ hψM μ
  have hv1 := hint (fun g => L.vM K₁ (g * y)) ((L.continuous_vM K₁).comp (continuous_id.mul continuous_const))
    (fun m' hm' g => by
      simp only [mul_assoc, show m' * (g * y) = ((⟨m', hm'⟩ : ↥L.M) : ↥d.G) * (g * y) from rfl,
        L.vM_mul_left])
  have hv2 := hint (L.vM K₂) (L.continuous_vM K₂) (fun m' hm' g => L.vM_mul_left K₂ ⟨m', hm'⟩ g)
  have hsub : ∫ q, f ((CosetSpace.out ι q)⁻¹ * x * CosetSpace.out ι q) *
        (L.vM K₁ (CosetSpace.out ι q * y) : ℂ) ∂m -
      ∫ q, f ((CosetSpace.out ι q)⁻¹ * x * CosetSpace.out ι q) *
        (L.vM K₂ (CosetSpace.out ι q) : ℂ) ∂m = 0 := by
    rw [← integral_sub hv1 hv2]
    have : (fun q => f ((CosetSpace.out ι q)⁻¹ * x * CosetSpace.out ι q) *
          (L.vM K₁ (CosetSpace.out ι q * y) : ℂ) -
        f ((CosetSpace.out ι q)⁻¹ * x * CosetSpace.out ι q) *
          (L.vM K₂ (CosetSpace.out ι q) : ℂ)) =
        fun q => ∑ i, f ((CosetSpace.out ι q)⁻¹ * x * CosetSpace.out ι q) *
          (φ i (CosetSpace.out ι q) : ℂ) := by
      funext q
      rw [← mul_sub, ← Finset.mul_sum, ← Complex.ofReal_sub, hsum, Complex.ofReal_sum]
    rw [this, integral_finsetSum _ fun i _ =>
      hint (φ i) (hφ i).continuous (hφ i).mul_left]
    exact Finset.sum_eq_zero fun i _ => integral_isCuspWeight_eq_zero L hf hcusp hx hxM μ (hφ i)
  unfold weightedOrbitalIntegral
  rw [h1, sub_eq_zero.1 hsub]
  rfl

/-- **Waldspurger 2010, Lemme 5.2 (i)** (Beuzart-Plessis Lemma 5.2.1(ii)): for `f ∈ C_c^∞(G(F))`
strongly cuspidal and `x ∈ M(F) ∩ G_reg(F)`, `J_M(x, f)` does not depend on the good compact
subgroup `K`.  (Rests on the two `sorry`s of §2.) -/
theorem weightedOrbitalIntegral_indep (K₁ K₂ : d.GoodK L.toFlagLeviDatum) {f : ↥d.G → ℂ}
    (hf : f ∈ testFunctions ↥d.G) (hcusp : IsStronglyCuspidalInline d f) {x : ↥d.G}
    (hx : x ∈ regularSet d.G d.lie) (hxM : x ∈ L.M) (μ : Measure ↥(d.centG x))
    [μ.IsHaarMeasure] :
    d.weightedOrbitalIntegral L K₁ x μ f = d.weightedOrbitalIntegral L K₂ x μ f := by
  have h := weightedOrbitalIntegral_eq_of_isStronglyCuspidal K₁ K₂ 1 hf hcusp hx hxM μ
  simpa using h

/-- **Waldspurger 2010, Lemme 5.2 (ii)**: for `f ∈ C_c^∞(G(F))` strongly cuspidal, `x ∈ M(F) ∩ G_reg(F)` and `y ∈ G(F)`,
`J_M(x, f(y · y⁻¹)) = J_M(x, f)`.  Beuzart-Plessis Lemma 5.2.1(iv),
`J_{y M y⁻¹}(y x y⁻¹, f) = J_M(x, f)`, follows from this and (i) by transport of structure (not
done here).  (Rests on the two `sorry`s of §2.) -/
theorem weightedOrbitalIntegral_conj_fun (K : d.GoodK L.toFlagLeviDatum) (y : ↥d.G)
    {f : ↥d.G → ℂ} (hf : f ∈ testFunctions ↥d.G) (hcusp : IsStronglyCuspidalInline d f)
    {x : ↥d.G} (hx : x ∈ regularSet d.G d.lie) (hxM : x ∈ L.M) (μ : Measure ↥(d.centG x))
    [μ.IsHaarMeasure] :
    d.weightedOrbitalIntegral L K x μ (fun g => f (y * g * y⁻¹)) =
      d.weightedOrbitalIntegral L K x μ f :=
  weightedOrbitalIntegral_eq_of_isStronglyCuspidal K K y hf hcusp hx hxM μ

/-! ### The case `a_M = a_G`: no cuspidality needed -/

/-- For `a_M = a_G` (e.g. `M = G`) `J_M(x, f)` does not depend on `K`, for every `f`
(`v_M = 1`). -/
theorem weightedOrbitalIntegral_indep_of_aG_eq_top (hG : L.aG = ⊤)
    (K₁ K₂ : d.GoodK L.toFlagLeviDatum) (x : ↥d.G) (μ : Measure ↥(d.centG x)) (f : ↥d.G → ℂ) :
    d.weightedOrbitalIntegral L K₁ x μ f = d.weightedOrbitalIntegral L K₂ x μ f := by
  rw [weightedOrbitalIntegral_eq_orbitalIntegral_of_aG_eq_top hG,
    weightedOrbitalIntegral_eq_orbitalIntegral_of_aG_eq_top hG]

/-- For `a_M = a_G`, `J_M(x, f(y · y⁻¹)) = J_M(x, f)` for every `f` and `y ∈ G(F)`: the orbital
integral is invariant under right translation on `G_x(F)\G(F)`. -/
theorem weightedOrbitalIntegral_conj_fun_of_aG_eq_top (hG : L.aG = ⊤)
    (K : d.GoodK L.toFlagLeviDatum) (y : ↥d.G) {x : ↥d.G} (μ : Measure ↥(d.centG x))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : ↥d.G → ℂ) :
    d.weightedOrbitalIntegral L K x μ (fun g => f (y * g * y⁻¹)) =
      d.weightedOrbitalIntegral L K x μ f := by
  rw [weightedOrbitalIntegral_eq_orbitalIntegral_of_aG_eq_top hG,
    weightedOrbitalIntegral_eq_orbitalIntegral_of_aG_eq_top hG]
  rw [orbitalIntegral_eq, orbitalIntegral_eq]
  congr 1
  set Φ : ↥d.G → ℂ := fun g => f (g⁻¹ * x * g)
  have hΦ : ∀ c ∈ d.centG x, ∀ g, Φ (c * g) = Φ g := by
    intro c hc g
    simp only [Φ, d.conj_mul_of_mem_centG x hc]
  refine Eq.trans ?_ (d.integral_out_mulRight μ hΦ y⁻¹)
  congr 1
  funext q
  simp only [Φ]
  congr 1
  group

/-! ## 4. `θ_f` -/

/-- **`θ_f(x)` does not depend on `K`** for `f ∈ C_c^∞(G(F))` strongly cuspidal and
`x ∈ M(F) ∩ G_reg(F)` (Beuzart-Plessis Lemma 5.2.1(ii); Waldspurger 2010, Lemme 5.2 (i)).
(Rests on the two `sorry`s of §2.) -/
theorem thetaFBP_indep (K₁ K₂ : d.GoodK L.toFlagLeviDatum) {f : ↥d.G → ℂ}
    (hf : f ∈ testFunctions ↥d.G) (hcusp : IsStronglyCuspidalInline d f) {x : ↥d.G}
    (hx : x ∈ regularSet d.G d.lie) (hxM : x ∈ L.M) :
    L.thetaFBP K₁ f x = L.thetaFBP K₂ f x := by
  unfold thetaFBP
  congr 1
  by_cases h : ∃ μ, L.IsDcMeasure x μ
  · have := (isDcMeasure_dcMeasure h).1
    exact weightedOrbitalIntegral_indep K₁ K₂ hf hcusp hx hxM _
  · rw [dcMeasure_of_not_exists h, weightedOrbitalIntegral_zero_measure,
      weightedOrbitalIntegral_zero_measure]

/-- **`θ_f(x)` is unchanged by conjugating `f` by any `y ∈ G(F)`**, for `f ∈ C_c^∞(G(F))`
strongly cuspidal and `x ∈ M(F) ∩ G_reg(F)` (Waldspurger 2010, Lemme 5.2 (ii); Beuzart-Plessis
Lemma 5.2.1(iv) follows from it and (i) by transport of structure, see the module docstring).  Extends `thetaFBP_conj_K` (`y ∈ K`, any `f`).  (Rests on the two `sorry`s of §2.) -/
theorem thetaFBP_conj_fun (K : d.GoodK L.toFlagLeviDatum) (y : ↥d.G) {f : ↥d.G → ℂ}
    (hf : f ∈ testFunctions ↥d.G) (hcusp : IsStronglyCuspidalInline d f) {x : ↥d.G}
    (hx : x ∈ regularSet d.G d.lie) (hxM : x ∈ L.M) :
    L.thetaFBP K (fun g => f (y * g * y⁻¹)) x = L.thetaFBP K f x := by
  unfold thetaFBP
  congr 1
  by_cases h : ∃ μ, L.IsDcMeasure x μ
  · have := (isDcMeasure_dcMeasure h).1
    exact weightedOrbitalIntegral_conj_fun K y hf hcusp hx hxM _
  · rw [dcMeasure_of_not_exists h, weightedOrbitalIntegral_zero_measure,
      weightedOrbitalIntegral_zero_measure]

/-- For `a_M = a_G`, `θ_f(x)` does not depend on `K`, for every `f`. -/
theorem thetaFBP_indep_of_aG_eq_top (hG : L.aG = ⊤) (K₁ K₂ : d.GoodK L.toFlagLeviDatum)
    (f : ↥d.G → ℂ) (x : ↥d.G) : L.thetaFBP K₁ f x = L.thetaFBP K₂ f x := by
  rw [thetaFBP_of_aG_eq_top hG, thetaFBP_of_aG_eq_top hG]

/-- For `a_M = a_G` and `x` regular, `θ_f(x)` is unchanged by conjugating `f` by any
`y ∈ G(F)`, for every `f`. -/
theorem thetaFBP_conj_fun_of_aG_eq_top (hG : L.aG = ⊤) (K : d.GoodK L.toFlagLeviDatum)
    (y : ↥d.G) (f : ↥d.G → ℂ) {x : ↥d.G} (hx : x ∈ regularSet d.G d.lie) :
    L.thetaFBP K (fun g => f (y * g * y⁻¹)) x = L.thetaFBP K f x := by
  unfold thetaFBP
  congr 1
  by_cases h : ∃ μ, L.IsDcMeasure x μ
  · have := (isDcMeasure_dcMeasure h).1
    have := isMulRightInvariant_of_mem_regularSet hx (L.dcMeasure x)
    exact weightedOrbitalIntegral_conj_fun_of_aG_eq_top hG K y _ f
  · rw [dcMeasure_of_not_exists h, weightedOrbitalIntegral_zero_measure,
      weightedOrbitalIntegral_zero_measure]

end ReducedLeviDatum

end GGPData

end GSpinGGP
