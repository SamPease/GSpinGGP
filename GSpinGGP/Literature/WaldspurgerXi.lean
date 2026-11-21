/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.HarmonicAnalysis.HarishChandraXi
import GSpinGGP.TraceFormula.LogNormDescent

/-!
# Square-integrability of Harish-Chandra's `Ξ` against a power of `σ` (Waldspurger 2003)

* **axiom** `exists_iwasawaPair_xi_sq_integrable` (*derived*, identification steps only):
  Waldspurger, *La formule de Plancherel pour les groupes `p`-adiques, d'après Harish-Chandra*,
  J. Inst. Math. Jussieu 2 (2003), Lemme II.1.5, p. 252, for `G = GSpin(W) × GSpin(V)`, with
  Waldspurger's special maximal compact subgroup, his `Ξ` and his `σ` written in our terms.

The form for every Iwasawa datum and the log-norm `σ_G` of the project is a theorem
(`GGPData.IwasawaDatum.exists_integrable_xiHC_sq_mul_logNormG_inv_pow`,
`TraceFormula/XiIntegrable.lean`).
-/

noncomputable section

open MeasureTheory

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **`∫_G Ξ(g)² (1 + σ(g))^{-d} dg < ∞`** (Waldspurger 2003, Lemme II.1.5).  A *derived* axiom:
a printed statement whose hypotheses and notation are matched with ours in the steps below (all
identifications: a choice of torus, compact subgroup and lattice basis, and notation).

**Ingredient (printed).** J.-L. Waldspurger, *La formule de Plancherel pour les groupes
`p`-adiques, d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333.
* Lemme II.1.5, p. 252: "Il existe `d ∈ ℕ` tel que l'intégrale `∫_G Ξ(g)²(1 + σ(g))^{-d} dg`
  soit convergente." (Proof printed there, from Lemme II.1.1 and I.1 (4)–(6).)
* Setting, §I.1, pp. 238–242: `F` non-archimedean local with finite residue field, `G` connected
  reductive; `A₀` a maximal split torus, `M₀ = Z_G(A₀)`, `P₀` a minimal parabolic subgroup with
  Levi `M₀`; p. 240: "On fixe un sous-groupe compact maximal `K` de `G`, dont on suppose qu'il est
  le fixateur d'un point spécial de l'appartement associé à `A₀` dans l'immeuble de `G`", the
  measure on a closed subgroup `H` is left invariant with `mes(H ∩ K) = 1`, `δ_H` is "le module
  du groupe `H`", and `G = P K` for `P` semi-standard; p. 242: "Fixons un plongement algébrique
  `τ : G → GL_n(F)`. On peut supposer, et l'on suppose, que `τ(K) ⊂ GL_n(𝒪)`",
  `‖g‖ = sup_{i,j} sup(|a_ij|_F, |b_ij|_F)` for `τ(g) = (a_ij)`, `τ(g)⁻¹ = (b_ij)`, "On vérifie
  que `‖g‖ ≥ 1`", `σ(g) = log ‖g‖`.
* §II.1, pp. 250–251: `Ξ(g) = ⟨π(g)e, e⟩` for `π = I_{P₀}^G 1` and `e` its `K`-fixed vector with
  `e(1) = 1`, and "`Ξ(g) = ∫_K δ₀(m₀(kg))^{1/2} dk`", with `g = u₀(g) m₀(g) k₀(g)` (p. 240) and
  `δ₀ = δ_{P₀}` (p. 241).

**Steps (identifications).**
(a) *Hypotheses and choice of `A₀`, `K`.* A `PAdicField` is non-archimedean local with finite
  residue field; `G = GSpin(W) × GSpin(V)` is connected reductive.  For full isotropic flags
  `F_W`, `F_V`, `P₀ = whittB F_W F_V` is a minimal parabolic subgroup, and the split torus of a
  Witt basis adapted to the flags (scaling `e_i` by `t_i`, `f_i` by `t_i⁻¹`) is a maximal split
  torus `A₀ ⊆ P₀` (the dictionary of `tits_iwasawa`, step 2).  Take Waldspurger's `K = K_s`, the
  fixer of a special point of the apartment of `A₀`; it is compact open, and `G = P₀ K_s`
  (p. 240).  So `(P₀, K_s)` is an `IwasawaPair` `I` with `I.P = whittB F_W F_V`.
(b) *`τ` and `σ`.* Let `A = C(W) × C(V)` and `τ₀(g) = L_g`, left multiplication on `A`.  `τ₀` is
  an algebraic embedding `G → GL(A)`: `GSpin(W)` is a closed subgroup of the algebraic group
  `C(W)^×`, and `C(W)^×` acts faithfully on `C(W)` by left multiplication, with closed image
  (likewise for `V`).  `K_s` is compact, so it stabilizes an `𝒪`-lattice `L ⊆ A`; for an
  `𝒪`-basis `b` of `L`, `τ₀(K_s) ⊆ GL_n(𝒪)` in the basis `b`, and Waldspurger's `‖g‖` is
  `sup` of the normalized absolute values `|·|_F` of the matrix entries of `L_g` and `L_{g⁻¹}`
  in `b`.  The norm `‖·‖` of `F` (Mathlib's) is `|·|_F^c` for some `c > 0` (two absolute values
  defining the same topology), so `entryMaxNorm b d.G g`, built with `‖·‖`, is `‖g‖_W^c` (the
  `max 1` there changes nothing since `‖g‖_W ≥ 1`), and `log (entryMaxNorm b d.G g) = c σ(g)`.
  Then `(1 + c σ)^{-d} ≤ max(1, 1/c)^d (1 + σ)^{-d}`, so the same `d` works for
  `1 + log entryMaxNorm` as for Waldspurger's `1 + σ`.
(c) *`δ` and `Ξ`.* Waldspurger's `δ_H` (p. 240; see the integration formula (2) there) is the
  module of `H` for left Haar measure, the
  convention of `IwasawaPair.delta` (Mathlib's `modularCharacter`: `μ(E p⁻¹) = δ(p) μ(E)`).  The
  module of `P₀` is trivial on `U₀` (a union of compact subgroups), so
  `δ₀(m₀(g)) = δ_{P₀}(u₀(g) m₀(g))`, and with `dk` of total mass `1` Waldspurger's `Ξ` is
  `I.xi`.
(d) *Measures.* Waldspurger's Haar measure on `G` (with `mes(K) = 1`) is a positive multiple of
  `Measure.haar` (uniqueness of Haar measure); convergence of the integral of the nonnegative
  continuous function `Ξ²(1 + σ)^{-d}` is integrability, which a positive multiple of the
  measure does not change.

Statement: for full isotropic flags `F_W`, `F_V` there are an Iwasawa pair `I` with
`I.P = whittB F_W F_V`, a basis `b` of `C(W) × C(V)` and `D ∈ ℕ` such that
`g ↦ Ξ_I(g)² (1 + log entryMaxNorm b g)^{-D}` is integrable on `G(F)`. -/
axiom exists_iwasawaPair_xi_sq_integrable (d : GGPData F) (FW : IsotropicFlag d.QW)
    (FV : IsotropicFlag d.QV) (hW : FW.IsFull) (hV : FV.IsFull) :
    ∃ (I : IwasawaPair ↥d.G) (_ : I.P = d.whittB FW FV)
      (b : Module.Basis (Fin (Module.finrank F d.ambient)) F d.ambient) (D : ℕ),
      Integrable (fun g : ↥d.G => I.xi g ^ 2 * ((1 + Real.log (entryMaxNorm b d.G g)) ^ D)⁻¹)
        (Measure.haar : Measure ↥d.G)

end GSpinGGP
