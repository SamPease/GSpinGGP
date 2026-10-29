/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Interface
import GSpinGGP.GGP.Levi

/-!
# Arthur's elliptic theory and the spectral side (cited)

The cited facts used by `TraceFormula/Spectral.lean`, each an
`axiom` with its source.  They are stated for the objects of `GGP/Levi.lean` §6–§7: normalized
parabolic induction `parInd` (a real definition) and `R_ind(G, η)` (`Rind`, defined at the level of
characters).

* `hc_vMult_eq_mult_parInd` (Harish-Chandra: finite length of `i_P^G(σ)`, linear independence of
  characters): a virtual representation with the character of `i_P^G(σ)` has the multiplicity of
  `i_P^G(σ)`.
* `vanDijk_charG_parInd_ell` (van Dijk 1972; BP (3.4.3)): induced characters vanish on the elliptic
  regular set.
* `arthur_mem_Rind_of_vChar_ell` (Arthur, Acta Math. 171 (1993); BP §2.7, (2.7.1)): a virtual
  tempered representation whose character vanishes on the elliptic regular set is properly
  induced.
* `bp_exists_vChar_eq_thetaF_ell` (BP Prop 5.6.1(ii) and Lemma 5.4.2(i)): on the elliptic set,
  `θ_f` is the character of a virtual tempered representation.

None of them depends on the normalization of Arthur's elliptic inner product (the "A93 constant",
still unchecked by hand): only the vanishing statements are used.
-/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **The multiplicity of an induced representation is that of its class in `R_temp`**
(Harish-Chandra; see Waldspurger, *La formule de Plancherel pour les groupes `p`-adiques d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), §III.4 and §VII (numbers unverified); BP §2.2,
§2.7).  For `P` proper and `σ` tempered with central character `η`, `i_P^G(σ)` is a finite
orthogonal sum `⊕ n_c π_c` of irreducible tempered representations, each with central character
`η` on `A_G(F)`.  If a virtual representation `Π ∈ R_temp(G, η)` has the character of `i_P^G(σ)` on
`G_reg(F)`, then `Π = Σ n_c [π_c]` (Harish-Chandra's linear independence of the characters of
inequivalent irreducible admissible representations, together with the local integrability of
characters, which makes equality on `G_reg(F)` an equality of distributions), and
`m(Π) = Σ n_c m(π_c) = m(i_P^G(σ))` (additivity of `Hom_H(·^∞, ξ)` over finite direct sums; each
`m(π_c) ≤ 1` by `emoryTakeda_mult_le_one`, so `m(i_P^G(σ))` is finite).

Hidden second input: `vMult` takes `ℕ∞.toNat` constituent by
constituent while the right-hand side takes it of the total, and these agree only because every
`m(π_c)` is finite.  That finiteness is not Harish-Chandra's: it is multiplicity at most one for
irreducible tempered representations (`emoryTakeda_mult_le_one`, itself a cited axiom on the same
path).  No hypothesis `m(i_P^G(σ)) ≠ ∞` is added, because it could not be
discharged from `emoryTakeda_mult_le_one` (which is for irreducible `π`) without this very
decomposition.  `K` in `ParIndData` may be any compact open subgroup with `G(F) = P(F) K`
(`dg = dp dk` holds for each).

Degenerate cases: if `G` has no proper parabolic subgroup (e.g. `toyData`) nothing is asserted.
If `charG (parInd D)` were `0` on `G_reg(F)` (the junk value of `characterOn`), the hypothesis
forces `Π = 0` by linear independence, and then `m(i_P^G(σ)) = 0` is what is asserted; this cannot
occur for a genuine `i_P^G(σ) ≠ 0`, whose character is nonzero. -/
axiom hc_vMult_eq_mult_parInd (ψ : NontrivialAddChar F) (d : GGPData F) (η : CentralCharOn d)
    (D : d.ParIndData) (hD : d.IsTempIndData η D) (P : VirtualTemp d η)
    (hP : Set.EqOn (vChar d P) (charG d (d.parInd D)) (regularSet d.G d.lie)) :
    vMult ψ d P = ((mult ψ d (d.parInd D)).toNat : ℂ)

/-- **Van Dijk's formula: induced characters vanish on the elliptic set** (G. van Dijk,
*Computation of certain induced characters of `p`-adic groups*, Math. Ann. 199 (1972), 229–240;
BP (3.4.2)/(3.4.3) = Thesis (3.5.3.2)).  The character of `i_P^G(σ)` at a regular `x` is a sum over
the `M(F)`-conjugacy classes of `M(F)`-elements `G(F)`-conjugate to `x`; for `P` proper the split
centre `A_M` of `M` strictly contains `A_G`, so an elliptic `x` (centralizer compact modulo
`A_G(F)`) is conjugate to no element of `M(F)`, and `θ_{i_P^G σ}(x) = 0`. -/
axiom vanDijk_charG_parInd_ell (d : GGPData F) (η : CentralCharOn d) (D : d.ParIndData)
    (hD : d.IsTempIndData η D) : ∀ x ∈ d.ellRegSet, charG d (d.parInd D) x = 0

/-- **Virtual representations with vanishing elliptic character are properly induced**
(J. Arthur, *On elliptic tempered characters*, Acta Math. 171 (1993), 73–138, §6 (orthogonality
relations for elliptic tempered characters; theorem numbers unverified); BP §2.7, (2.7.1):
`R_temp(G) = R_ind(G) ⊕ R_ell(G)`, with `R_ell(G)` spanned by the elliptic representations
`𝒳_ell(G)`, whose characters are orthogonal, hence linearly independent, for the elliptic inner
product; transported to the `χ`-equivariant setting).  Write `Π = Π_ind + Σ c_π π`
with `π ∈ 𝒳_ell(G, η)`; `θ_{Π_ind} = 0` on `G_ell,reg(F)` by van Dijk; so `θ_Π = 0` there forces
all `c_π = 0` by orthogonality.  Only the vanishing is used, not the value of the elliptic norms.

Implicit content: a generator of `Rind` carries a `ParIndData`, i.e. a compact open `K` with
`G(F) = P(F) K`; the axiom therefore also asserts that such `K` exist for the parabolic subgroups
involved (Bruhat–Tits: a good maximal compact subgroup; Thesis §2.3, BP §1.5).

Degenerate case `toyData` (`A_G = G`, so every regular element is elliptic and there is no proper
parabolic subgroup, `Rind = 0`): the axiom says `θ_Π = 0` on `G_reg(F)` implies `Π = 0`, which is
the linear independence of characters. -/
axiom arthur_mem_Rind_of_vChar_ell (d : GGPData F) (η : CentralCharOn d) (P : VirtualTemp d η)
    (hP : ∀ x ∈ d.ellRegSet, vChar d P x = 0) : P ∈ d.Rind η

/-- **On the elliptic set, `θ_f` is a virtual tempered character** (BP Prop 5.6.1(ii) and
Lemma 5.4.2(i); Thesis Prop 4.8.1; transported to the `χ`-equivariant setting).  For `f ∈ 𝒞_scusp(A_G(F)\G(F))` with `θ_f(ag) = η(a) θ_f(g)`
(`f ∈ ScuspTestFn d η.inv`),
`θ_f = Σ_{π ∈ 𝒳_ell(G, η)} D(π) θ̂_f(π) θ_π` on `G_ell,reg(F)` (BP Prop 5.6.1(ii)), and the sum is
finite since `f` is compactly supported modulo `A_G(F)` (BP Lemma 5.4.2(i)).

**Adapted, not the cited statement.**  BP Prop 5.6.1(ii) is
for `f ∈ 𝒞_scusp(G(F))` without central equivariance, compact centre, and gives `θ_f` as an
integral over `𝒳(G)` against a continuous measure, not as a finite sum.  The form here is a
composite of: (1) the `P_χ` transfer `f = P_χ(κ f)`, expressing a `χ`-equivariant `f` through an
untwisted one (proved in `TraceFormula/ThetaF.lean`); (2) restriction to `G_ell` kills the
induced part of `𝒳(G)` (van Dijk); (3) discreteness
of `𝒳_ell(G, η)` under a fixed central character `η` on `A_G(F)` (unramified twists trivial on
`A_G` form a finite group modulo those fixing an elliptic triple), which with BP Lemma 5.4.2(i)
makes the sum finite; (3) is not cited from a source.  Direction of the central character:
`f(ag) = η(a) f(g)` gives `θ_f(ag) = η(a) θ_f(g)`, the law of characters in
`VirtualTemp d η`; positive normalization constants are absorbed into `Π`.

Degenerate cases: `f = 0` (take `Π = 0`); if no quasi-character represents the orbital pairing of
`f`, then `thetaF d f = 0` by definition and `Π = 0` works. -/
axiom bp_exists_vChar_eq_thetaF_ell (d : GGPData F) (η : CentralCharOn d) {f : ↥d.G → ℂ}
    (hf : f ∈ ScuspTestFn d η.inv) :
    ∃ P : VirtualTemp d η, ∀ x ∈ d.ellRegSet, vChar d P x = thetaF d f x

end GSpinGGP
