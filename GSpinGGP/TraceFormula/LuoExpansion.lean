/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.SOLie

/-!
# The geometric expansion of `J^Lie` for the special orthogonal triple

One statement, `luo_lie_geomExpansion_SO`, about the special orthogonal GGP triple `(Ḡ, H̄, ξ)` on
`𝔤 = so(W) ⊕ so(V)` of an admissible pair, with the objects of `TraceFormula/SOLie.lean` (defined
on the quadratic spaces, not on `GSpin`).  It is a **theorem with `sorry`, not a literature axiom**:
it combines several published statements about the quasi-character `θ_f` of a strongly cuspidal
`f`, and one of its parts is not printed in the form used here.

Published statements (the labels (b)–(d) are those of the statement):

* (c) Waldspurger, Compositio 146 (2010), §6.1 Lemme (ii): `θ_f` is a quasi-character; §5.3 Lemme via
  §6.1: it is locally integrable and locally constant on `𝔤_reg(F)`;
* (d) Luo (arXiv:2009.13947) Thm 7.3.3: `J^Lie(f) = m^Lie_geom(θ_f)`, with `m^Lie_geom` in its limit
  form (Luo Prop 7.1.2(3));
* for (b): Beuzart-Plessis, Astérisque 418 (2020), Thm 5.5.2(ii) (page numbers and reference labels
  below are those of arXiv:1506.01452) and the Weyl integration formula of BP §1.7.

Not printed: (b) itself, `∫ θ_f f' = ∫_{Ḡ(F)} ∫_{𝔤(F)} f(x⁻¹Xx) f'(X) dX dx`.  It follows from
BP Thm 5.5.2(ii) by the Weyl integration formula; see the docstring.  The sources define `θ_f` by
an explicit formula (weighted orbital integrals), which is not formalized; here `θ_f` is the
existential witness `θ`.  The identification of these objects with those of the general spin
triple on `𝔤⁰` is `TraceFormula/LuoTransfer.lean`.
-/

open MeasureTheory Topology Filter

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

open LuoDatum

/-- **The geometric expansion of `J^Lie` for the special orthogonal GGP triple, with the
properties of `θ_f` it uses** (Luo Thm 7.3.3; Beuzart-Plessis Thm 5.5.2(ii) with the Weyl integration formula;
Waldspurger 2010 §5.3, §6.1).  BP page numbers and reference labels are those of arXiv:1506.01452.

**Setting.**  `F` is `p`-adic, `L` an admissible pair `(W, V)`, `V = W ⊕^⊥ D ⊕^⊥ Z`, with Luo's basis
(Luo §2.1, Def 2.1.3: `q(z_i, z_j) = δ_{i,-j}` on `Z`, `ν₀ = q(z₀, z₀)`), `Ḡ = SO(W) × SO(V)`,
`H̄ = SO(W) ⋉ N`, `λ`, `ξ = ψ ∘ λ` and `B = ½(tr_W + tr_V)` as in Luo §2.1, `𝔤 = so(W) ⊕ so(V)`
with the self-dual measure for `ψ ∘ B` (BP §1.6; Luo uses the notation of BP §1–§5, Luo p. 6).
The measures are: any Haar measure `μG` on `Ḡ(F)`; any Haar measure `μH` on `H̄(F)` with `μ𝔥` on
`𝔥(F)` deduced from it through `exp` (BP §1.6, used for `J^Lie` in Luo §4: `B` is degenerate on
`𝔥`); the quotient measure `m` on `H̄(F)\Ḡ(F)`; and on each `𝔱(F)`, `T ∈ 𝒯`, the measure `ν(T) dX`
(`IsExpCompatT`; Luo §7.1).  The exponential is the exponential series in `End W × End V`, i.e. that
of the faithful representation on `W ⊕ V`.  `f ∈ S_scusp(𝔤(F))` (`IsScusp`; Luo p. 7, BP §5.1,
Waldspurger 2010 §6.1 "très cuspidale").

**Conclusion.** There is `θ` (the function `θ_f` of BP §5.2, Waldspurger 2010 §6.1 and Luo
pp. 6–7: `θ_f(X) = (−1)^{a_{M(X)} − a_G} ν(G_X)^{−1} D^G(X)^{−1/2} J_{M(X)}(X, f)` on `𝔤_reg(F)`,
Arthur's weighted orbital integrals) with:

* (b) `θ` is locally integrable, continuous on `𝔤_reg(F)`, and `∫_{𝔤(F)} θ f' dX = ∫_{Ḡ(F)} ∫_{𝔤(F)}
  f(x⁻¹Xx) f'(X) dX dx` for every test function `f'`.  The identity is the **composite of BP Thm
  5.5.2(ii)** (`J^A(f, f') = ∫_{Γ(𝔤)} D^G(X)^{1/2} θ_f(X) J_G(X, f') dX`, absolutely convergent)
  **with the Weyl integration formula on `𝔤` of BP §1.7** (p. 38), exactly as in the proof of BP
  Prop 5.6.1(i) (p. 130: "By Theorem 5.5.2(ii) and (iii) and the Weyl integration formula, we have
  `∫ θ_f f̂' = ∫ θ_{f̂} f'`").  Local integrability and local constancy on `𝔤_reg(F)`: Waldspurger
  2010 §5.3 Lemme (`θ_f` "invariante par conjugaison, à support compact modulo conjugaison,
  localement intégrable … et localement constante sur `G_reg(F)`"), transferred to the Lie algebra in
  §6.1 ("Elle a des propriétés similaires à celles énoncées au lemme 5.3").
* (c) `θ` is a quasi-character on `𝔤(F)` (Waldspurger 2010 §6.1 Lemme (ii); BP Prop 5.6.1(i):
  a Schwartz quasi-character).  Its support is compact modulo conjugation (the support of `θ_f` is
  contained in `(Supp f)^G`, proof of Waldspurger's §5.3 Lemme, via §6.1), so `θ_f ∈ QC_c(𝔤)`; this
  is not part of the statement below, which does not need it.
* (d) `m^Lie_{geom,s}(θ) → J^Lie(f)` as `s → 0⁺`.  Luo Thm 7.3.3 (p. 46): "`J^Lie(f) =
  J^Lie_geom(f)` for any `f ∈ S_scusp(𝔤)`", with `J^Lie_geom(f) = m^Lie_geom(θ_f)` (§7.3) and
  `m^Lie_geom(θ) = lim_{s→0⁺} ∫_{Γ^Lie(G,H)} D^G(X)^{1/2} c_θ(X) Δ(X)^{s−1/2} dX` for
  `θ ∈ QC_c(𝔤)` (Prop 7.1.2(3), p. 44; the limit exists), extended continuously to `SQC(𝔤)`.  Since
  `θ_f ∈ QC_c(𝔤)` (see (c)), the limit formula applies to it directly.  `Γ^Lie(G, H)` and its measure
  `Σ_{T ∈ 𝒯} |W(H,T)|⁻¹ ν(T) ∫_{𝔱(F)}` are Luo §7.1, (7.1.5); `Δ` is (7.1.7).  **Luo's text does not define
  `c_θ(X)` for `X ≠ 0`**: it defines `c_θ` only
  at `X = 0` for quasi-split `G` (p. 41: `c_{θ,O_reg}`, `c_{θ,O_{ν₀}}` if `dim V ≥ 4` is even,
  `c_{θ,O_{−ν₀}}` if `dim W ≥ 4` is even).  The definition used here at `X ∈ 𝔱_♮(F)` is that of
  Waldspurger 2010 §7.3
  (the same recipe applied to the descended triple: `O_{ν₀}` on `V'_X` if `dim V'_X ≥ 4` is even,
  `O_{−ν₀}` on `W'_X` if `dim W'_X ≥ 4` is even, the unique regular orbit otherwise) and §7.9 (its
  Lie-algebra form on `𝔱_♮(F)`); when `G_X` is not quasi-split, `c_θ(X) = 0` (BP Prop 4.5.1 2.(i)).

**Status: `sorry`, not a literature axiom.**  (c) and (d) are published statements for this
group.  The identity in (b) is not printed.  What is printed is BP Thm 5.5.2(ii),
`J^A(f, f') = ∫_{Γ(𝔤)} D^G(X)^{1/2} θ_f(X) J_G(X, f') dX` (absolutely convergent), where
`J^A(f, f') = ∫_{A_G(F)\G(F)} ∫_{𝔤(F)} f(x⁻¹Xx) f'(X) dX dx`, and the Weyl integration formula
`∫_{𝔤(F)} φ(X) dX = ∫_{Γ(𝔤)} D^G(X)^{1/2} J_G(X, φ) dX` (BP §1.7, for `φ ∈ S(𝔤(F))`), both for any
connected reductive group, here `Ḡ` with `A_Ḡ = 1`.  Argument for (b), not formalized: `θ_f` is
invariant under conjugation, so `J_G(X, θ_f f') = θ_f(X) J_G(X, f')`; the Weyl formula extends from
`S(𝔤(F))` to the integrable function `θ_f f'`; so `∫ θ_f f' = ∫_{Γ(𝔤)} D^G(X)^{1/2} θ_f(X) J_G(X, f') dX
= J^A(f, f')`.  (BP uses the same two ingredients in the proof of Prop 5.6.1(i), for a different
identity.)  BP Thm 5.5.2 is itself announced, not proved: "The two theorems
below are slight variations around the local trace formula of Arthur (cf. [A1]) and its version for
Lie algebras due to Waldspurger (cf. [Wa3]). The proof of these two theorems will appear elsewhere
[Beu2]" (BP p. 127).  Waldspurger 2010 §6.1 proves
the corresponding identity `J(φ̂, f) = ∫ φ̂ θ_f` for the geometric side `J` of the local trace
formula on `𝔤`, not for the kernel integral.

**Coverage.**  Luo works over any `p`-adic or real field (from §5 on, p. 6) and every admissible
pair; Luo Thm 7.3.3 is proved by induction on `dim G` together with Thms 7.3.1, 7.3.2 (p. 46).  The
hypothesis that neither `W` nor `V` is a hyperbolic plane is added: otherwise `Ḡ` has the split
central torus `SO(W)` (resp. `SO(V)`) `≅ G_m`, which acts trivially on `𝔤` and freely on
`H̄(F)\Ḡ(F)` with non-compact orbits, so `J^Lie` (Luo §4: an integral over `H(F)\G(F)` with no
quotient by `A_G`) is `0` or divergent, and BP's integrals over `A_G(F)\G(F)` are not those
over `Ḡ(F)`.  With the hypothesis, `A_Ḡ = 1`.

**Caveats.**
* Luo's induction applies the three theorems to the smaller triples `(G'_X, H'_X)` of semisimple
  descent, and starts at `dim G = 1`, i.e. `SO(1) × SO(2)`; these can have a hyperbolic-plane factor,
  where Luo's `J` and `J^Lie` (no quotient by `A_G`) are `0` or divergent.  Luo does not say how this
  is handled (BP, for unitary groups, work modulo `A_G`).  The statement here is only used for
  triples without such a factor.
* Luo states no condition on the residue characteristic, and `PAdicField` allows `p = 2`.  His
  Appendix B (the regular germs used, through Lemma B.3.1, in the proof of Prop 7.3.7) refers to
  Waldspurger, Astérisque 269 (2001), parts of which assume the residue characteristic odd and the
  groups unramified.  Whether the steps Luo uses need that assumption has not been checked.
* Luo's article is a preprint (arXiv:2009.13947v1); for `p`-adic `F` it follows Waldspurger 2010,
  whose Thm 7.9 is the published `p`-adic statement closest to (d) (it is not the same statement).
* The sources fix the Haar measure on `Ḡ(F)` (BP §1.6).  The statement allows any Haar measure
  `μG`: for `μG = c · dg`, (b) holds with `c θ_f`, and both sides of (d) are multiplied by `c`.
* The quasi-character, germ and Fourier-transform notions are this project's definitions
  (`IsLieQuasiCharacter`, `germLie` with `jHat`, `selfDualHaar`); the orbits `O_ν` are
  `IsInOrbitNu` (Luo §2.1, Waldspurger 2010 §7.1). -/
theorem luo_lie_geomExpansion_SO {F : Type} [NontriviallyNormedField F] [PAdicField F]
    (L : LuoDatum F) (hW : ¬ IsHypPlane L.QW) (hV : ¬ IsHypPlane L.QV)
    (ψ : NontrivialAddChar F)
    (μG : Measure ↥L.Gbar) [μG.IsHaarMeasure]
    (μH : Measure ↥L.Hbar) [μH.IsHaarMeasure]
    (μ𝔥 : Measure ↥L.lieH) (h𝔥 : L.IsExpCompatH μH μ𝔥)
    (m : Measure (CosetSpace L.Hbar.subtype)) (hm : IsWeilMeasure L.Hbar.subtype μG μH m)
    (μT : ∀ T : L.GammaTorus, Measure ↥(L.lieTorus T.1))
    (hμT : ∀ T : L.GammaTorus, L.IsExpCompatT T.1 (μT T))
    (f : ↥L.lie → ℂ) (hf : L.IsScusp f) :
    ∃ θ : ↥L.lie → ℂ,
      -- (b) BP Thm 5.5.2(ii) with the Weyl integration formula (BP §1.7); Waldspurger 2010 §5.3, §6.1
      (LocallyIntegrable θ (L.measLie ψ) ∧
        ContinuousOn θ {X : ↥L.lie | IsRegularSS L.lie (X : L.Amb)} ∧
        ∀ f' : ↥L.lie → ℂ, IsTestFn f' →
          ∫ X, θ X * f' X ∂L.measLie ψ = L.orbitalPairing ψ μG f f') ∧
      -- (c) Waldspurger 2010 §6.1 Lemme (ii)
      IsLieQuasiCharacter L.Gbar L.lie L.traceForm ψ θ ∧
      -- (d) Luo Thm 7.3.3 with Prop 7.1.2(3)
      Tendsto (L.mGeomLieS ψ μT θ) (𝓝[>] (0 : ℝ)) (𝓝 (L.distribJLie ψ μ𝔥 m f)) := by
  sorry

end GSpinGGP
