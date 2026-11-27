# GSpinGGP

A Lean 4 + Mathlib formalization, **in progress**, of the local Gan–Gross–Prasad conjecture for
general spin groups over a p-adic field, following the PhD dissertation

> Samantha Pease, *The Local Gan-Gross-Prasad Conjecture for General Spin Groups*,
> Rutgers University–Newark, 2026. [doi:10.7282/t3-qb3s-s249](https://doi.org/10.7282/t3-qb3s-s249)

cited in the source as "Thesis". The proof adapts Beuzart-Plessis's local trace formula for
unitary groups (Astérisque 418) and Waldspurger's and Luo's work on special orthogonal groups.

**This is a work in progress.** The main theorem is stated and its proof is assembled, but it still
depends on unproved steps (`sorry`) and on results from the literature that are assumed as axioms.
See [Status](#status), and the **[blueprint](https://sampease.github.io/GSpinGGP/)**, whose
[dependency graph](https://sampease.github.io/GSpinGGP/blueprint/dep_graph_document.html) shows
every step of the proof coloured by formalization status.

## The main theorem

Let `W ⊂ V` be quadratic spaces over `F` with `V = W ⊕ Z`, `Z` split of odd dimension, and let
`(G, H, ξ)` be the associated GGP triple, `G = GSpin(W) × GSpin(V)`, with `G` quasi-split.
For a tempered irreducible representation `π` of `G(F)` write `m(π) = dim Hom_H(π, ξ)`.
Given tempered packets `Π_α` on the pure inner forms `G_α` that are stable, transfer to one another
with the Kottwitz sign, and are generic for every Whittaker datum (Thesis §6.3), exactly one
member `π` of `⊔_α Π_α` has `m(π) = 1`, and all others have `m(π) = 0` (Thesis Thm. 6.4.1).

In Lean (`GSpinGGP/Main.lean`):

```lean
theorem local_ggp (d : GGPData F) (hqs : d.IsQuasiSplit) (IF : InnerFormSystem d)
    (P : TemperedPacketFamily d IF) :
    (∃! p : Σ α : IF.Idx, P.ι α, mult ψ (IF.data p.1) (P.rep p.1 p.2) = 1) ∧
    ∀ p : Σ α, P.ι α, mult ψ (IF.data p.1) (P.rep p.1 p.2) = 1 ∨
      mult ψ (IF.data p.1) (P.rep p.1 p.2) = 0
```

The Langlands parameter is not modelled: the theorem is proved for every family of packets
satisfying the stability, transfer and genericity hypotheses, which is all the proof uses.

## Status

As of November 2026:

- The project builds with 44 declarations containing `sorry`. The main theorem `local_ggp`
  depends on 24 of them. They are of two kinds: the analytic core of the local trace formula
  (Thesis Ch. 8–12, e.g. the bound on the kernel of the distribution `J` and its spectral
  expansion), and published results that the dissertation adapts to general spin groups (see
  below), plus some smaller lemmas. A `sorry` is a step this project still owes.
- Results from the literature are assumed as `axiom`s in `GSpinGGP/Literature/`, each with a
  docstring citing its source; they are where the formalization stops, and are not meant to be
  proved here. `local_ggp` uses 28 of the 30. The other two are `exists_iwasawaPair_xi_sq_integrable`
  (Waldspurger 2003, Lemme II.1.5), intended as an input of the estimates of Thesis Ch. 8 and 10,
  and `tits_iwasawa_specialStab` (the Iwasawa decomposition for a special maximal compact subgroup
  in lattice form), intended for the existence of special presentations (`exists_specialK`).
  Among those used: `weyl_integration_exists` (the Weyl integration formula) and the three on
  Beuzart-Plessis's `θ_f` of a strongly cuspidal function, `waldspurger2010_lemme_5_3`,
  `waldspurger2010_cor_5_9` and `bp_thm_5_5_1_iv`, through `thetaF`, which is Beuzart-Plessis's
  formula for `θ_f`.
  That these axioms say what the sources say rests in part on two `sorry`s that are not on the path:
  `finite_parabolics` (so that the weight `v_M` in `θ_f` is not a junk value) and
  `exists_isCompact_conj_mem` (convergence of the orbital integrals).
  There are two classes.
  A *verbatim* axiom is a statement printed in its source, for the group the source treats,
  specialized (`bp_integrable_kernel_scusp`, `bp_thm_5_5_1_iv` and `weyl_integration_exists` are
  stated without proof in their sources).
  A *derived* axiom is a short, explicit combination of such statements, or a printed statement
  whose hypotheses are checked for our object in the docstring only; the docstring quotes the
  ingredients and gives the steps. 14 of the 30 are derived (`scripts/derived-axioms.txt`).
  They are the three on Galois cohomology (applied to groups of `F̄`-points whose description as algebraic
  groups, and for Kottwitz's lemma as a fundamental maximal torus, is argued in the docstring);
  `jantzen_finrank_soCentMat_ge` (four statements of Jantzen combined);
  `luo_lie_geomExpansion_SO` (Luo's theorem with properties of `θ_f` from Waldspurger and
  Beuzart-Plessis, one obtained from a theorem stated without proof by the Weyl integration formula);
  `waldspurger2010_thm_7_9` (Waldspurger's Lie-algebra integral formula for `(SO(V), SO(W))`,
  with his `θ_f`, which is not formalized, replaced by any function representing the orbital pairing
  of `f`; the link uses Beuzart-Plessis's expansion of the kernel, stated without proof in its
  source, and the Weyl integration formula);
  `tits_iwasawa` (the Iwasawa decomposition as stated by Tits, from the valuation of the root
  datum of Bruhat–Tits; the identification of Tits's `Z(F)U⁺(F)` with a stabilizer of full isotropic
  flags is our own step);
  `bp_sqrt_weylDisc_mul_locallyBounded` (BP's local boundedness of `(D^G)^{1/2} θ`, stated for
  connected reductive groups; that a quasi-character in our sense is one in BP's is checked in
  the docstring);
  `weyl_integration_exists` (the Weyl integration formula as printed by Beuzart-Plessis, without
  proof, for connected reductive groups, for some Haar measures on the maximal tori, together with
  the finiteness of each torus term of its right side for `|f|`, which is the formula for `|f|`
  read in `[0, ∞]` as Beuzart-Plessis reads it when deducing (1.7.1); the
  identification of maximal tori with centralizers of regular semisimple elements, and of the
  other objects, is written in the docstring; the author decided on it as a verbatim citation,
  and it is labelled derived because of these unfolding and identification steps);
  `exists_iwasawaPair_xi_sq_integrable` (Waldspurger's `∫_G Ξ² (1 + σ)^{-d} < ∞` for connected
  reductive groups; the identification of his special maximal compact subgroup, `Ξ`, and `σ` for a
  lattice basis of `C(W) × C(V)` with ours is written in the docstring);
  and three on `θ_f` for a strongly cuspidal `f ∈ C_c^∞(G(F))`, stated for every `θ` that equals
  Beuzart-Plessis's formula on the regular set for every presentation with a special maximal compact
  subgroup in lattice form (`IsBPThetaF`; the lattice form is Waldspurger 2010 §7.1–7.2, stated
  without proof there): `waldspurger2010_lemme_5_3` (Waldspurger 2010, Lemmes 5.2–5.3:
  independence of the special subgroup, conjugation invariance, local integrability),
  `waldspurger2010_cor_5_9` (Waldspurger 2010, Cor 5.9: `θ_f` is a quasi-character; that his
  quasi-characters are ours is checked in the docstring) and `bp_thm_5_5_1_iv` (Beuzart-Plessis
  Thm 5.5.1(iv), the geometric expansion of `J^A`, stated without proof in its source, for some
  Haar measures on the maximal tori; the measure on `A_G(F)` is Arthur's `d_c a`, not the
  exp-lifted one of Beuzart-Plessis's general rule, since it is the only one for which the
  formula can hold; the form for all Haar measures is a theorem). Their identification steps
  (`M(x)`, the special subgroup, the normalizations of `dg`) are written in the docstrings;
  `tits_iwasawa_specialStab` (`G = P K` for every `P ∈ 𝒫(M)`, with `K` the stabilizer, cut by
  `H_G = 0`, of special lattices of `W` and `V` adapted to `M`: Tits's and Waldspurger 2003's
  Iwasawa decomposition for the fixer of a special point, the latter stated without proof, applied
  through Waldspurger 2010 §7.1–7.2, stated without proof there, and the Bruhat–Tits
  identification of the buildings of `GSpin` and `SO`; every step is written in the docstring).
  The axioms on characters (Harish-Chandra, Beuzart-Plessis) and on multiplicity one (Pan Yan) are
  stated, as in their sources, for irreducible admissible smooth representations; the exception is
  `rodier_germ_one` (Rodier, Mœglin–Waldspurger), which is still stated for irreducible tempered
  unitary representations. The forms of the former for the unitary representations of the main
  theorem are proved, from Cartier's corollary of
  Bernstein's theorem (the smooth vectors of an irreducible unitary representation form a dense
  admissible representation) and Flath's tensor-product theorem, both verbatim axioms
  (`Foundations/SmoothRepresentations.lean`, `GGP/UnitaryCharacters.lean`,
  `GGP/MultOne.lean`).
  No axiom states for general spin groups a result that its source states for another group.
  Where the dissertation adapts a published result (stated for orthogonal or unitary groups, groups
  with compact centre, pure inner forms, …) or combines several, the statement is a theorem with
  `sorry`, and its docstring names the exact ingredients and sketches the argument.
- Definitions are never axiomatized. `GSpinGGP/Sanity/` checks key definitions on small cases
  (a few of these checks are hand computations recorded as `sorry` statements).
- Classical facts about quadratic forms (Witt cancellation and decomposition, Cartan–Dieudonné,
  the classification over `p`-adic fields) are proved from the
  [Tau Ceti](https://github.com/TauCetiProject/TauCeti) library, which this project depends on.
- Hilbert's Theorem 90 for `GL_m` is proved (`GGP/Hilbert90.lean`), from Mathlib's linear
  independence of characters, and from it Hilbert 90 for the units of a central simple algebra
  (`GGP/Hilbert90Units.lean`).
- Schur's lemma for irreducible unitary representations (Dixmier 13.1.4: the commutant is the
  scalars) is proved (`Foundations/UnitarySchur.lean`) from Tau Ceti's spectral theorem for
  bounded normal operators.

To see exactly what the main theorem rests on:

```lean
import GSpinGGP
#print axioms GSpinGGP.local_ggp
```

## Layout

| Folder | Contents |
|---|---|
| `Foundations/` | p-adic groups and their representations; `GSpin` via Clifford algebras; quadratic forms, and the links to Tau Ceti and Mathlib (local fields, the Lipschitz group) |
| `HarmonicAnalysis/` | group-agnostic harmonic analysis on locally compact groups (log-norms, BP §1.2; the function `Ξ^{H\G}` and polynomial growth, BP Prop 6.7.1(i),(iii),(iv)) |
| `GGP/` | GGP triples, inner forms, semisimple descent, Levi subgroups |
| `Literature/` | results assumed from the literature (Harish-Chandra, Waldspurger, Beuzart-Plessis, Arthur, Kottwitz, …) |
| `TraceFormula/` | quasi-characters, `θ_f`, `Γ(G)` and the Weyl integration formula, the distributions `J`, `J^A` and `J^Lie`, `m_geom`, spectral and geometric expansions |
| `Main.lean` | the multiplicity formula and the deduction of the main theorem |
| `Sanity/` | checks of definitions, and of the literature axioms (`Sanity/AxiomRedTeam.lean`), on small examples |

## Building

Requires [elan](https://github.com/leanprover/elan). The Lean version is pinned in
`lean-toolchain`; the project depends on a pinned commit of
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) (`lakefile.toml`), and Mathlib comes
through Tau Ceti at the commit recorded in `lake-manifest.json`.

```sh
bash scripts/get-cache.sh   # download prebuilt Mathlib and Tau Ceti
lake build
```

## How this was made

The Lean code was written by AI agents (Anthropic's Claude), directed by the
dissertation's author. Writing the formalization surfaced places where the dissertation's
statements needed adjusting; where a Lean statement deliberately differs from the dissertation,
its docstring says how.

## License

Apache 2.0, see [LICENSE](LICENSE).
