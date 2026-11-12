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

- The project builds with 37 declarations containing `sorry`. The main theorem `local_ggp`
  depends on 21 of them. They are of three kinds: the analytic core of the local trace formula
  (Thesis Ch. 8–12, e.g. the bound on the kernel of the distribution `J` and its spectral
  expansion); published results that the dissertation adapts to general spin groups (see below);
  and 3 statements identifying the special orthogonal objects of a cited theorem (Luo's geometric
  expansion of `J^Lie`) with those of the general spin triple (`TraceFormula/LuoTransfer.lean`),
  plus some smaller lemmas. A `sorry` is a step this project still owes.
- Results from the literature are assumed as `axiom`s in `GSpinGGP/Literature/`, each with a
  docstring citing its source; they are where the formalization stops, and are not meant to be
  proved here. `local_ggp` uses 18 of the 19. There are two classes.
  A *verbatim* axiom is a statement printed in its source, for the group the source treats,
  specialized (one, `bp_integrable_kernel_scusp`, is stated without proof in its source).
  A *derived* axiom is a short, explicit combination of such statements, or a printed statement
  whose hypotheses are checked for our object in the docstring only; the docstring quotes the
  ingredients and gives the steps. 8 of the 19 are derived (`scripts/derived-axioms.txt`):
  the two on characters and the one on multiplicity one (sources state them for irreducible
  admissible smooth representations, the axioms for irreducible unitary ones);
  the three on Galois cohomology (applied to groups of `F̄`-points whose description as algebraic
  groups, and for Kottwitz's lemma as a fundamental maximal torus, is argued in the docstring);
  `jantzen_finrank_soCentMat_ge` (four statements of Jantzen combined);
  and `luo_lie_geomExpansion_SO` (Luo's theorem with properties of `θ_f` from Waldspurger and
  Beuzart-Plessis, one obtained from a theorem stated without proof by the Weyl integration formula).
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

To see exactly what the main theorem rests on:

```lean
import GSpinGGP
#print axioms GSpinGGP.local_ggp
```

## Layout

| Folder | Contents |
|---|---|
| `Foundations/` | p-adic groups and their representations; `GSpin` via Clifford algebras; quadratic forms, and the links to Tau Ceti and Mathlib (local fields, the Lipschitz group) |
| `GGP/` | GGP triples, inner forms, semisimple descent, Levi subgroups |
| `Literature/` | results assumed from the literature (Harish-Chandra, Waldspurger, Beuzart-Plessis, Arthur, Kottwitz, …) |
| `TraceFormula/` | quasi-characters, `θ_f`, the distributions `J` and `J^Lie`, `m_geom`, spectral and geometric expansions |
| `Main.lean` | the multiplicity formula and the deduction of the main theorem |
| `Sanity/` | checks of definitions on small examples |

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
