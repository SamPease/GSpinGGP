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

As of October 2026:

- The project builds with 29 declarations containing `sorry`. The main theorem `local_ggp`
  depends on 18 of them: 7 are the analytic core of the local trace formula (Thesis Ch. 8–12,
  e.g. convergence of the distribution `J` and its spectral expansion), the rest smaller lemmas.
- Results from the literature are assumed as `axiom`s in `GSpinGGP/Literature/`, each with a
  docstring citing its source. `local_ggp` uses 28 of the 31. Several are adapted to general
  spin groups from statements in the literature for unitary or special orthogonal groups; their
  docstrings say how.
- Definitions are never axiomatized. `GSpinGGP/Sanity/` checks key definitions on small cases.
- Classical facts about quadratic forms (Witt cancellation and decomposition, Cartan–Dieudonné,
  the classification over `p`-adic fields) are proved from the
  [Tau Ceti](https://github.com/TauCetiProject/TauCeti) library, which this project depends on.

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
