/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.SpecialLattice

/-!
# The Iwasawa decomposition for the stabilizer of adapted special lattices

* **axiom** `tits_iwasawa_specialStab` (*derived*): for special lattices `R_W`, `R_V`
  (Waldspurger 2010, §7.1) adapted to the weight bases of a flag Levi datum `L`, and every
  `P ∈ 𝒫(M)`, `G(F) = P(F) · K` with `K = specialStab R_W R_V`.

It is used by `GGP/SpecialK.lean` (`exists_goodK_eq_specialStab`: the stabilizer is a `GoodK`).
It is the Iwasawa decomposition for a special maximal compact subgroup in good position (Tits,
Corvallis, 3.3.2; Waldspurger 2003, p. 240), applied to `K` through W1 §7.1–7.2 (stated there
without proof) and the Bruhat–Tits identification of special subgroups of `GSpin` with those of
`SO`.  Every step between the printed statements and the Lean statement is written out in the
docstring.

Checks: `Sanity/AxiomRedTeam/SpecialKIwasawa.lean`.
-/

noncomputable section

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **The Iwasawa decomposition `G = P K` for the stabilizer of adapted special lattices.**
A *derived* axiom: printed statements combined by identification steps (checking hypotheses,
relabelling), written out below.

**Lean statement.**  `L` a flag Levi datum, with Levi subgroup `M = L.M`; `S_W`, `S_V` special
lattices of `W` and `V` (`SpecialLattice`, W1 §7.1) adapted to `L`'s weight bases
(`SpecialLattice.IsAdapted`); `K = specialStab S_W S_V`, the `g` with `H_G(g) = 0` such that
`P(g)` stabilizes `R_W` and `R_V`.  Then for every `P ∈ 𝒫(M)` (`d.parabolics L.M`) every
`g ∈ G(F)` is `p k` with `p ∈ P`, `k ∈ K`.

**Printed ingredients.**
* (W1) J.-L. Waldspurger, *Une formule intégrale reliée à la conjecture locale de Gross–Prasad*,
  Compositio Math. 146 (2010), cited with the pagination of arXiv:0902.1875v1.
  - §1.1, arXiv p. 5 (definition of good position): "on dit que K est en bonne position
    relativement à M s'il existe un sous-tore déployé maximal A ⊂ M de sorte que K fixe un point
    spécial de l'appartement associé à A dans l'immeuble de G".  `F` is any non-archimedean
    field of characteristic `0`, with no restriction on the residue characteristic.
  - §7.1, arXiv pp. 33–34, for `G = SO(V)`, `V` any nondegenerate quadratic space: the special
    lattices `R = R_Z ⊕ R_an` (as in `SpecialLattice`), and "Pour un tel réseau R spécial, notons
    K le stabilisateur de R dans G(F). C'est un sous-groupe compact spécial de G(F)".
    **Stated there without proof.**
  - §7.2, arXiv pp. 34–35: `V = W' ⊕ D ⊕ Z` (`D` a line, `Z` hyperbolic of dimension `2r`,
    `2r + 1 ≤ d`), `V₀ = W' ⊕ D`, `A` the maximal torus of `SO(Z)` preserving each line `F v_i`
    of a maximal hyperbolic system of `Z`, `M = A·G₀` (`G₀ = SO(V₀)`) the Levi subgroup of the
    parabolic subgroup stabilizing the flag `F v_r ⊂ ⋯ ⊂ F v_r ⊕ ⋯ ⊕ F v_1`; "Remarquons que
    A_M = A, sauf dans le cas où V₀ est hyperbolique de dimension 2, auquel cas A_M = M".  For a
    special lattice `R₀` of `V₀` and `R_Z` with a basis proportional to the `v_i` such that
    `R = R₀ ⊕ R_Z` is special: "Le groupe K est en bonne position relativement à M"
    (`K = Stab(R)`).  **Stated there without proof.**
* (Tits) J. Tits, *Reductive groups over local fields*, in *Automorphic forms, representations
  and L-functions*, Proc. Sympos. Pure Math. 33, Part 1 (1979), 29–69.
  - 1.2, pp. 31–32: the apartment `A(G, S, K)` is an affine space under
    `X_*(S) ⊗ ℝ`, `Z(K)` acting by translations `ν(z)`, `χ(ν(z)) = −ω(χ(z))`; for `G` not
    semisimple it is "canonified" as `A(DG°, …) × X_*(S₀) ⊗ ℝ` (`S₀` the maximal split central
    torus), i.e. the extended apartment.
  - 2.1, pp. 43–44: "the building ℬ is canonically isomorphic with the direct product of the
    buildings ℬ(S₀, K) (which is an affine space) and ℬ(G_i, K)" (`G_i` the almost simple
    factors); "If G is K-anisotropic (i.e., if S = {1}), ℬ consists of a single point".
  - 1.9, p. 35: "The point x is called special … if every element of the root system Φ is
    proportional to some element of Φ_x, that is, if Φ and Φ_x have the same Weyl group"
    (`Φ_x`: vector parts of the affine roots vanishing at `x`).
  - 1.12, p. 38: "those data [the local Dynkin diagram and the index] are the same for G and for
    the adjoint group of G°"; for a product they are disjoint unions.
  - 3.1, p. 50: "The stabilizers G(K)^x of special (resp. hyperspecial) points x ∈ ℬ are called
    special (resp. hyperspecial) subgroups of G(K)."
  - 3.2, pp. 50–51: "If the residue field K̄ is finite, G(K)^Ω is even compact"; "special
    subgroups are maximal bounded subgroups".
  - 3.3, p. 51: "Let C be a chamber of A = A(G, S). We identify A with the vector space V in such
    a way that 0 becomes a special point contained in the closure of C; in particular, G(K)⁰ is a
    special subgroup of G(K). Set D = ℝ₊^* · C (a "vector chamber") … Let U⁺ be the group
    generated by all U_a for which a|_C — and hence a|_D — is positive".  3.3.2, p. 51:
    "Iwasawa decomposition. One has G(K) = G(K)⁰Z(K)U⁺(K)" (`Z = Z_G(S)`, `S` a maximal
    `K`-split torus; the bijection with `Y` stated there is not used).  Proofs: "cf. [8, §4]"
    (Bruhat–Tits I, Publ. IHÉS 41, Prop. 4.4.3; the valuation of the root datum exists for every
    connected reductive group over a discretely valued henselian field with perfect residue
    field by Bruhat–Tits II, Thm 5.1.20 and §5.1.1, as recorded for `tits_iwasawa`).
* (W2003) J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
  Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), p. 238: `A₀` a maximal split torus; "on dit
  que P est semi-standard si P ⊃ A₀".  p. 240: "On fixe un sous-groupe compact maximal K de G,
  dont on suppose qu'il est le fixateur d'un point spécial de l'appartement associé à A₀ dans
  l'immeuble de G. … Soit P = MU un sous-groupe parabolique semi-standard de G. Alors G = PK".
  **Stated there without proof** (the same decomposition as Tits 3.3.2, for all `P ⊇ A₀`).
* (BT II) F. Bruhat, J. Tits, *Groupes réductifs sur un corps local II*, Publ. IHÉS 60 (1984).
  - 4.2.15, pp. 93–94: "L'immeuble de G est invariant par épimorphisme central : soit G' un
    autre groupe algébrique défini sur K et soit j : G → G' un homomorphisme surjectif de noyau
    central. Alors … l'image S' = j(S) en est un tore K-déployé maximal" (the omitted words
    restate §4's quasi-split hypotheses, lifted by 5.1.20 Rem. 1 below); "il existe un
    isomorphisme et un seul de ℐ sur l'immeuble ℐ' de G' compatible avec les actions de G(K) et
    de G'(K) et envoyant φ sur φ'" (so it carries the apartment of `S` to that of `S'`).
  - 4.2.14, p. 93: the centre of `G(K)` acts trivially on `ℐ`.
  - 4.2.16, pp. 94–95: the extended building `ℐ¹ = ℐ × V¹`, `V¹` dual to `X_K(G) ⊗ ℝ`, `g` acting
    on `V¹` by `θ(g)`, `⟨θ(g), χ⟩ = −ω(χ(g))`; "le stabilisateur de ℐ pour l'action de G sur ℐ¹
    est le sous-groupe distingué G¹ = {g ∈ G(K) | ω(χ(g)) = 0 pour tout χ ∈ X_K(G)}"; "Si X est le
    stabilisateur (resp. fixateur) d'une partie M … de ℐ pour l'opération de G sur ℐ, alors
    X¹ [= X ∩ G¹] est le stabilisateur de M × {0} dans G pour l'opération de G sur ℐ¹".
  - 5.1.20, Remarques 1), p. 154: the theorem and the results on the building (5.1.21–28) hold
    without the smoothness hypothesis, "il suffit de considérer le morphisme canonique de G dans
    le groupe adjoint ad G (cf. 4.2.14 et 15)", the building being "le même pour G et ad G";
    this covers groups that are not quasi-split (here `d_an ∈ {3, 4}` occurs).  5.1.29, p. 157:
    the same for the extended building and `G¹`.
* (MT) G. Malle, D. Testerman, *Linear Algebraic Groups and Finite Groups of Lie Type*, Cambridge
  Stud. Adv. Math. 133 (2011), over an algebraically closed field `k` throughout (p. 3).
  Def. 6.3, p. 37: a Borel subgroup is "a closed, connected, solvable subgroup B of G which is
  maximal with respect to all these properties".  Def. 12.3, p. 97: "A parabolic subgroup of G is
  any subgroup containing a Borel subgroup".  Prop. 12.13, p. 101: "The parabolic subgroups of a
  simple classical group Cl(V) are precisely the subgroups of the form
  P = Stab_{Cl(V)}(0 ⊂ V₁ ⊂ … ⊂ V_r ⊂ V), where V_i is a totally isotropic (totally singular if
  V is equipped with a quadratic form) subspace of V"; `Cl(V)` is `SL(V)`, `Sp(V)` or `SO(V)`
  (p. 101).  The direction used here is the first paragraph of the proof, p. 102: "Given a flag
  F of totally singular subspaces, refine this to obtain a maximal flag inside a maximal totally
  singular subspace of V. By Witt's lemma (see [2, §20]), all maximal singular subspaces, and
  moreover all maximal flags inside a given maximal singular subspace are Isom(V)-conjugate. By
  the explicit constructions in Example 6.7, there exists a Borel subgroup of G stabilizing a
  maximal flag of a maximal singular subspace of V. So the stabilizer of F contains a Borel
  subgroup and hence is parabolic by Proposition 12.2".  That paragraph does not use simplicity
  (Prop. 12.2 asks only for `G` connected reductive), so it applies to `SO(V)` for every
  `dim V ≥ 2`.  Its Borel subgroups: Example 6.7(4), p. 39, `SO_{2n} ∩ T_{2n}` for every
  `n ≥ 1`, proved there; for `SO_{2n+1}`, "Analogously one shows …", left as Exercise 10.19(b),
  p. 77: **stated there without proof**.  (Conjugation by `Isom(V)` normalizes `SO(V)`, so it
  carries Borel subgroups to Borel subgroups.)
* (Milne) J. S. Milne, *Algebraic Groups* (course notes, version 2.00, 2015; preliminary
  version of the book, Cambridge 2017, whose numbering differs).
  - Thm 3.38 (Cartier), p. 62: "Every affine algebraic group over a field of characteristic
    zero is smooth".  Prop. 1.49, p. 29: "A surjective homomorphism φ: G → H of group varieties
    is smooth if and only if Ker(φ) is smooth".  Def. 5.7, p. 82: a quotient map is a faithfully
    flat homomorphism.  A.114(c), p. 511: "Products of complete schemes are complete".
  - §18 b, where "k is algebraically closed": Def. 18.10, a Borel subgroup is a maximal
    connected solvable subgroup variety; Thm 18.21, p. 317: "A subgroup variety P of G is
    parabolic if and only if it contains a Borel subgroup"; Prop. 18.24, p. 318 (`q : G → Q` a
    quotient map of connected group varieties), last paragraph of the proof: "Let H' be a
    parabolic subgroup of Q. Then H' contains a Borel subgroup B', which we can write B' = q(B)
    with B a Borel subgroup of G. Now H = q⁻¹(H') contains B, and so it is parabolic".
  - §18 f, over an arbitrary field: Def. 18.63, p. 329: "A parabolic subgroup of G is a subgroup
    variety such that G/P is complete.  Let k' be a field containing k; then an algebraic
    subgroup P of G is parabolic if and only if P_{k'} is parabolic in G_{k'}" (the second
    sentence **stated there without proof**).

**Steps** (`U` stands for `W` or `V`; `π = specP : GSpin(U) → SO(U)`).
1. *Hypotheses.*  A `PAdicField` is a complete, discretely valued, non-archimedean field of
   characteristic `0` with finite residue field, so W1, Tits §3 (§0.2, p. 30), BT II §5.1 and
   W2003 apply; `GSpin(U)`, `SO(U)` and `G = GSpin(W) × GSpin(V)` are connected reductive.
   `S_U` gives W1's data verbatim: the hyperbolic system `(v_i, v'_i) = (v_i, v_{−i})` for W1's
   bilinear form `polar Q` (W1's `q(v)` is `Q v`), `V_an = hypOrth`, anisotropic, and `c` with
   `|ϖ^c| = r` a value of `val_F ∘ q` on `V_an` (`attained`).  So `R_U = S_U.R` is a W1-special
   lattice, and `K_U := Stab_{SO(U)(F)}(R_U)` is a special subgroup of `SO(U)(F)` (W1 §7.1).
2. *Good position, and which torus.*  Let `A_U ⊆ SO(U)` be the torus of the whole hyperbolic
   system (`t_i` on `v_i`, `t_i⁻¹` on `v_{−i}`, `1` on `V_an`); it is a maximal split torus, as
   `V_an` is anisotropic.  Apply W1 §7.2:
   - if `V_an ≠ 0`: `Z` the span of the whole system (`r = n`), `V₀ = V_an`, `D` any line of
     `V_an` (anisotropic, so `q(D) ≠ 0`), `R₀ = R_an` (a special lattice of `V₀`: no hyperbolic
     part, same `c`), `R_Z = ⟨v_i, ϖ^c v_{−i}⟩`.  W1's `M` is `A_U · SO(V_an)`;
   - if `V_an = 0` and `n ≥ 1`: `r = n − 1`, `V₀` the plane of `v_{±n}`, `D = F(v_n + v_{−n})`,
     `W' = F(v_n − v_{−n})` (both anisotropic, `q = ±1`), `R₀ = ⟨v_n, ϖ^c v_{−n}⟩` (special for
     `V₀`), `R_Z = ⟨v_i, ϖ^c v_{−i}⟩_{i < n}`.  W1's `M` is `A_U` (the torus of `v_{±1..±(n−1)}`
     times `SO(V₀)`, a split torus of rank `1`);
   - if `n = 0` (`U` anisotropic) `SO(U)` is anisotropic, its building is a single point `y_U`
     (Tits 2.1), `SO(U)(F)` is compact and `K_U = SO(U)(F) = SO(U)(F)^{y_U}`.
   In each case `R_U = R₀ ⊕ R_Z`, and W1 §7.2 gives: `K_U` is in good position relative to W1's
   `M`, i.e. (W1 §1.1) fixes a special point `y_U` of the apartment of some maximal split torus
   `A' ⊆ M`.  Here `M` has a unique maximal split torus, namely `A_U`: in the first case
   `M = A_U × SO(V_an)` with `SO(V_an)` anisotropic, so `A' = A_M = A_U` (W1 §7.2: "A_M = A");
   in the second `M = A_U` is itself a split torus (W1 §7.2: "A_M = M").  So `y_U` lies in the
   apartment of `A_U`.  As `K_U ⊆ SO(U)(F)^{y_U}`, `K_U` is special, hence maximal bounded
   (Tits 3.2), and `SO(U)(F)^{y_U}` is bounded: `K_U = SO(U)(F)^{y_U}`.
3. *From `SO(U)` to `GSpin(U)` (identification through general Bruhat–Tits theory, for all
   reductive groups).*  `π : GSpin(U) → SO(U)` is surjective with central kernel `G_m`, so
   BT II 4.2.15 applies to it (5.1.20 Rem. 1 for non-quasi-split `U`): `GSpin(U)` and `SO(U)`
   have the same reduced building (that of `PSO(U)`), compatibly with `π`, and the same local
   Dynkin diagram, so
   the same special points (Tits 1.12, 1.9).  So the stabilizer of `y_U` in `GSpin(U)(F)` for the
   reduced building is the preimage of the reduced stabilizer in `SO(U)(F)`, and by BT II 4.2.16
   (5.1.29) the stabilizer of the point `x_U = (y_U, 0)` of the extended building `ℐ × V¹` is
   `π⁻¹(K_U) ∩ GSpin(U)(F)¹` (`K_U` is the reduced stabilizer cut by `SO(U)(F)¹`, and `π` maps
   `GSpin(U)(F)¹` into `SO(U)(F)¹`, since `χ ∘ π ∈ X_F(GSpin(U))` for every
   `χ ∈ X_F(SO(U))`).  When the semisimple part of `SO(U)` is anisotropic or trivial
   (`U` anisotropic, or `dim U ≤ 2`), the reduced buildings are points,
   `GSpin(U)(F)^{x_U} = GSpin(U)(F)¹`, and `π` maps it into the unique maximal bounded subgroup
   `K_U` of `SO(U)(F)`, so the formula `π⁻¹(K_U) ∩ GSpin(U)(F)¹` still holds.
   `GSpin(U)(F)¹ = {g : |χ(g)| = 1 ∀ χ ∈ X_F(GSpin(U))}` is `ker H` (`hcMap`; for `U` a hyperbolic
   plane `X_F` has rank `2` and `hcMap` uses both characters).  `x_U` is special (step 2 and
   Tits 1.12; the factor `V¹` = `X_*(S₀) ⊗ ℝ` does not enter Tits 1.9), and lies in the extended
   apartment of the maximal split torus `S_U` of `GSpin(U)` lying over `A_U` (the identity
   component of `π⁻¹(A_U)`, so that `π(S_U) = A_U`, consistently with BT II 4.2.15's
   `S' = j(S)`; Tits 1.2).
4. *Product.*  For `G = GSpin(W) × GSpin(V)` the (extended) building is the product (Tits 2.1),
   `x = (x_W, x_V)` is special (Tits 1.9, 1.12: the diagram of a product is the disjoint union),
   `S = S_W × S_V` is a maximal split torus of `G` with `x` in its apartment, `G(F)¹ = ker H_G`
   (`hcG`), and `G(F)^x = {g : H_G(g) = 0, π(g_W) ∈ K_W, π(g_V) ∈ K_V}`.  Since
   `latticeStab Q R = {k : π(k) R = R}`, this is `specialStab S_W S_V`.
5. *`P ⊇ S`* (W2003's "semi-standard").  `P ∈ 𝒫(M)` is `whittB F'_W F'_V`, the stabilizer of
   isotropic flags of `W` and `V`: the `F`-points of `π⁻¹(P_W) × π⁻¹(P_V)`, where
   `P_U = Stab_{SO(U)}(F'_U)` (stabilizing each member).  This is a parabolic subgroup of `G`.
   All group schemes here are smooth (characteristic `0`, Milne 3.38).  Over `F̄`, `U ⊗ F̄` is
   isometric to MT's standard form (nondegenerate quadratic forms of equal dimension over an
   algebraically closed field of characteristic `≠ 2` are isometric), `F'_U ⊗ F̄` is a flag of
   totally singular subspaces, and its stabilizer `P_{U,F̄}` contains a Borel subgroup (MT 12.13,
   first paragraph of the proof; MT's and Milne's Borel subgroups agree, MT 6.3 = Milne 18.10).
   If `dim U ≤ 1`, `SO(U)` is trivial and `P_U = SO(U)`.  So `P_{U,F̄}` is parabolic
   (Milne 18.21) and `P_U` is parabolic (Milne 18.63).  `π` is surjective with smooth kernel
   `G_m`, so `π` is smooth (Milne 1.49), hence flat and surjective, i.e. a quotient map
   (Milne 5.7); so `π⁻¹(P_U)` is parabolic in `GSpin(U)` (Milne 18.24 over `F̄`, then 18.63).
   Finally `G/(π⁻¹(P_W) × π⁻¹(P_V)) ≅ GSpin(W)/π⁻¹(P_W) × GSpin(V)/π⁻¹(P_V)` is complete
   (Milne A.114(c)), so the product is parabolic (Milne 18.63).
   And `M ⊆ P` (`IsLevi.le`).
   `S ⊆ M`: by `IsAdapted` each of the lines `F v_i`, `F v_{−i}` and the space `V_an` lies in a
   single weight space; since `U = ⊕ F v_i ⊕ F v_{−i} ⊕ V_an` (`SpecialLattice.sub_sum_mem_Van`)
   and `U = ⊕_w wtSpan w`, each weight space is the sum of the pieces it contains, so every
   element of `A_U` preserves each weight space, and every `g` with `π(g_U) ∈ A_U` lies in
   `flagLevi` (`mem_flagLevi_iff`).  So `S ⊆ π⁻¹(A_W × A_V) ⊆ M ⊆ P`.
6. *The decomposition.*  W2003 p. 240 with `A₀ = S`, `K = G(F)^x` the fixer of the special point
   `x` of the apartment of `A₀` (steps 3–4) and `P` semi-standard (step 5): `G(F) = P(F) K`.
   W2003's building is read as the extended one: W2003 calls its `K` a maximal *compact*
   subgroup, and a fixer in the reduced building contains the centre `Z_G(F)` (BT II 4.2.14),
   which is not compact when `A_G ≠ 1` (here `A_G ⊇ G_m × G_m`); the extended fixer `G(F)^x` is
   compact and, `x` being special, maximal bounded (Tits 3.2, for Tits's extended building).
   This step rests on W2003 alone.  For comparison only (not used): the same follows from Tits
   3.3.2, which also gives the proof reference: `P ⊇ S` contains a minimal
   parabolic subgroup `P₁ = Z U⁺ ⊇ S`, `U⁺` defined by a vector chamber `D` (concretely: each
   member of `F'_U` is `S`-stable, hence spanned by vectors `v_{±i}` — its intersection with
   `V_an` is isotropic, hence `0` — and refining it by these lines gives full flags whose
   stabilizer `P₁` lies in `P`; that this stabilizer contains `Z U⁺` for the corresponding
   ordering is the dictionary of `tits_iwasawa`, step 2, which W2003's form makes unnecessary).
   As `x` is special, the affine walls through `x` are the translates of all the vector walls
   (Tits 1.9), so the chamber `C` containing `x + εD` (small
   `ε > 0`) has `x` in its closure and `ℝ₊^* (C − x) = D`; Tits 3.3 with `0 := x` gives
   `G(F) = G(F)^x Z(F) U⁺(F) ⊆ K P₁(F)`.  Inverting, `G(F) = P₁(F) K ⊆ P(F) K`.
7. *The cut `H_G = 0` costs nothing.*  It is part of `G(F)^x` already: points of the extended
   building have stabilizers in `G(F)¹` (BT II 4.2.16), so Tits's and W2003's `K` lie in
   `ker H_G`.  Consistently, `g = p k` forces `H_G(g) = H_G(p)`, so the decomposition needs
   `H_G(P(F)) = H_G(G(F))`; this holds because `H_G(G(F)) = H_G(Z(F))` (3.3.2, with `K` and
   `U⁺(F)` in `ker H_G`) and `Z = Z_G(S) ⊆ M ⊆ P` (`Z` preserves the `S`-eigenspaces
   `F v_i`, `F v_{−i}`, `V_an`, hence every weight space, as in step 5).

Nothing here is a statement about `SO` carried over to `GSpin`: W1 §7.1–7.2 are used for
`SO(U)`, which is what they state, and the passage to `GSpin` and to the product is the general
Bruhat–Tits theory of steps 3–4.  The statement is the special case `P ⊇ S` of W2003 / Tits for
the particular special point `x`; it is no stronger than the print.  (If `attained` is dropped,
the statement can be false: in `SO(3) ≅ PGL₂` the lattice of `Sanity/GL2SpecialK.lean`'s
`gl2_iwahori_data` has as stabilizer the normalizer of an Iwahori subgroup, not special, and
`G ≠ B · I` for an Iwahori subgroup `I`: standard, not formalized here.) -/
axiom tits_iwasawa_specialStab (d : GGPData F) (L : d.FlagLeviDatum) (SW : SpecialLattice d.QW)
    (SV : SpecialLattice d.QV) (hW : SW.IsAdapted L.bW L.wtW) (hV : SV.IsAdapted L.bV L.wtV) :
    ∀ P ∈ d.parabolics L.M, ∀ g : ↥d.G, ∃ p ∈ P, ∃ k ∈ d.specialStab SW SV, g = p * k

end GSpinGGP
