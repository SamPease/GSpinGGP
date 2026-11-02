/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.SoCentralizer

/-!
# Orbit dimensions in `so(V)` over an algebraically closed field (cited)

Jantzen, *Nilpotent orbits in representation theory* (Progr. Math. 228, Birkhäuser 2004), for the
classical group `G = SO(V, φ)` over an algebraically closed field `K` with `char K ≠ 2` (§1.3).
In a basis, with `Φ` the (symmetric, invertible) matrix of `φ`,
`g = Lie G = {X ∈ M_n(K) | ᵗX Φ + Φ X = 0}` (§1.3 (3), in matrix form as in §7.7), the
skew-adjoint matrices `skewAdjointMatricesSubmodule Φ`. Here `n = dim V`; Jantzen's `n` is our
`n / 2`.

* `jantzen_finrank_soCentMat_ge`: every centralizer `g_X` has dimension at least `rk G = ⌊n/2⌋`.
-/

open Module

namespace GSpinGGP

/-- **Centralizers in `so(V)` have dimension at least the rank** (Jantzen 2004, §7.11,
Proposition and its proof, and the Remark after it, pp. 81–82: for `G = SO(V, φ)` as in
§7.6–7.7, the maximal dimension of a `G`-orbit in `g` is `2 dim n = dim G − rk G`; cf. §7.13,
Proposition, for any reductive `G`), combined with `dim O_X = dim G − dim G_X` (§2.1 (6)) and
`Lie(G_X) = g_X` in characteristic `0` (§2.2, condition (iii), "always satisfied if
`char(K) = 0`"; `dim G_X = dim Lie(G_X)`). Here `g_X = {Z ∈ g | [Z, X] = 0}` (§2.2 (3)) is
`soCentMat Φ X`, and `rk SO(V) = ⌊n/2⌋` for `n ≥ 3` (§6.3, last paragraph, with §6.4, first
sentence, pp. 64–65: `dim g_X = ⌊n/2⌋` for regular nilpotent `X`, and this equals `rk G`).

Specialization: `K` algebraically closed of characteristic `0` (Jantzen needs `char K ≠ 2`),
`V = K^n` with the form of the symmetric invertible matrix `Φ`; `n ≥ 3` as in §6.3. -/
axiom jantzen_finrank_soCentMat_ge {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    (hn : 3 ≤ n) (Φ : Matrix (Fin n) (Fin n) K) (hΦ : Φ.transpose = Φ) (hdet : Φ.det ≠ 0)
    (X : Matrix (Fin n) (Fin n) K) (hX : X ∈ skewAdjointMatricesSubmodule Φ) :
    n / 2 ≤ finrank K (soCentMat Φ X)

end GSpinGGP
