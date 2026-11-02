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
`g = Lie G = {X ∈ M_n(K) | ᵗX Φ + Φ X = 0}` (§7.7), the skew-adjoint matrices
`skewAdjointMatricesSubmodule Φ`.

* `jantzen_finrank_soCentMat_ge`: every centralizer `g_X` has dimension at least `rk G = ⌊n/2⌋`.
-/

open Module

namespace GSpinGGP

/-- **Centralizers in `so(V)` have dimension at least the rank** (Jantzen 2004, §7.11, Remark
after the Proposition: for `G = SO(V, φ)` as in §7.6–7.7, the maximal dimension of a `G`-orbit in
`g` is `2 dim n = dim G − rk G`), combined with `dim O_X = dim G − dim G_X` (§2.1 (6)) and
`dim G_X = dim g_X` in characteristic `0` (§2.2, condition (iii), "always satisfied if
`char(K) = 0`"). Here `g_X = {Z ∈ g | [Z, X] = 0}` (§2.2 (3)) is `soCentMat Φ X` and
`rk SO(V) = ⌊n/2⌋` (`n = dim V`).

Specialization: `K` algebraically closed of characteristic `0`, `V = K^n` with the form of the
symmetric invertible matrix `Φ`; `n ≥ 3` as in Jantzen §6.3 for `SO(V, φ)`. -/
axiom jantzen_finrank_soCentMat_ge {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    (hn : 3 ≤ n) (Φ : Matrix (Fin n) (Fin n) K) (hΦ : Φ.transpose = Φ) (hdet : Φ.det ≠ 0)
    (X : Matrix (Fin n) (Fin n) K) (hX : X ∈ skewAdjointMatricesSubmodule Φ) :
    n / 2 ≤ finrank K (soCentMat Φ X)

end GSpinGGP
