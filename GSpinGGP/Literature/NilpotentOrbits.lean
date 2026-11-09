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
* `jantzen_regularNil_partition`: the Jordan type of a regular nilpotent element of `g`.
-/

open Module

namespace GSpinGGP

/-- **Centralizers in `so(V)` have dimension at least the rank** (Jantzen 2004, §7.13,
Proposition, p. 84: for reductive `G`, each regular orbit in `g` has dimension `2 dim n`, regular
meaning of maximal dimension; for `G = SO(V, φ)` as in §7.6–7.7 this is also §7.11, Remark after
the Proposition, pp. 81–82: the maximal dimension of a `G`-orbit in `g` is `2 dim n = dim G − rk G`),
combined with `dim O_X = dim G − dim G_X` (§2.1 (6)), `Lie(G_X) = g_X` in characteristic `0`
(§2.2, condition (iii), "always satisfied if `char(K) = 0`"), and `dim G_X = dim Lie(G_X)` (a
general fact about algebraic groups, not part of §2.2 (iii)). Here `g_X = {Z ∈ g | [Z, X] = 0}` (§2.2 (3)) is
`soCentMat Φ X`, and `rk SO(V) = ⌊n/2⌋` for `n ≥ 3` (§6.3, last paragraph, with §6.4, first
sentence, pp. 64–65: `dim g_X = ⌊n/2⌋` for regular nilpotent `X`, and this equals `rk G`).

Specialization: `K` algebraically closed of characteristic `0` (Jantzen needs `char K ≠ 2`),
`V = K^n` with the form of the symmetric invertible matrix `Φ`; `n ≥ 3` as in §6.3. -/
axiom jantzen_finrank_soCentMat_ge {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    (hn : 3 ≤ n) (Φ : Matrix (Fin n) (Fin n) K) (hΦ : Φ.transpose = Φ) (hdet : Φ.det ≠ 0)
    (X : Matrix (Fin n) (Fin n) K) (hX : X ∈ skewAdjointMatricesSubmodule Φ) :
    n / 2 ≤ finrank K (soCentMat Φ X)

/-- **Regular nilpotent elements of `so(V)` have partition `[n]` (`n` odd) or `[n − 1, 1]`
(`n` even)** (Jantzen 2004, §6.3, p. 64, last paragraph: for `G = SO(V, φ)` with `dim V ≥ 3`, the
regular nilpotent orbit in `so(V, φ)` consists of the nilpotent elements with partition `[2n + 1]`
when `dim V = 2n + 1`, and of those with partition `[2n − 1, 1]` when `dim V = 2n`. Jantzen
leaves the deduction from §3.2 (5) to the reader, and in the Remark after §6.4, p. 65, reduces it to
checking `dim g_X = rk G` for these partitions. The even case is stated again in §7.7, p. 78: "Let
`X ∈ g` be regular nilpotent. Then `X` has partition `[2n − 1, 1]`". Chapter 6 assumes `G ⊂ GL(V)` connected reductive, which `SO(V, φ)` is; partitions
are `GL(V)`-invariant, so working with `SO` rather than `O` does not affect the conclusion.)

Hypothesis. Jantzen calls `X` regular nilpotent if its orbit is dense in the nilpotent cone, and
shows in §6.3 that a nilpotent `X` is regular iff `dim G_X` is minimal among nilpotent elements
(by §2.1 (6)). In characteristic `0`, `Lie(G_X) = g_X` (§2.2, condition (iii)), and
`dim G_X = dim Lie(G_X)` (standard for algebraic groups), so `hreg`
(`dim g_X` minimal among nilpotent `Y ∈ g`) says that `X` is regular nilpotent.

Conclusion. The partition of a nilpotent `X` is the list of its Jordan block sizes (§1.1, §1.6),
so its largest part is the least `k` with `X^k = 0`. For an `n × n` nilpotent matrix, partition
`[n]` means `X^(n−1) ≠ 0`, and partition `[n − 1, 1]` means `X^(n−2) ≠ 0` and `X^(n−1) = 0`;
these are the two conjuncts below, with no loss.

Specialization: as for `jantzen_finrank_soCentMat_ge` (`K` algebraically closed of characteristic
`0`, `V = K^n` with the form of `Φ`, `n ≥ 3`). -/
axiom jantzen_regularNil_partition {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    (hn : 3 ≤ n) (Φ : Matrix (Fin n) (Fin n) K) (hΦ : Φ.transpose = Φ) (hdet : Φ.det ≠ 0)
    (X : Matrix (Fin n) (Fin n) K) (hX : X ∈ skewAdjointMatricesSubmodule Φ)
    (hnil : IsNilpotent X)
    (hreg : ∀ Y ∈ skewAdjointMatricesSubmodule Φ, IsNilpotent Y →
      finrank K (soCentMat Φ X) ≤ finrank K (soCentMat Φ Y)) :
    (Odd n → X ^ (n - 1) ≠ 0) ∧ (Even n → X ^ (n - 2) ≠ 0 ∧ X ^ (n - 1) = 0)

end GSpinGGP
