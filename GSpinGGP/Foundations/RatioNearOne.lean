/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Ratios near `1`

In a normed field, if `p = c q` with `p` and `q` both close to `n ≠ 0`, then `c` is close to `1`
(`exists_mem_nhds_eq_mul_imp_mem`), and the same componentwise on `K × K`.
-/

open Topology Filter

namespace GSpinGGP

/-- If `p = c q` with `p, q` close to `n ≠ 0`, then `c` is close to `1`. -/
theorem exists_mem_nhds_eq_mul_imp_mem {K : Type*} [NormedField K] {n : K} (hn : n ≠ 0)
    {U : Set K} (hU : U ∈ 𝓝 (1 : K)) :
    ∃ N ∈ 𝓝 n, ∀ p ∈ N, ∀ q ∈ N, ∀ c : K, p = c * q → c ∈ U := by
  have hc : ContinuousAt (fun pq : K × K => pq.1 / pq.2) (n, n) :=
    continuousAt_fst.div continuousAt_snd hn
  have hpre : (fun pq : K × K => pq.1 / pq.2) ⁻¹' U ∈ 𝓝 (n, n) :=
    hc.preimage_mem_nhds (by simpa [div_self hn] using hU)
  obtain ⟨N₁, hN₁, N₂, hN₂, hsub⟩ := mem_nhds_prod_iff.1 hpre
  refine ⟨N₁ ∩ N₂ ∩ {q | q ≠ 0}, inter_mem (inter_mem hN₁ hN₂) (isOpen_ne.mem_nhds hn),
    fun p hp q hq c hpq => ?_⟩
  have h := hsub (Set.mk_mem_prod hp.1.1 hq.1.2)
  simp only [Set.mem_preimage] at h
  rwa [hpq, mul_div_assoc, div_self hq.2, mul_one] at h

/-- `exists_mem_nhds_eq_mul_imp_mem` on `K × K`, componentwise. -/
theorem exists_mem_nhds_eq_mul_imp_mem_prod {K : Type*} [NormedField K] {n : K × K}
    (hn₁ : n.1 ≠ 0) (hn₂ : n.2 ≠ 0) {U : Set (K × K)} (hU : U ∈ 𝓝 (1 : K × K)) :
    ∃ N ∈ 𝓝 n, ∀ p ∈ N, ∀ q ∈ N, ∀ c : K × K, p = c * q → c ∈ U := by
  rw [show (1 : K × K) = ((1 : K), (1 : K)) from rfl] at hU
  obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := mem_nhds_prod_iff.1 hU
  obtain ⟨N₁, hN₁, h₁⟩ := exists_mem_nhds_eq_mul_imp_mem hn₁ hU₁
  obtain ⟨N₂, hN₂, h₂⟩ := exists_mem_nhds_eq_mul_imp_mem hn₂ hU₂
  refine ⟨N₁ ×ˢ N₂, prod_mem_nhds hN₁ hN₂, fun p hp q hq c hpq => hsub ⟨?_, ?_⟩⟩
  · exact h₁ p.1 hp.1 q.1 hq.1 c.1 (congrArg Prod.fst hpq)
  · exact h₂ p.2 hp.2 q.2 hq.2 c.2 (congrArg Prod.snd hpq)

end GSpinGGP
