/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Log-norms on topological groups (BP §1.2)

Beuzart-Plessis (*A local trace formula for the Gan-Gross-Prasad conjecture for unitary groups:
the archimedean case*, Astérisque 418, §1.2; Thesis §2.2) works with a log-norm `σ` on `G(F)`,
the logarithm of a Kottwitz norm, and only ever uses the following properties of it:
`σ ≥ 1`, `σ(xy) ≪ σ(x) + σ(y)`, `σ(x⁻¹) ∼ σ(x)`, and boundedness of `σ` on compact sets.
This file isolates these properties for an arbitrary topological group, so that the estimates
built on them (BP Ch. 6, 8) can be stated without reference to a particular reductive group.

## Main definitions

* `IsLogNorm σ`: `σ ≥ 1`, `σ(gh) ≤ σ(g) + σ(h)`, `σ(g⁻¹) = σ(g)`, and `σ` is bounded above on
  compact sets. (The concrete log-norms of the project are exactly subadditive and symmetric,
  so the predicate takes these with constant `1`; BP's `≪` and `∼` versions follow.)
* `infLeft σ S g = inf_{s ∈ S} σ(s g)`: the log-norm of `S\G` (BP (1.2.1)).
* `fiberInf σ π q = inf_{π g = q} σ(g)`: the push-forward `π_* σ` of BP §1.2, for any map
  `π : G → X` (used for `H(F)\G(F)/A_G(F)`).

## Main results

* `GroupSeminorm.isLogNorm_one_add`: `1 + f` is a log-norm for a group seminorm `f` that is
  bounded on compact sets (Mathlib's `GroupSeminorm`).
* `IsLogNorm.le_mul_add`: `σ(g) ≤ σ(gh) + σ(h)` (and the left version).
* `IsLogNorm.exists_mul_le_add`, `IsLogNorm.exists_le_mul_add`: right (and left) translation by
  a compact set changes `σ` by at most a constant: `|σ(gk) − σ(g)| ≤ C_K`.
* `IsLogNorm.add_le_mul`: `σ + C ≤ (1 + C) σ`, which turns the additive bounds into `∼`.
* `infLeft`: `1 ≤ σ_{S\G} ≤ σ`, left `S`-invariance, `σ_{S\G}(gh) ≤ σ_{S\G}(g) + σ(h)`; for normal
  `S`, `σ_{S\G}(gh) ≤ σ_{S\G}(g) + σ_{S\G}(h)` and `σ_{S\G}(g⁻¹) = σ_{S\G}(g)`.
* `fiberInf`: `1 ≤ π_*σ`, `π_*σ(π g) ≤ σ(g)`, and if right translation descends along `π`,
  `π_*σ(π(gh)) ≤ π_*σ(π g) + σ(h)`; upper semicontinuity when `π` is a quotient map whose
  fibres are the orbits of a group acting by homeomorphisms.
-/

open Set Topology

noncomputable section

namespace GSpinGGP

variable {G : Type*} [Group G] [TopologicalSpace G]

/-! ### The predicate -/

/-- A **log-norm** on a topological group `G` (BP §1.2; Thesis §2.2): `σ ≥ 1`, subadditive,
symmetric under inversion, and bounded above on compact sets. These are the properties of BP's
`σ_G` used in BP Ch. 6 and 8. (BP's `σ(xy) ≪ σ(x) + σ(y)` is stated up to a constant; the
log-norms of this project are exactly subadditive, and so is any `1 + f` for a group seminorm `f`,
see `GroupSeminorm.isLogNorm_one_add`.) -/
structure IsLogNorm (σ : G → ℝ) : Prop where
  one_le : ∀ g, 1 ≤ σ g
  mul_le : ∀ g h, σ (g * h) ≤ σ g + σ h
  inv_eq : ∀ g, σ g⁻¹ = σ g
  bddAbove_image : ∀ K : Set G, IsCompact K → BddAbove (σ '' K)

namespace IsLogNorm

variable {σ : G → ℝ} (hσ : IsLogNorm σ)
include hσ

omit hσ in
/-- A continuous function with the algebraic properties of a log-norm is a log-norm. -/
theorem of_continuous {τ : G → ℝ} (hc : Continuous τ) (h1 : ∀ g, 1 ≤ τ g)
    (hm : ∀ g h, τ (g * h) ≤ τ g + τ h) (hi : ∀ g, τ g⁻¹ = τ g) : IsLogNorm τ :=
  ⟨h1, hm, hi, fun _ hK => hK.bddAbove_image hc.continuousOn⟩

theorem nonneg (g : G) : 0 ≤ σ g := zero_le_one.trans (hσ.one_le g)

theorem pos (g : G) : 0 < σ g := zero_lt_one.trans_le (hσ.one_le g)

/-- `σ(g) ≤ σ(gh) + σ(h)` (subadditivity applied to `g = (gh)h⁻¹`). -/
theorem le_mul_add (g h : G) : σ g ≤ σ (g * h) + σ h := by
  have := hσ.mul_le (g * h) h⁻¹
  rwa [mul_inv_cancel_right, hσ.inv_eq] at this

/-- `σ(h) ≤ σ(gh) + σ(g)` (subadditivity applied to `h = g⁻¹(gh)`). -/
theorem le_mul_add' (g h : G) : σ h ≤ σ (g * h) + σ g := by
  have := hσ.mul_le g⁻¹ (g * h)
  rw [inv_mul_cancel_left, hσ.inv_eq] at this
  linarith

/-- `|σ(gh) − σ(g)| ≤ σ(h)`. -/
theorem abs_sub_le (g h : G) : |σ (g * h) - σ g| ≤ σ h :=
  abs_sub_le_iff.2 ⟨by linarith [hσ.mul_le g h], by linarith [hσ.le_mul_add g h]⟩

/-- `σ` is bounded on a compact set, by a nonnegative constant. -/
theorem exists_le_of_isCompact {K : Set G} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ k ∈ K, σ k ≤ C := by
  obtain ⟨C, hC⟩ := hσ.bddAbove_image K hK
  exact ⟨max C 0, le_max_right _ _, fun k hk => (hC ⟨k, hk, rfl⟩).trans (le_max_left _ _)⟩

/-- **Right translation by a compact set** changes `σ` by a bounded amount:
`σ(gk) ≤ σ(g) + C_K` and `σ(g) ≤ σ(gk) + C_K` for `k ∈ K` (BP §1.2, used throughout BP Ch. 6). -/
theorem exists_mul_le_add {K : Set G} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ g, ∀ k ∈ K, σ (g * k) ≤ σ g + C ∧ σ g ≤ σ (g * k) + C := by
  obtain ⟨C, hC0, hC⟩ := hσ.exists_le_of_isCompact hK
  exact ⟨C, hC0, fun g k hk => ⟨(hσ.mul_le g k).trans (by linarith [hC k hk]),
    (hσ.le_mul_add g k).trans (by linarith [hC k hk])⟩⟩

/-- **Left translation by a compact set** changes `σ` by a bounded amount. -/
theorem exists_mul_le_add' {K : Set G} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ g, ∀ k ∈ K, σ (k * g) ≤ σ g + C ∧ σ g ≤ σ (k * g) + C := by
  obtain ⟨C, hC0, hC⟩ := hσ.exists_le_of_isCompact hK
  exact ⟨C, hC0, fun g k hk => ⟨(hσ.mul_le k g).trans (by linarith [hC k hk]),
    (hσ.le_mul_add' k g).trans (by linarith [hC k hk])⟩⟩

/-- `σ + C ≤ (1 + C) σ` for `C ≥ 0`, since `σ ≥ 1`: additive bounds give BP's `≪`. -/
theorem add_le_mul {C : ℝ} (hC : 0 ≤ C) (g : G) : σ g + C ≤ (1 + C) * σ g := by
  nlinarith [hσ.one_le g]

/-- **Two-sided translation by a compact set**, in BP's multiplicative form: there is `c ≥ 1`
with `σ(k g k') ≤ c σ(g)` for `k, k' ∈ K` (so `σ(k g k') ∼ σ(g)` uniformly on `K × K`). -/
theorem exists_mul_mul_le_mul {K : Set G} (hK : IsCompact K) :
    ∃ c, 1 ≤ c ∧ ∀ g, ∀ k ∈ K, ∀ k' ∈ K, σ (k * g * k') ≤ c * σ g := by
  obtain ⟨C, hC0, hC⟩ := hσ.exists_le_of_isCompact hK
  refine ⟨1 + 2 * C, by linarith, fun g k hk k' hk' => ?_⟩
  calc σ (k * g * k') ≤ σ k + σ g + σ k' :=
        (hσ.mul_le _ _).trans (by linarith [hσ.mul_le k g])
    _ ≤ σ g + 2 * C := by linarith [hC k hk, hC k' hk']
    _ ≤ (1 + 2 * C) * σ g := hσ.add_le_mul (by linarith) g

end IsLogNorm

/-- If `f` is a group seminorm on `G` (Mathlib's `GroupSeminorm`) that is bounded on compact
sets, then `1 + f` is a log-norm. (The log-norm `1 + log max(1, ‖g‖, ‖g⁻¹‖)` of a linear group is
of this form.) -/
theorem GroupSeminorm.isLogNorm_one_add (f : GroupSeminorm G)
    (hf : ∀ K : Set G, IsCompact K → BddAbove (f '' K)) : IsLogNorm fun g => 1 + f g where
  one_le g := le_add_of_nonneg_right (apply_nonneg f g)
  mul_le g h := by linarith [map_mul_le_add f g h]
  inv_eq g := by rw [map_inv_eq_map f g]
  bddAbove_image K hK := by
    obtain ⟨C, hC⟩ := hf K hK
    exact ⟨1 + C, by rintro _ ⟨k, hk, rfl⟩; linarith [hC ⟨k, hk, rfl⟩]⟩

/-! ### Log-norms of `S\G` (BP (1.2.1)) -/

section InfLeft

/-- The log-norm of `S\G` attached to `σ` (BP (1.2.1)): `σ_{S\G}(g) = inf_{s ∈ S} σ(s g)`. -/
def infLeft (σ : G → ℝ) (S : Subgroup G) (g : G) : ℝ := ⨅ s : S, σ ((s : G) * g)

variable {σ : G → ℝ} (hσ : IsLogNorm σ) (S : Subgroup G)
include hσ

theorem IsLogNorm.bddBelow_infLeft (g : G) : BddBelow (range fun s : S => σ ((s : G) * g)) :=
  ⟨1, by rintro _ ⟨s, rfl⟩; exact hσ.one_le _⟩

/-- `σ_{S\G} ≥ 1`. -/
theorem IsLogNorm.one_le_infLeft (g : G) : 1 ≤ infLeft σ S g :=
  le_ciInf fun _ => hσ.one_le _

/-- `σ_{S\G}(g) ≤ σ(s g)` for `s ∈ S`. -/
theorem IsLogNorm.infLeft_le_of_mem {s : G} (hs : s ∈ S) (g : G) : infLeft σ S g ≤ σ (s * g) :=
  ciInf_le (hσ.bddBelow_infLeft S g) ⟨s, hs⟩

/-- `σ_{S\G} ≤ σ`. -/
theorem IsLogNorm.infLeft_le (g : G) : infLeft σ S g ≤ σ g := by
  simpa using hσ.infLeft_le_of_mem S S.one_mem g

/-- `σ_{S\G}` is left `S`-invariant. -/
theorem IsLogNorm.infLeft_mul_left {s : G} (hs : s ∈ S) (g : G) :
    infLeft σ S (s * g) = infLeft σ S g := by
  apply le_antisymm
  · refine le_ciInf fun t => ?_
    have := hσ.infLeft_le_of_mem S (S.mul_mem t.2 (S.inv_mem hs)) (s * g)
    rwa [mul_assoc, inv_mul_cancel_left] at this
  · refine le_ciInf fun t => ?_
    have := hσ.infLeft_le_of_mem S (S.mul_mem t.2 hs) g
    rwa [mul_assoc] at this

/-- `σ_{S\G}(gh) ≤ σ_{S\G}(g) + σ(h)`. -/
theorem IsLogNorm.infLeft_mul_le (g h : G) : infLeft σ S (g * h) ≤ infLeft σ S g + σ h := by
  rw [← sub_le_iff_le_add]
  refine le_ciInf fun s => ?_
  rw [sub_le_iff_le_add]
  calc infLeft σ S (g * h) ≤ σ ((s : G) * (g * h)) := hσ.infLeft_le_of_mem S s.2 _
    _ ≤ σ ((s : G) * g) + σ h := by rw [← mul_assoc]; exact hσ.mul_le _ _

/-- `σ_{S\G}(g) ≤ σ_{S\G}(gh) + σ(h)`. -/
theorem IsLogNorm.infLeft_le_mul_add (g h : G) : infLeft σ S g ≤ infLeft σ S (g * h) + σ h := by
  have := hσ.infLeft_mul_le S (g * h) h⁻¹
  rwa [mul_inv_cancel_right, hσ.inv_eq] at this

/-- **Right translation by a compact set** changes `σ_{S\G}` by a bounded amount. -/
theorem IsLogNorm.exists_infLeft_mul_le_add {K : Set G} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ g, ∀ k ∈ K,
      infLeft σ S (g * k) ≤ infLeft σ S g + C ∧ infLeft σ S g ≤ infLeft σ S (g * k) + C := by
  obtain ⟨C, hC0, hC⟩ := hσ.exists_le_of_isCompact hK
  exact ⟨C, hC0, fun g k hk => ⟨(hσ.infLeft_mul_le S g k).trans (by linarith [hC k hk]),
    (hσ.infLeft_le_mul_add S g k).trans (by linarith [hC k hk])⟩⟩

/-- For a normal subgroup `S`, `σ_{S\G}` is subadditive. -/
theorem IsLogNorm.infLeft_mul_le_add [S.Normal] (g h : G) :
    infLeft σ S (g * h) ≤ infLeft σ S g + infLeft σ S h := by
  rw [← sub_le_iff_le_add]
  refine le_ciInf fun s => ?_
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add']
  refine le_ciInf fun t => ?_
  rw [sub_le_iff_le_add']
  -- `s g t h = (s (g t g⁻¹)) (g h)` with `s (g t g⁻¹) ∈ S`.
  have hmem : (s : G) * (g * (t : G) * g⁻¹) ∈ S :=
    S.mul_mem s.2 (‹S.Normal›.conj_mem _ t.2 g)
  calc infLeft σ S (g * h) ≤ σ ((s : G) * (g * (t : G) * g⁻¹) * (g * h)) :=
        hσ.infLeft_le_of_mem S hmem _
    _ = σ ((s : G) * g * ((t : G) * h)) := by group
    _ ≤ σ ((s : G) * g) + σ ((t : G) * h) := hσ.mul_le _ _

/-- For a normal subgroup `S`, `σ_{S\G}(g⁻¹) = σ_{S\G}(g)`. -/
theorem IsLogNorm.infLeft_inv [S.Normal] (g : G) : infLeft σ S g⁻¹ = infLeft σ S g := by
  have key : ∀ x : G, infLeft σ S x ≤ infLeft σ S x⁻¹ := by
    intro x
    refine le_ciInf fun s => ?_
    -- `(s x⁻¹)⁻¹ = x s⁻¹ = (x s⁻¹ x⁻¹) x`
    have hmem : x * (s : G)⁻¹ * x⁻¹ ∈ S := ‹S.Normal›.conj_mem _ (S.inv_mem s.2) x
    calc infLeft σ S x ≤ σ (x * (s : G)⁻¹ * x⁻¹ * x) := hσ.infLeft_le_of_mem S hmem x
      _ = σ ((s : G) * x⁻¹)⁻¹ := by group
      _ = σ ((s : G) * x⁻¹) := hσ.inv_eq _
  exact le_antisymm (by simpa using key g⁻¹) (key g)

/-- For a normal subgroup `S`, `σ_{S\G}` is again a log-norm on `G` (constant on `S`-cosets). -/
theorem IsLogNorm.isLogNorm_infLeft [S.Normal] : IsLogNorm (infLeft σ S) where
  one_le := hσ.one_le_infLeft S
  mul_le := hσ.infLeft_mul_le_add S
  inv_eq := hσ.infLeft_inv S
  bddAbove_image K hK := by
    obtain ⟨C, hC⟩ := hσ.bddAbove_image K hK
    exact ⟨C, by rintro _ ⟨k, hk, rfl⟩; exact (hσ.infLeft_le S k).trans (hC ⟨k, hk, rfl⟩)⟩

end InfLeft

/-! ### Push-forward of a log-norm along a map (BP §1.2, `f_* σ_X`) -/

section FiberInf

/-- The push-forward of `σ` along `π : G → X` (BP §1.2): `(π_* σ)(q) = inf_{π g = q} σ(g)`
(this is `0`, a junk value, off the image of `π`). -/
def fiberInf {X : Type*} (σ : G → ℝ) (π : G → X) (q : X) : ℝ := ⨅ g : {g : G // π g = q}, σ g

variable {X : Type*} {σ : G → ℝ} (hσ : IsLogNorm σ) (π : G → X)
include hσ

theorem IsLogNorm.bddBelow_fiberInf (q : X) : BddBelow (range fun g : {g : G // π g = q} => σ g) :=
  ⟨1, by rintro _ ⟨g, rfl⟩; exact hσ.one_le _⟩

/-- `π_* σ (π g) ≤ σ(g)`. -/
theorem IsLogNorm.fiberInf_le (g : G) : fiberInf σ π (π g) ≤ σ g :=
  ciInf_le (hσ.bddBelow_fiberInf π _) ⟨g, rfl⟩

/-- `π_* σ ≥ 1` on the image of `π`. -/
theorem IsLogNorm.one_le_fiberInf (g : G) : 1 ≤ fiberInf σ π (π g) :=
  have : Nonempty {g' : G // π g' = π g} := ⟨⟨g, rfl⟩⟩
  le_ciInf fun _ => hσ.one_le _

/-- `π_* σ ≥ 1` when `π` is surjective. -/
theorem IsLogNorm.one_le_fiberInf_of_surjective (hπ : Function.Surjective π) (q : X) :
    1 ≤ fiberInf σ π q := by
  obtain ⟨g, rfl⟩ := hπ q
  exact hσ.one_le_fiberInf π g

/-- If right translation by `h` descends along `π` (`π g = π g' → π (g h) = π (g' h)`), then
`π_* σ (π (g h)) ≤ π_* σ (π g) + σ(h)`. -/
theorem IsLogNorm.fiberInf_mul_le {h : G} (hπ : ∀ g g', π g = π g' → π (g * h) = π (g' * h))
    (g : G) : fiberInf σ π (π (g * h)) ≤ fiberInf σ π (π g) + σ h := by
  have : Nonempty {g' : G // π g' = π g} := ⟨⟨g, rfl⟩⟩
  rw [← sub_le_iff_le_add]
  refine le_ciInf fun g' => ?_
  rw [sub_le_iff_le_add, ← hπ _ _ g'.2]
  exact (hσ.fiberInf_le π _).trans (hσ.mul_le _ _)

/-- If right translations descend along `π`, then `π_* σ (π g) ≤ π_* σ (π (g h)) + σ(h)`. -/
theorem IsLogNorm.fiberInf_le_mul_add {h : G}
    (hπ : ∀ g g', π g = π g' → π (g * h⁻¹) = π (g' * h⁻¹)) (g : G) :
    fiberInf σ π (π g) ≤ fiberInf σ π (π (g * h)) + σ h := by
  have := hσ.fiberInf_mul_le π hπ (g * h)
  rwa [mul_inv_cancel_right, hσ.inv_eq] at this

/-- **Right translation by a compact set** changes `π_* σ` by a bounded amount, when right
translations descend along `π`. -/
theorem IsLogNorm.exists_fiberInf_mul_le_add
    (hπ : ∀ h g g', π g = π g' → π (g * h) = π (g' * h)) {K : Set G} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ g, ∀ k ∈ K, fiberInf σ π (π (g * k)) ≤ fiberInf σ π (π g) + C ∧
      fiberInf σ π (π g) ≤ fiberInf σ π (π (g * k)) + C := by
  obtain ⟨C, hC0, hC⟩ := hσ.exists_le_of_isCompact hK
  exact ⟨C, hC0, fun g k hk => ⟨(hσ.fiberInf_mul_le π (hπ k) g).trans (by linarith [hC k hk]),
    (hσ.fiberInf_le_mul_add π (hπ k⁻¹) g).trans (by linarith [hC k hk])⟩⟩

/-- **Upper semicontinuity of `π_* σ`.** Let `σ` be continuous and `π` a quotient map whose
fibres are the orbits of a family of homeomorphisms `φ i` of `G` (e.g. `g ↦ h g a` for
`H\G/A`). Then `π_* σ` is upper semicontinuous, hence Borel measurable. -/
theorem IsLogNorm.upperSemicontinuous_fiberInf [TopologicalSpace X] (hπ : IsQuotientMap π)
    (hc : Continuous σ) {ι : Type*} (φ : ι → G → G) (hφ : ∀ i, Continuous (φ i))
    (hfib : ∀ g g', π g = π g' ↔ ∃ i, g' = φ i g) : UpperSemicontinuous (fiberInf σ π) := by
  intro q c hqc
  -- the set `{q | π_* σ q < c}` is open: its preimage is a union of preimages of `{σ < c}`
  have hopen : IsOpen {q | fiberInf σ π q < c} := by
    rw [← hπ.isOpen_preimage]
    have : π ⁻¹' {q | fiberInf σ π q < c} = ⋃ i, φ i ⁻¹' {g | σ g < c} := by
      ext g
      simp only [mem_preimage, mem_ofPred_eq, mem_iUnion]
      constructor
      · intro hg
        have : Nonempty {g' : G // π g' = π g} := ⟨⟨g, rfl⟩⟩
        obtain ⟨⟨g', hg'⟩, hlt⟩ := exists_lt_of_ciInf_lt hg
        obtain ⟨i, rfl⟩ := (hfib g g').1 hg'.symm
        exact ⟨i, hlt⟩
      · rintro ⟨i, hi⟩
        have := (hfib g (φ i g)).2 ⟨i, rfl⟩
        exact (this ▸ hσ.fiberInf_le π (φ i g)).trans_lt hi
    rw [this]
    exact isOpen_iUnion fun i => (isOpen_lt hc continuous_const).preimage (hφ i)
  exact Filter.mem_of_superset (hopen.mem_nhds hqc) fun _ h => h

end FiberInf

end GSpinGGP
