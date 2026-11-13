/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.AxiomRedTeam.Common
import GSpinGGP.Sanity.AxiomRedTeam.HarishChandra
import GSpinGGP.Sanity.AxiomRedTeam.Luo
import GSpinGGP.Sanity.AxiomRedTeam.Galois
import GSpinGGP.Sanity.AxiomRedTeam.Measure
import GSpinGGP.Sanity.AxiomRedTeam.WholeSystem
import GSpinGGP.Sanity.AxiomRedTeam.BPQuasiCharacter

/-!
# Checks of the literature axioms on small instances

A Lean axiom can be inconsistent, or say something other than its source, without any proof
failing.  The files imported here test each axiom of `GSpinGGP/Literature/` in one of three ways:

* **(V) verified**: an instance where the hypotheses hold and the conclusion is proved without the
  axiom;
* **(P) pinned**: the object the axiom provides is shown to equal an independently computed one;
* **(C) consistency**: the axiom's own instance, or two axioms together, agree with a computation
  done without them.

Most instances live on the toy datum `toyD` (`W = 0`, `V` a line, `G ≅ F^× × F^×`; see
`Sanity/Witnesses.lean`), so nonabelian groups, nonzero nilpotent orbits, proper parabolics and
nontrivial tori are **not** exercised.  No check depends on `sorry`.  A (V) check does not use
the axiom it tests; the computations of germs at `toyD` use `exists_isSelfDual` (the measure in
`ĵ(0, ·)`).  `local_ggp` does not import this file.

* `dixmier_commutant_scalar`: V (`scalar_of_C`), C (`triv2_not_irreducible_via_dixmier`). Not
  covered: infinite-dimensional `π`.
* `hc_regular_open_dense_conull`: V at `toyD` (`toyD_hc_regular_check`, `D^G ≡ 1`). Not covered:
  `G_reg ≠ G`.
* `hc_character_exists`: V at `toyD`, `π = 1` (`toyD_hc_character_exists_check`). Not covered:
  `π ≠ 1`.
* `hc_character_isQuasiCharacter`: V at `toyD`, `π = 1` (`toyD_hc_isQuasiCharacter_check`). Not
  covered: nonzero orbits.
* `emoryTakeda_mult_le_one`: V, sharp (`toyD_mult_eq_one_check`); C (`toyD_mult_trivialRep`). Not
  covered: `π ≠ 1`.
* `germ_unique`: V at `toyD`, every `θ` (`toyD_germ_unique`), nonvacuous; consequences on any datum
  (`false_of_orbitMeasure_eq`, `germ_unique_forces_jHat_ne_zero`). Not covered: several orbits.
* `rodier_germ_one`: V at `toyD`, `π = 1` (`toyD_rodier_trivialRep`); C
  (`toyD_charG_trivialRep_one`). Not covered: `π` without models.
* `waldspurger_goodNbhd`: C, smoke test (`toyD_goodNbhd_smoke`). Not covered: the exponential
  clause.
* `luo_lie_geomExpansion_SO`: V on the smallest Luo datum, all measures and `f`
  (`luo_conclusion_L0`). Not covered: nontrivial tori.
* `germLie_unique_SO`: V on the smallest Luo datum, every `θ` (`L0_germLie_unique`), nonvacuous
  (`L0_hasGermExpansionLie`); the hypothesis `X ∈ 𝔤` is needed
  (`L0_germLie_unique_needs_mem_lie`); consequences on any Luo datum
  (`false_of_orbitMeasure_eq_lie`, `germLie_unique_SO_forces_jHat_ne_zero`). Not covered: several
  orbits.
* `jantzen_finrank_soCentMat_ge`: V for `n = 3` (`jantzen_ge_three`). Not covered: `n ≥ 4`.
* `jantzen_regularNil_partition`: V for `n = 3`, `Φ` antidiagonal (`jantzen_partition_three`); C
  at `n = 4` with the previous axiom (`partition_four_via_axioms`). Not covered: `n ≥ 5`.
* `finite_H1_torusBar`: V for central `x` and `dim W = 0` (`finite_H1_torusBar_central`,
  `finite_H1_dim_zero`). Not covered: nontrivial tori.
* `finite_H1_normalizerBar`: V for `dim W = 0` (`finite_H1_dim_zero`). Not covered: `dim W > 0`.
* `exists_rel_torusBar_of_fixerBar`: V for central `x` (`exists_rel_central`). Not covered:
  noncentral `x`.
* `kottwitz_nilpotent_sq_smul`: V for `N = 0` and on `toyData` (`kottwitz_sq_smul_toy`). Not
  covered: `N ≠ 0`.
* `exists_isSelfDual`: hypothesis needed (`not_isSelfDual_zero`); P on the zero space. Not covered:
  `dim V > 0`.
* `weil_quotient_radon`: P for `S = Γ` (`weil_id_eq`), scaling (`weil_id_two`). Not covered: proper
  subgroups.
* `integral_eq_mul_integral_compact_integral`: V for `P = G`, `K = 1` (`integral_formula_top_bot`).
  Not covered: proper `P`.
* `bp_sqrt_weylDisc_mul_locallyBounded`: V at `toyD`, every quasi-character
  (`toyD_locallyBounded`); nonvacuous for `θ = 1`. Not covered: nonzero nilpotent orbits.
* `bp_integrable_kernel_scusp`: V when `A_G = G` (`bp_conclusion_of_AG_eq_top`, hyperbolic `V`,
  `toyD`). Not covered: `G/A_G` noncompact.

`WholeSystem.lean` also proves, at `toyD`, the conclusions of several `sorry` statements on the
path of the main theorem and the multiplicity formula for the trivial representation, with both
sides computed separately.
-/
