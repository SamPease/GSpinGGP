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
import GSpinGGP.Sanity.AxiomRedTeam.Tits
import GSpinGGP.Sanity.AxiomRedTeam.BPQuasiCharacter
import GSpinGGP.Sanity.AxiomRedTeam.WaldspurgerXi
import GSpinGGP.Sanity.AxiomRedTeam.SmoothRepresentations
import GSpinGGP.Sanity.AxiomRedTeam.WaldspurgerLie
import GSpinGGP.Sanity.AxiomRedTeam.WeylIntegration
import GSpinGGP.Sanity.AxiomRedTeam.BPThetaF
import GSpinGGP.Sanity.AxiomRedTeam.SpecialKIwasawa

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

* `hc_regular_open_dense_conull`: V at `toyD` (`toyD_hc_regular_check`, `D^G ≡ 1`). Not covered:
  `G_reg ≠ G`.
* `hc_character_exists_admissible`: V at `toyD`, `ρ = 1^∞`
  (`toyD_hc_character_exists_admissible_check`), hypotheses hold (`toyD_smoothRep_trivial_irr_adm`).
  Not covered: `ρ ≠ 1`. The unitary form `hc_character_exists` (a theorem): V
  (`toyD_hc_character_exists_check`).
* `hc_character_isQuasiCharacter_admissible`: V at `toyD`, `ρ = 1^∞`
  (`toyD_hc_isQuasiCharacter_admissible_check`). Not covered: nonzero orbits.
* `panYan_mult_le_one`: V at `toyD`, `ρ₀ = ρ = 1` (`toyD_panYan_check`). Not covered: `ρ ≠ 1`. The
  unitary form `emoryTakeda_mult_le_one` (a theorem): V, sharp (`toyD_mult_eq_one_check`); C
  (`toyD_mult_trivialRep`).
* `cartier_smoothVectors_dense_admissible`: V at `toyD`, `π = 1` (`toyD_cartier_check`). Not
  covered: infinite-dimensional `π`.
* `flath_tensor_decomposition`: V for the trivial representation of any product
  (`flath_trivial_check`). Not covered: nontrivial representations.
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
* `waldspurger2010_thm_7_9`: C, junk values: `I_N` vanishes for `f = 0` or `θ = 0`, so
  the axiom forces `I(θ, τ) = 0` there (`Igeom_eq_zero_of_f_zero`, nonvacuous: `isVeryCuspidal_zero`,
  `isThetaFW1_zero`; `Igeom_zero_left`). Not covered: a constructed `W1Input` (special lattices,
  measures) with both sides computed.
* `jantzen_finrank_soCentMat_ge`: V for `n = 3` (`jantzen_ge_three`). Not covered: `n ≥ 4`.
* `jantzen_regularNil_partition`: V for `n = 3`, `Φ` antidiagonal (`jantzen_partition_three`); C
  at `n = 4` with the previous axiom (`partition_four_via_axioms`). Not covered: `n ≥ 5`.
* `finite_H1_torusBar`: V for central `x` and `dim W = 0` (`finite_H1_torusBar_central`,
  `finite_H1_dim_zero`). Not covered: nontrivial tori.
* `finite_H1_normalizerBar`: V for `dim W = 0` (`finite_H1_dim_zero`). Not covered: `dim W > 0`.
* `exists_rel_torusBar_of_fixerBar`: V for central `x` (`exists_rel_central`). Not covered:
  noncentral `x`.
* `tits_iwasawa`: V for anisotropic `W`, `V` (`tits_iwasawa_check_of_wittIndex_zero`), at `toyD`
  (`toyD_tits_iwasawa_check`); V for `V` a hyperbolic plane (`tits_iwasawa_check_of_isHypPlane_V`),
  at `hypVData` with a nonempty full flag (`hypVData_tits_iwasawa_check`). Not covered: proper
  `P₀`.
* `exists_iwasawaPair_xi_sq_integrable`: V at `toyD` (`toyD_exists_iwasawaPair_xi_sq_integrable`;
  hypotheses `toyD_xi_sq_integrable_hyps`): `Ξ ≡ 1` and `σ^{-4}` integrable by polynomial growth of
  `F^× × F^×`. Not covered: nonabelian `G`, proper `P₀`.
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
* `weyl_integration_exists`: V at `toyD`, the whole statement including the `[0, ∞]` convergence
  conjunct (`toyD_weyl_integration_exists_check`); an infinite atom `∞ · δ_x` is invisible to
  `toReal` but not to `lintegral` (`counterModel_toReal`, `counterModel_lintegral`: generic facts,
  no axiom), and the axiom excludes it from every torus term
  (`weylMeasureOn_ne_top_smul_dirac_of_axiom`, the one check that uses the axiom);
  with a genuine finite sum and integrable integrand (`toyD_summable_gammaIntegral`,
  `toyD_integrable_weylIntegrand`); Haar families exist on every datum
  (`isHaarMeasure_haarFamily`); junk values: the Haar conjunct is needed
  (`not_formula_zero_family`), and the axiom forces maximal tori to exist
  (`nonempty_maxTorusClass_of_axiom`), C with `hc_regular_open_dense_conull` and
  `jantzen_finrank_soCentMat_ge` (`nonempty_maxTorusClass`); it also forces a class with a finite
  Weyl group and a nonzero term (`exists_class_weylCardG_ne_zero_of_axiom`). Not covered (accepted):
  nonabelian `G`, `|W(G,T)| > 1`, `D^G ≠ 1`, several torus classes.
* `waldspurger2010_lemme_5_3`, `waldspurger2010_cor_5_9`, `bp_thm_5_5_1_iv`
  (`AxiomRedTeam/BPThetaF.lean`): V at `toyD`, the whole statements (`toyD_lemme_5_3_check`,
  `toyD_cor_5_9_check`, `toyD_bp_thm_5_5_1_iv_check`), with a special `K` built at `toyD`
  (`toyD_specialK_isSpecial`) so that the hypothesis `IsBPThetaF` is satisfiable
  (`toyD_isBPThetaF`) and pins `θ = c f` (`toyD_isBPThetaF_iff`, `toyD_not_isBPThetaF_add_one`);
  a wrong `IsSpecial` makes the hypothesis unsatisfiable (`not_isBPThetaF_of_not_exists`,
  `not_isBPThetaF_of_ne`), and `IsSpecial` excludes non-special `K` on `gl2Data`
  (`not_isSpecial_gl2GoodK'`, `not_exists_specialLattice_R_eq_iwahori`); `f = 0`
  (`bp_thm_5_5_1_iv_zero`); C, a joint model with `bp_integrable_kernel_scusp`
  (`toyD_joint_check`); `IsMx` unchanged under `L ↦ L.opp` (`IsMx.opp`). Off `toyD`, non-vacuity
  rests on the `sorry`s `exists_isMx`, `exists_specialK`. Owed: a proper-Levi `IsMx` at `gl2Data`,
  `thetaFBP` under `L ↦ L.opp`. Not covered: nonabelian `G`, `M ≠ G`, `v_M ≠ 1`.
* `tits_iwasawa_specialStab` (`AxiomRedTeam/SpecialKIwasawa.lean`): V for `M = G` on any datum
  (`tits_iwasawa_specialStab_check_of_M_eq_top`), at `toyD` with the hypotheses met
  (`toyD_tits_iwasawa_specialStab_check`), and at `gl2Data` for the diagonal torus `M` and every
  `P ∈ 𝒫(M)` (`gl2_tits_iwasawa_specialStab_check`: `specialStab = gl2K`, `gl2_iwasawa`); not
  applicable to the Iwahori lattice, excluded by `attained`
  (`gl2_tits_iwasawa_specialStab_not_iwahori`, nonvacuous: `gl2_iwahori_exclusion_nonvacuous`).
  Not covered: `d_an ≥ 2`, Witt index `≥ 2`.

`WholeSystem.lean` also proves, at `toyD`, the conclusions of several `sorry` statements on the
path of the main theorem and the multiplicity formula for the trivial representation, with both
sides computed separately.
-/
