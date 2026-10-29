/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Basic

/-!
# The local trace formula for GGP triples (umbrella)

The local trace formula of Thesis Ch. 7–12 is split into:

* `TraceFormula/Basic.lean`: the objects — strongly cuspidal test functions `ScuspTestFn`, the
  kernel `kernelK`, the quotient `H(F)\G(F)/A_G(F)` with its Weil measure, the distribution
  `distribJ`, the orbital pairing and `thetaF`, the elliptic regular set;
* `TraceFormula/ThetaF.lean`: the theory of `θ_f` (existence, uniqueness, quasi-character
  property, `χ`-equivariant transfer);
* `TraceFormula/Analytic.lean`: the analytic estimates (kernel bounds, convergence of `J`,
  Harish-Chandra Schwartz spaces);
* `TraceFormula/SpinorNorm.lean`: the spinor norms and the Harish-Chandra map `H_G`;
* `TraceFormula/Interface.lean`: the shared definitions of the decomposition (`GeomAt`,
  `HYP`, `QC`, supports);
* `TraceFormula/MGeom.lean`, `Scusp.lean`, `Spectral.lean`, `Geometric.lean`, `Lie.lean`: the
  component statements (`m_geom` on quasi-characters; elliptic isolation and cuts; the spectral side;
  `J_qc` and localization away from `1`; the geometric expansion near `1`);
* `TraceFormula/Spine.lean`: the induction proving the multiplicity formula
  (Thesis Thm 7.2.2) from the geometric expansion (Thesis Thm 12.2.1) and the elliptic form of
  Thesis Prop. 7.4.1(ii), these being proved from the component statements.

This file only re-exports `TraceFormula/Basic.lean`.
-/
