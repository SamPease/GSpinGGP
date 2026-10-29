/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Interface

/-!
# Inputs of the localization and semisimple descent (cited)

Intended content: the topology of quasi-characters and its
properties (BP §4.4, Prop 4.4.1), BP Cor 5.7.2(ii), BP Prop 4.8.1(ii), BP (2.7.2), BP Prop 5.7.1,
BP Lemmas 11.1.1–11.1.2, BP (3.2.5), (3.3.2), (11.1.2), and Arthur's local trace formula for the
triple `(G''_x, H''_x, 1)` (Arthur, Publ. IHÉS 73 (1991); Waldspurger 1995), each as an `axiom`
with its source.

Status: empty, on purpose.  The topology of `QC` is a definition
(`qcTopology`, `TraceFormula/Geometric.lean`), and in the `p`-adic case continuity of a linear form
is compact support, so BP Prop 4.4.1, Cor 5.7.2(ii), Prop 4.8.1(ii) and (2.7.2) are not needed for
`exists_isJqc`.  The descent inputs (BP (3.2.5), (11.1.2), Prop 5.7.1, Lemmas 11.1.1–11.1.2,
Prop 4.4.1(v), Arthur's local trace formula) are used only inside the SORRY
`exists_good_nhd_of_not_nearCentral`; they become axioms here when that statement is split.
-/
