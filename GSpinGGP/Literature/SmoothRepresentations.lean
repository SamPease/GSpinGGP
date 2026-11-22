/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups
import GSpinGGP.Foundations.GSpin
import GSpinGGP.Foundations.SmoothRepresentations

/-!
# Cited results on smooth representations: Cartier (Bernstein), Flath

Two results from the Corvallis proceedings (*Automorphic forms, representations and
L-functions*, Proc. Sympos. Pure Math. 33, Part 1, AMS 1979) that connect the unitary
representations in the statement of the main theorem with the irreducible admissible smooth
representations for which Harish-Chandra, Beuzart-Plessis and Pan Yan state their results.

## Contents
* `cartier_smoothVectors_dense_admissible` — Cartier, *Representations of p-adic groups: a
  survey*, §2.7, Corollary 2.3 (resting on Bernstein 1974, Thm 1): the smooth vectors of an
  irreducible unitary representation are dense and form an admissible representation.
* `flath_tensor_decomposition` — Flath, *Decomposition of representations into tensor
  products*, Theorem 1 (1.2): an irreducible admissible representation of `G₁ × G₂` is an
  external tensor product.

The algebraic irreducibility of `π^∞` is proved from Corollary 2.3, not assumed
(`isIrreducible_smoothRep`, `Foundations/SmoothRepresentations`).
-/

open MeasureTheory Topology

noncomputable section

namespace GSpinGGP

universe u v

/-- **Cartier, Corollary 2.3** (P. Cartier, *Representations of p-adic groups: a survey*, PSPUM 33
Part 1 (1979), §2.7, p. 133): "Let `(π, V)` be any irreducible unitary representation of `G`. Let
`V_∞` be the space of vectors in `V` stable by `π(K)` for some compact open subgroup `K` of `G`.
Then `V_∞` is dense in `V` and stable under `G`, hence affords a smooth representation `π_∞` of
`G`. The representation `(π_∞, V_∞)` is admissible." Here (Cartier §2.1) `F` is a local field and
`G` a connected reductive algebraic group over `F`, identified with its group of `F`-points; the
corollary follows from Bernstein's
bound (Cartier Thm 2.8 and its proof via Thm 2.7; I. N. Bernstein, *All reductive p-adic groups
are tame*, Funct. Anal. Appl. 8 (1974), 91–93, Thm 1).

Specialized to `G = GSpin(W) × GSpin(V)` (`↥d.G`). `V_∞` is `smoothVectors π`, the vectors with
open stabilizer; in the locally profinite group `↥d.G` this is the same set, since every open
subgroup contains a compact open one (van Dantzig). Stability under `G` is built into
`smoothRep π` (a subrepresentation). -/
axiom cartier_smoothVectors_dense_admissible {F : Type*} [NontriviallyNormedField F]
    [PAdicField F] (d : GGPData F) (π : UnitaryRep ↥d.G) (hπ : π.IsIrreducible) :
    Dense (smoothVectors π : Set π.H) ∧ (smoothRep π).IsAdmissible

/-- **Flath, Theorem 1 (1.2)** (D. Flath, *Decomposition of representations into tensor
products*, PSPUM 33 Part 1 (1979), pp. 179–183, Theorem 1, p. 179): "Let `G₁`, `G₂` be locally
compact totally disconnected groups and let `G = G₁ × G₂`. … (1.2) If `π` is an admissible
irreducible representation of `G`, then there exist admissible irreducible representations `πᵢ`
of `Gᵢ` such that `π ≃ π₁ ⊗ π₂`." Representations are complex; `π₁ ⊗ π₂` is the external tensor
product, `(g₁, g₂) ↦ π₁(g₁) ⊗ π₂(g₂)` (Tau Ceti's `Representation.externalTensor`).

Only the existence half of (1.2) is stated (not the uniqueness of the classes of the `πᵢ`), and
the factors are taken in the universe of `V`; this is no loss, since `V₁` and `V₂` embed in `V`
(`v₁ ↦ v₁ ⊗ v₂` for a fixed `v₂ ≠ 0`). A totally disconnected topological group is Hausdorff. -/
axiom flath_tensor_decomposition {G₁ G₂ : Type u} [Group G₁] [TopologicalSpace G₁]
    [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [TotallyDisconnectedSpace G₁] [Group G₂]
    [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂]
    [TotallyDisconnectedSpace G₂] {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (G₁ × G₂) V) (hirr : ρ.IsIrreducible) (hadm : ρ.IsAdmissible) :
    ∃ (V₁ V₂ : Type v) (_ : AddCommGroup V₁) (_ : Module ℂ V₁) (_ : AddCommGroup V₂)
      (_ : Module ℂ V₂) (ρ₁ : Representation ℂ G₁ V₁) (ρ₂ : Representation ℂ G₂ V₂),
      ρ₁.IsIrreducible ∧ ρ₁.IsAdmissible ∧ ρ₂.IsIrreducible ∧ ρ₂.IsAdmissible ∧
        Nonempty (Representation.Equiv ρ (ρ₁.externalTensor ρ₂))

end GSpinGGP
