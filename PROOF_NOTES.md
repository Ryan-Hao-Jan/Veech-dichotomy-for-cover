# Proof notes

These notes describe how the formal proof of the compact branch
configuration theorem is organized. The main declaration is
`VeechDichotomy.PaperMainTheorem.main`; the orbit-closure version is
`VeechDichotomy.PaperMainTheorem.of_orbitClosure`.

## Mathematical objects

A translation surface is represented by a nonzero holomorphic differential
on a compact connected complex curve. A translation cover is a finite
surjective holomorphic map satisfying the pullback identity for the
differentials. Its branch values are defined from the critical points of
the map, and their finiteness is proved.

An ordered branch configuration is a tuple of points on the whole base
curve. Distinctness is expressed by injectivity of the tuple, so branch
values at zeros of the differential are allowed. The affine group acts on
all coordinates simultaneously.

Directional dynamics are defined on complete nonsingular trajectories.
The conclusion identifies every invariant probability measure with
normalized flat area. The existence and invariance of this area measure
are also proved.

## From lattice geometry to compact returns

The formal reduction begins with a dense complete orbit on the base,
obtained by projecting a minimal direction on the cover. Its contracting
Teichmüller ray is considered in the right quotient
$\operatorname{SL}(2,\mathbb R)/\Gamma$, where $\Gamma$ is the derivative group.

The lattice hypothesis yields a finite-area Dirichlet region. The geometric
development proves finiteness of its corners and ideal endpoints, constructs
parabolic elements at the ideal endpoints, and chooses compatible cusp
horoballs with compact complement. An escaping ray eventually lies in one
horoball. An explicit matrix calculation then gives a nonzero unipotent in
the derivative group fixing the contracted direction.

On a surface of genus at least two, the affine parabolic obstruction rules
out such an element in a direction with a dense complete orbit. Hence the
specified ray has arbitrarily late returns to a compact set. This supplies
the directional recurrence needed by the main theorem.

## Keeping the branch values apart

At the selected return times, write the normalized base matrices as
$A_n=H_{t_n}\gamma_n$ in a common compact set. Choose affine automorphisms
$\phi_n$ with derivatives $\gamma_n$. The corresponding branch tuples are
$\phi_n^{-1}(\mathbf b)$, which remain in the compact invariant set $F$.

The normalization tracks the base surface, the branch values and the cover
together. Compactness is developed through concrete local families of
curves and covers, with finite monodromy choices and varying marked points.
This produces a convergent family description along a subsequence of the
return times.

## Unique ergodicity on the cover

The family version of Masur's criterion uses the contraction of the tested
direction and the returning family to compare invariant measures in
translation charts. The argument identifies an arbitrary invariant
probability measure with normalized flat area. Direction changes are
handled by proved flow and measure equivalences.

`NativeCoverReturnErgodicity.uniquely_ergodic` applies this criterion to the
cover. `PaperCompactReturnReduction.strict_ergodicity_of_dense_returns`
combines it with the projected dense base orbit, and
`PaperMainTheorem.main` supplies the compact returns from the lattice
hypothesis.

## Guide to the main files

| Part of the argument | Entry points |
| --- | --- |
| Surfaces, covers and directional dynamics | [NativeSurface](VeechDichotomy/NativeSurface.lean), [NativeTranslationCover](VeechDichotomy/NativeTranslationCover.lean), [NativeDynamics](VeechDichotomy/NativeDynamics.lean) |
| Statement and branch configurations | [PaperStatement](VeechDichotomy/PaperStatement.lean), [Configuration](VeechDichotomy/Configuration.lean) |
| Pointwise lattice cusp theorem | [NativeLatticePointwiseCusp](VeechDichotomy/NativeLatticePointwiseCusp.lean) |
| Compact returns in a dense base direction | [NativeDenseDirectionReturns](VeechDichotomy/NativeDenseDirectionReturns.lean) |
| Returning families of covers | [NativeRayFamilyReturns](VeechDichotomy/NativeRayFamilyReturns.lean) |
| Family criterion and cover ergodicity | [NativeGeneralFamilyMasurCriterion](VeechDichotomy/NativeGeneralFamilyMasurCriterion.lean), [NativeCoverReturnErgodicity](VeechDichotomy/NativeCoverReturnErgodicity.lean) |
| Final assembly | [PaperCompactReturnReduction](VeechDichotomy/PaperCompactReturnReduction.lean), [PaperMainTheorem](VeechDichotomy/PaperMainTheorem.lean) |

The paper presents the cover compactness step through marked moduli and
Hurwitz spaces. The implementation works with explicit families of curves,
differentials and covers sufficient for the return argument. The lattice
recurrence and family criterion used in the proof are established within
the library.

## Verification and scope

`CheckMainTheorem.lean` rechecks the main declaration against both the
named proposition and an expanded formulation of Theorem 1. It also prints
the axioms used by the main theorem and the pointwise cusp theorem.
`CheckAxioms.lean` audits all project declarations and permits only
`propext`, `Classical.choice` and `Quot.sound`.

The completed target is the compact branch configuration criterion and its
orbit-closure version. For the torsion criterion, the library proves
general compactness and invariance lemmas for torsion-separated tuples;
it does not provide a complete formalization of the canonical period-torus
construction or the later polygonal examples.
