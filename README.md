# Veech dichotomy for branched covers

This repository formalizes the main theorem of Haoran Hu's paper,
*Veech dichotomy for specific covering surface over Veech surface*, in Lean.
It gives a sufficient condition for a finite translation cover of a Veech
surface to have a uniquely ergodic flow in every minimal direction.

**The main theorem is proved.** The proof is in
[PaperMainTheorem.lean](VeechDichotomy/PaperMainTheorem.lean), and the
mathematical definitions and statement are in
[PaperStatement.lean](VeechDichotomy/PaperStatement.lean).

## The theorem

Let $(X,\omega)$ be a compact Veech translation surface of genus at least
two, and let $\pi:(Y,\eta)\to(X,\omega)$ be a connected finite translation
cover, with $\eta=\pi^*\omega$. Write $\mathbf b$ for the ordered tuple of
distinct branch values of $\pi$.

Suppose that $\mathbf b$ belongs to a compact
$\operatorname{Aff}^+(X,\omega)$-invariant set

$$
F\subset\operatorname{Conf}_m(X).
$$

Here $\operatorname{Conf}_m(X)$ is the space of ordered tuples of $m$
distinct points of $X$.

Then every minimal direction on $Y$ is uniquely ergodic.

Equivalently, it is enough that the closure of the affine orbit of
$\mathbf b$ avoid the fat diagonal in $X^m$, the set of tuples with a repeated
coordinate. The two Lean entry points are:

- `VeechDichotomy.PaperMainTheorem.main`: the compact-configuration criterion.
- `VeechDichotomy.PaperMainTheorem.of_orbitClosure`: the orbit-closure formulation.

Here, minimality concerns complete nonsingular trajectories, and unique
ergodicity means that normalized flat area is the unique invariant
probability measure for the nonsingular flow.

## Build and verify

The project uses **Lean 4.35.0** and mathlib, with dependency versions recorded
in [lake-manifest.json](lake-manifest.json). Lean and Lake can be managed
through Elan; fetching dependencies also requires Git.

From the repository root, download the mathlib cache and build:

```sh
lake exe cache get
lake build
```

To check the theorem statement and audit proof dependencies:

```sh
lake env lean -DwarningAsError=true -DautoImplicit=false CheckMainTheorem.lean
lake env lean -DwarningAsError=true -DautoImplicit=false CheckAxioms.lean
```

With PowerShell, [Verify.ps1](Verify.ps1) runs the build and both checks,
and saves their output under `verification/`:

```powershell
./Verify.ps1
```

The cache download is needed only when the compiled dependencies are missing.

## What the checks establish

[CheckMainTheorem.lean](CheckMainTheorem.lean) checks both `MainClaim` and an
expanded version of Theorem 1 with the branch tuple and compact invariant
set written explicitly. [CheckAxioms.lean](CheckAxioms.lean) audits the
transitive dependencies of all project declarations, including the main
theorem. The only permitted foundational axioms are:

```text
propext
Classical.choice
Quot.sound
```

There are no added mathematical axioms or unfinished proofs (`sorry`) in
the audited dependencies. The saved results are summarized in
[MAIN-THEOREM-VERIFICATION.txt](MAIN-THEOREM-VERIFICATION.txt).

## Reading the code

For the overall argument, start with
[PROOF_NOTES.md](PROOF_NOTES.md). The final proof combines compact returns
for a base direction with compactness of the corresponding family of covers
and a family version of Masur's criterion.

```text
VeechDichotomy/       Definitions and proof modules
VeechDichotomy.lean   Imports the complete library
vendor/              Reused MNEC and Jacobians source modules
CheckMainTheorem.lean Statement checks and printed theorem assumptions
CheckAxioms.lean      Transitive axiom audit
Verify.ps1           Build and verification script
```

The verification target is Theorem 1 and its orbit-closure formulation.
The later torsion criterion and explicit polygonal examples are not claimed
as fully formalized here; the library does include supporting configuration
lemmas. Source provenance for reused and adapted modules is recorded in
[NATIVE-SOURCE-PROVENANCE.json](NATIVE-SOURCE-PROVENANCE.json) and
[ADAPTED-SOURCE-PROVENANCE.json](ADAPTED-SOURCE-PROVENANCE.json).
