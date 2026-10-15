# An Arbor Polytope with Nonreal Ehrhart Roots

Lean sources accompanying [hexagon:2610.00235v1](https://hexagonmath.org/2610.00235v1), contributed by Yuran Xiu (IIIS, Tsinghua University).

The witness consists of two top vertices above one 180-leaf star and ten 5-leaf stars. It has 243 distinct singleton-labeled vertices. At every natural dilation m, including zero, the actual lattice count is

    (m+1)^230 (7m+2)^8
      (24+5852m+400056m^2+8533751m^3+44368122m^4+67184474m^5) / 6144.

The quintic has a nonreal root, certified by a negative Laguerre expression at -3/10. The result disproves the universal real-root assertion for arbor Ehrhart polynomials. It does not disprove the separate h*-root assertion or claim that this witness is smallest.

## Read the statement and proof

- `Challenge.lean` independently states the definitions and five claims in about 120 lines, importing only mathlib.
- `Solution.lean` exposes the corresponding proved declarations through `Audit.lean`; it never imports Challenge.
- `Arbor.lean` defines the actual subtree inequalities and proves a finite-deficit bijection.
- `Moments.lean` and `Count.lean` prove the count at every dilation.
- `ComplexFTA.lean` and `RootObstruction.lean` establish the nonreal-root certificate.
- `Main.lean` identifies the Ehrhart polynomial, proves its uniqueness, and gives the complete counterexample.
- `Audit.lean` states the explicit universal negation and verifies nonzero polynomial and endpoint axioms.

Palomar's independent Challenge contains deliberate statement placeholders (`sorry`). These are not proofs and do not occur in the Solution's imports or transitive proof dependencies. The proof development itself has no `sorry`, `admit`, `native_decide`, or postulated mathematical axiom. Comparator must match the separately compiled statements and accept only `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduce

Install the official elan toolchain manager, clone this repository, and run:

```sh
lake exe cache get
lake build
lake env lean Solution.lean
python3 verify.py
```

The toolchain and all dependencies are pinned in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. The GitHub Actions workflow invokes Palomar's complete mechanical verifier at an exact pipeline commit with `mode: full`; local compilation is not a substitute for that check or for registry review. A successful fresh proof build is saved in `verification/local-run/`; exact source hashes are in `SOURCES.json`. The checker rebuilds all eight proof-side modules separately and audits their transitive dependencies.

The original Lean 4.27.0 proof snapshot is preserved separately by the contributor. This repository ports it to Lean 4.35.0-rc3 and the matching mathlib revision. No original source snapshots are overwritten. The trust boundary includes Lean's kernel/compiler and pinned dependency proof objects; locally using mathlib caches does not independently rebuild the entire toolchain.

## Provenance and limitations

Mathematical development, source code and statement review used OpenAI Codex agents. The contributor reported that no parts had been checked and understood by a human. The formal code checks mathematical propositions; identifying the formal definitions with the informal source remains an explicitly documented AI assessment. No human peer review or exhaustive novelty/priority guarantee is claimed. See `formalization.yaml` for sources, attribution, automation and scope.

Code: Apache-2.0. The paper has its separate CC BY 4.0 license. Attribution for the adapted mathlib proof is retained in `ComplexFTA.lean` and `NOTICE`.
