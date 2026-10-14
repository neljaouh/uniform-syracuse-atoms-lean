# Lean proofs for uniform Syracuse atoms and density regularity

This independent Lean project contains the source needed to check the named
results of *Uniform Syracuse atoms and exact density regularity with
quantitative Collatz predecessor counts*. The corresponding manuscript has
SHA-256 `553ca2aa8dc2a0924ae89590e022c8e61975e2964bc391f82e525f3e6cbd0745`.
The paper source and unrelated research files are outside this repository.

The Lean version is pinned in `lean-toolchain`; Mathlib and its dependencies
are pinned in `lake-manifest.json`. From this directory, run:

```sh
lake exe cache get
lake build CheckPaper AuditProofs CheckMainTheorems
```

`CheckPaper` checks 47 named proposition contracts and their transitive axiom
dependencies. `AuditProofs` checks the manuscript's proof namespace. The
permitted logical axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Passing these checks does not replace a mathematical review of the
correspondence between the manuscript and the formal statements.
The release-folder check on 14 October 2026 completed successfully with
the pinned toolchain and a prebuilt dependency cache: 47 paper contracts
passed, and `AuditProofs` checked 1,746 declarations, including 1,443
theorems. A new checkout should run the commands above to rebuild locally.

The `SyracuseReport` modules hold the paper-specific proofs. The
`Erdos1135` modules are the local source closure for the published
fine-scale mixing input; their public-release origins and checksums are
recorded in `source-origins.json`. Four retained local source versions differ
from their archived extraction; that record gives both checksums. Retained
upstream rights and notices are
in `NOTICE.mixing-source` and `notices/M2/`. Mathlib is fetched by Lake and is
not redistributed here. Build artifacts under `.lake/` are excluded from Git.
