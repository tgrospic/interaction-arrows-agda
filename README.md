# agda-collab

Agda experiments, plus a local checkout of Conal Elliott's Agda corpus for reading alongside them.

The context is [conal/Collaboration](https://github.com/conal/Collaboration), where Conal describes what he looks for in collaborators and mentees: formalizing questions in a proof assistant, then hunting for the simplest possible specification before an efficient implementation. His `learning-agda.md` recommends Jesper Cockx's *Programming and Proving in Agda*, part one of [PLFA](https://plfa.github.io/), and Wadler's *Propositions as Types*. His own repos are where the denotational design ideas actually live in Agda.

## Layout

| Path | What it is |
| --- | --- |
| `agda-collab.agda-lib` | Project root marker. One include root (`.`), so every module is named by its path. Depends on `standard-library`. |
| `essay/` | `essay_v01.agda`, an indexed command monad for an essay workflow, plus `essay.idr`, the Idris original it came from. |
| `scratch/` | Version-numbered experiments: `pico`, `essay_v02`..`v06`, `maybe_v01`..`v02`, `rust_v01`..`v03`. All named `scratch.*`. |
| `external/` | Conal's repos, cloned by the fetch script. Gitignored. |
| `scripts/fetch-conal.sh` | Clones his eight Agda repos and registers the library ones with Agda. |
| `_build/` | Interface files, one tree per Agda version. Gitignored. |

`external/` is not committed. None of Conal's repos carries a LICENSE file, so this repo links to his work and fetches it on demand rather than vendoring copies of it.

```
./scripts/fetch-conal.sh              # clone + register
WITH_CATEGORIES=1 ./scripts/fetch-conal.sh   # also clone the agda-categories fork
```

## Conal's Agda corpus

Found by cloning all 121 of his public repos and scanning for `.agda` and `.lagda` files, rather than by trusting GitHub's primary-language field. That field misses three repos where the Agda sits beside TeX, one of which is the largest single body of his Agda after felix.

Eleven repos he authored. Five more contain Agda but are forks of other people's work, listed separately below and excluded from every count here.

| Repo | What it is | Files | Lines | Checks clean | Notes |
| --- | --- | ---: | ---: | ---: | --- |
| [felix](https://github.com/conal/felix) | Category theory library built for denotational design. Raw/Laws/Homomorphism layering, comma and product constructions, instances for functions, setoids and predicates. | 29 | 3918 | 29/29 | Needs only the standard library. The centerpiece. |
| [paper-2021-language-derivatives](https://github.com/conal/paper-2021-language-derivatives) | The Agda behind his language derivatives paper: languages as predicates, calculus of derivatives, decidability, symbolic and automatic representations. | 22 | 3859 | 7/22 | Written against a 2021 standard library. Most failures are `Not in scope` from the `Function` reorganization since. |
| [agda-cat-linear](https://github.com/conal/agda-cat-linear) | Linear map categories: biproducts, inductive matrices, semiring-as-category. | 14 | 2169 | 0/14 | Depends on his `agda-categories` fork, which requires `standard-library-2.4`. |
| [felix-boolean](https://github.com/conal/felix-boolean) | Boolean structure layered on felix. Two modules are literate TeX. | 6 | 478 | 6/6 | Requires `felix` registered first. |
| [agda-play](https://github.com/conal/agda-play) | Miscellaneous experiments, including `Perfect` (perfect binary trees) and `Misc`. | 5 | 403 | 2/5 | Three files duplicate `DependentTypesAtWork-exercises`; two byte-identical, `Lambda` diverges. |
| [DependentTypesAtWork-exercises](https://github.com/conal/DependentTypesAtWork-exercises) | Worked exercises: balanced trees, sorted trees, sorting, vectors by recursion. | 5 | 329 | 4/5 | `Lambda.agda` defines `_⟶_`, which now clashes with `Function.Bundles`. |
| [equation-transfer](https://github.com/conal/equation-transfer) | Transferring equational properties backward through homomorphisms. Small and directly on-theme. | 1 | 85 | 1/1 | |
| [nim](https://github.com/conal/nim) | The game of Nim, with well-founded recursion on board order. | 1 | 67 | 0/1 | `acc` made its `y` argument implicit in newer stdlib, so `rs _ p` passes one argument too many. `rs p` fixes it. |
| [agda-puzzles](https://github.com/conal/agda-puzzles) | Tower of Hanoi as a reachability relation over configurations. | 1 | 52 | 0/1 | Ends on `A↝C` with no definition. The puzzle is the point. |
| [talk-2023-galilean-revolution](https://github.com/conal/talk-2023-galilean-revolution) | Talk sources, one literate module. | 1 | 7 | 1/1 | |
| [agda-latex](https://github.com/conal/agda-latex) | Literate TeX scaffolding. | 1 | 7 | 1/1 | Depends on felix. |
| **Total** | | **86** | **11374** | **51 files** | |

Forks, cloned only with `WITH_FORKS=1`: `agda-stdlib` (1044 files), `agda-categories` (536), `cheshire` (16, checks clean), `blag` (7), `jespercockx-agda-lecture-notes` (1, the notes his reading list recommends).

### Coverage

Checked with Agda 2.6.4.3 and standard-library 2.1.

| Measure | Runnable | Corpus | Share |
| --- | ---: | ---: | ---: |
| Files | 51 | 86 | **59.3%** |
| Lines | 5540 | 11374 | **48.7%** |

Nothing that fails here fails because his code is wrong. The gap is three causes:

* **Standard library drift**, the dominant one. The 2021 paper repo (3859 lines) and `nim` were written against a much older stdlib, and names have moved since. Expect this to get *worse*, not better, on stdlib 2.4.
* **A missing dependency.** `agda-cat-linear` (2169 lines) needs `agda-categories`, which wants `standard-library-2.4`.
* **A deliberate hole.** `agda-puzzles` leaves its theorem unproved.

Read `felix` first. At 3918 lines it is over a third of the corpus, it checks 29/29 against a plain standard library, and it is the direct expression of the denotational design ideas the collaboration is about. `equation-transfer` is the smallest thing on-theme, at 85 lines.

## Toolchain

Agda finds the standard library through a registry file, not a search path:

```
~/.config/agda/libraries    one absolute path to an .agda-lib per line
~/.config/agda/defaults     library names loaded without an explicit depend
```

Two behaviors worth knowing, both learned the hard way here:

* **The nearest `.agda-lib` above a file defines its project**, which sets the include roots and puts interfaces in `_build/<version>/agda/`. A checkout placed underneath this repo would inherit *this* project unless it carries its own `.agda-lib`. That is why `external/conal-examples.agda-lib` exists for the repos that ship without one.
* **Agda takes the include set from the current working directory, not from the file being checked.** Checking `external/felix/src/Felix/All.agda` from the repo root fails on module resolution; `cd external/felix` first and it succeeds.

On Agda 2.7 and later, `agda --build-library` type-checks everything under the include roots in one command. On 2.6.x, loop over the files.

## Status of the experiments here

5 of 12 modules check: `scratch/pico`, `scratch/essay_v03`, `scratch/maybe_v02`, `scratch/rust_v01`, `scratch/rust_v03`.

The `essay_*` failures share one cause. `EssayCmd` is indexed by `Set`-valued states, so the datatype lands in `Set₁` and its constructors no longer fit:

```
Set₁ is not less or equal than Set
when checking that the type Set of an argument to the constructor
pure fits in the sort Set of the datatype.
```

Making the state index a small enumeration instead of `Set` should clear the family at once. The rest are unsolved metas (`essay_v02b`, `maybe_v01`) and an ambiguous instance (`rust_v02`).
