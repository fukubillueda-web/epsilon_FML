# Langlands’s First Main Lemma

A Lean 4 formalization of Langlands’s First Main Lemma for local epsilon factors over nonarchimedean local fields, in mixed and equal characteristic.

## Theorem

The exported declaration is [`LanglandsFirstMainLemma.firstMainLemma`](LanglandsFirstMainLemma/Main.lean). The proof is local and covers cyclic extensions of prime degree.

## Papers and proof guide

- [Companion mathematical paper (TeX)](references/epsilon_FML.tex)
- [Published release and manuscript files](https://github.com/fukubillueda-web/epsilon_FML/releases/tag/v1.0.0)
- [Source map](SOURCE_MAP.md), [dependency graph](DEPENDENCY_GRAPH.dot), and [mathematical blueprint](blueprint/src/print.tex)

## Reproduce the proof

Install Git, Python 3, and [elan](https://github.com/leanprover/elan). Then run:

```bash
git clone https://github.com/fukubillueda-web/epsilon_FML.git
cd epsilon_FML
git checkout v1.0.0
bash FIRST_RUN_MAC.command
bash scripts/VERIFY_PUBLICATION.command
```

Despite its name, `FIRST_RUN_MAC.command` also works in a Unix shell on Linux. It obtains the available Mathlib cache and runs the full project checks. `VERIFY_PUBLICATION.command` additionally audits the axioms of the exported theorem and checks the stored proof terms with `leanchecker --fresh`.

The release pins **Lean 4.32.2** and **Mathlib `905b95818eb32af7874a58b427f50c1711a5e96c`** in `lean-toolchain` and `lake-manifest.json`. Use those committed files; do not run `lake update` when reproducing this release.

GitHub Actions runs the build, structural and dependency checks, declaration checks, axiom audit, and kernel recheck. It also compiles the companion mathematical paper. The final release includes the corresponding verification output.

## Source organization

`LanglandsFirstMainLemma/` contains the Lean development. `blueprint/src/` explains the mathematical statements attached to the proof nodes. `NODE_SPEC.csv` and `DEPENDENCY_GRAPH.dot` are machine-readable indexes used by the checks, not development logs.

## Citation and license

Author: Fukuhiro Ueda. Use the metadata in [CITATION.cff](CITATION.cff) to cite the software. The source is distributed under the [Apache License 2.0](LICENSE).
