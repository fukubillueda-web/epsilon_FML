# Langlands’s First Main Lemma

A Lean 4 formalization of Langlands’s First Main Lemma for local epsilon factors over nonarchimedean local fields, in mixed and equal characteristic.

The exported theorem is [`LanglandsFirstMainLemma.firstMainLemma`](LanglandsFirstMainLemma/Main.lean). The proof is local and covers cyclic extensions of prime degree.

## Paper

- [Companion mathematical paper](references/epsilon_FML.tex)
- [Paper-to-Lean source map](SOURCE_MAP.md)

## Build

```bash
git clone https://github.com/fukubillueda-web/epsilon_FML.git
cd epsilon_FML
git checkout v1.0.0
lake exe cache get
lake build
lake env leanchecker --fresh LanglandsFirstMainLemma.Main
```

The committed files pin Lean **4.32.2** and Mathlib **`905b95818eb32af7874a58b427f50c1711a5e96c`**.

## Citation and license

Author: Fukuhiro Ueda. See [CITATION.cff](CITATION.cff). The source is distributed under the [Apache License 2.0](LICENSE).
