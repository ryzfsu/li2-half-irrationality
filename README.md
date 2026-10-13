# Irrationality of the dilogarithm at 1/2

Ruiyi Zhang

DOI: [10.5281/zenodo.23251312](https://doi.org/10.5281/zenodo.23251312)

The manuscript proves that `Li_2(1/2)` is irrational. By the reflection formula,
`Li_2(1/2) = pi^2/12 - (1/2) log^2 2`, so this is equivalent to the irrationality of
`pi^2 - 6 log^2 2`.

Irrationality of `Li_2(1/s)` was known for integers `s <= -5` and `s >= 6` (Hata; Rhin and
Viola), and Prellberg recently proved it for `s = -4, 5, -3`. The approximations are
determinant polynomials `G_m(T)` built from moments of `1/(xy-2)`, differentiated `m/2`
times in the parameter. For `m >= 8`, `4 | m`:

    |G_m(Li_2(1/2))| <= exp(-alpha m^2 + 10 m log m + 56 m + 301),   alpha = 1.992909,

by a logarithmic energy on an ellipse certified with directed interval arithmetic.
Valuations of binomial coefficients give `D_m G_m(T) in Z[T]` with
`limsup log D_m / m^2 <= tau < 1.979`. A Lucas congruence modulo 83 gives
`G_m(t) != 0` for every rational `t` along `m = 32 * 83^k`.

## Contents

- `main.tex`, `sec-*.tex`, `main.pdf` (20 pages)
- `anc/li2-half-supplement-v1-20261008.tar.gz` - the supplementary archive: finite data, the checking programs,
  environment details and replay outputs. See `SUPPLEMENTARY.md`.
- `SUPPLEMENTARY.md`
- `SHA256SUMS`
- `lean/` - Lean 4 formalization of the main theorem (see below and `lean/README.md`)

## Build

    pdflatex main.tex
    pdflatex main.tex
    pdflatex main.tex

The source uses the standard packages `amsart`, `amssymb`, `mathtools`, `longtable`,
`seqsplit` and `hyperref`.

## Checks

Python 3 with `python-flint` (Arb) and at least 20 GiB of available memory:

    tar xzf anc/li2-half-supplement-v1-20261008.tar.gz
    python3 li2-half-supplement-v1-20261008/replay.py

`replay.py --quick` runs only the light exact stages.

## Lean formalization

`lean/` contains a Lean 4 formalization of the main theorem (Lean 4.35.0-rc4,
Mathlib `25e572b8`). The formal statement is

```lean
theorem li2_half_irrational :
    Irrational (∑' k : ℕ, ((2 : ℝ)⁻¹) ^ (k + 1) / ((k : ℝ) + 1) ^ 2)
```

It is proved without hypotheses and depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. The Lean kernel (through the `comparator`
tool) and the independent `nanoda` kernel both accept the proof; the receipts
are in `lean/verification/`.

The formalization follows the method of the paper: the same polynomials
`G_m(T)`, the same three estimates of Proposition 1.1 and the same final
argument. Some explicit parameters differ slightly from the paper, where
weaker constants shortened the Lean certificates:

| | paper | Lean |
|---|---|---|
| `alpha` in (1.2) | 1.992909 | 397/200 = 1.985 |
| integerizer rate in (1.3) | `tau < 1.979` | 248/125 = 1.984 |

The final inequality `1.984 < 1.985` closes the argument in the same way as
`1.979 < 1.992909` in Section 10. `lean/README.md` maps each section of the
paper to the Lean modules and describes how to build and check the proof.

## Citation

Ruiyi Zhang, *Irrationality of the dilogarithm at 1/2*, preprint, Zenodo, 2026. https://doi.org/10.5281/zenodo.23251312

```bibtex
@misc{zhang2026li2half,
  author    = {Zhang, Ruiyi},
  title     = {Irrationality of the dilogarithm at 1/2},
  year      = {2026},
  publisher = {Zenodo},
  note      = {Preprint},
  doi       = {10.5281/zenodo.23251312},
  url       = {https://doi.org/10.5281/zenodo.23251312}
}
```
