# Supplementary materials

This file accompanies *Irrationality of the dilogarithm at 1/2* (Ruiyi Zhang).

- Archive: `anc/li2-half-supplement-v1-20261008.tar.gz`
- SHA-256 of the archive: `ad6f16382bd30a28cea7df56441b189cc146a767ef87ee72e682378cca9f8bf0`
- SHA-256 of the archive's root manifest `SHA256SUMS`: `85441ea65275ccc6fe357698b38239a5ccc2b63072297d0708fa8680e677e460`

The archive contains the finite data of the three computations listed in the
appendix of the paper, the checking programs, the environment details and the
outputs of one complete replay.

| Directory | Contents |
| --- | --- |
| `core/certificates/dual/` | Reference pair, cell lists and the directed Arb checker for the constant `alpha` (Section 5). |
| `core/certificates/arithmetic_basic/`, `arithmetic/` | Exact rational certificate and verifiers for the denominator bound `tau < 1.979` (Section 8). |
| `core/certificates/seed/` | Seed matrices modulo 83 and 103 and the determinant check (Section 9). |
| `core/certificates/assembly/`, `linear_tail/` | Exact checks of the rational constants in the assembly and the tail. |
| `core/verify_bundle.py` | Light exact replay of the arithmetic, the dual bookkeeping, the constants and the seed. |
| `root_checks/` | Small independent check of the source series and the margins. |
| `independent/a`, `independent/b` | Two independent interval checkers for the dual certificate. |
| `replay_outputs/` | Logs, receipts and environment of one complete replay. |

From the extracted archive root:

```text
python3 replay.py          # complete replay, about one minute on one core
python3 replay.py --quick  # light exact stages only
```

The replay checks `SHA256SUMS`, copies the bundle to a fresh directory and
runs the checkers there. It needs Python 3 with `python-flint` and at least
20 GiB of available memory. The finite numerical statements of the paper
use only exact rational, directed-interval or modular checks; rounded
decimals are never premises.
