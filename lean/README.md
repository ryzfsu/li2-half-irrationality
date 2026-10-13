# Li2(1/2) Lean Certificate

This package distributes the Lean proof sources for the statement

`Li2(1/2) = Σ_{k≥1} 2^{-k}/k²`

is irrational.

Paper: Ruiyi Zhang, *Irrationality of the dilogarithm at 1/2*, preprint,
Zenodo, 2026, https://doi.org/10.5281/zenodo.23251313 (repository
`ryzfsu/li2-half-irrationality`). Section numbers below refer to that
manuscript.

Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu).

## Statement

`Challenge.lean` states the premise-free challenge and `Solution.lean` proves
the identical proposition. The exact Lean statement is:

```lean
theorem li2_half_irrational :
    Irrational (∑' k : ℕ, ((2 : ℝ)⁻¹) ^ (k + 1) / ((k : ℝ) + 1) ^ 2)
```

The summation index `k` starts at zero, so `k + 1` indexes the mathematical
series from one.

## Build and dependencies

Use Lean 4.35.0-rc4 and the Mathlib revision recorded in
`lake-manifest.json`. The only direct external Lake dependency is Mathlib;
its pinned dependencies include Batteries. Third-party source included or
adapted in this package is listed in `THIRD_PARTY_NOTICES.md`.

With Mathlib's dependencies available locally, run:

```text
lake build Li2Lean Solution Challenge
lake env lean -DautoImplicit=false SolutionAxioms.lean
```

The target build contains 695 Lean modules in the import closure of
`Li2Lean`, `Solution`, and `Challenge`; `SolutionAxioms.lean` is the separate
axiom-report driver. The package does not include the original CSV/reference
inputs, their generators, or the manuscript files cited in source comments.
The manuscript and those data are needed for a complete paper-to-source and
data-regeneration audit; this distribution is the proof source, not a full
research archive.

## Mathematical scope

The formalization follows the method of the paper: the same determinant
polynomials `G_m(T)`, the same analytic, integerization and nonvanishing
estimates, and the same final argument. Only some explicit constants differ.
They were relaxed where this shortened the Lean certificates; the method is
unchanged.

| Paper | Content | Lean |
|---|---|---|
| §1, (1.1) | determinant polynomials `G_m(T)` | `p0CanonicalPolynomial`, `p0A2CanonicalFamily` (`Li2Lean/Main.lean`) |
| §2 | rational matrices and parameter derivatives | `Li2Lean/P0/` source and coefficient modules |
| §§3-7, Prop. 1.1 (1.2) | analytic estimate: contour expansion, tube transfer, dual lower bound, finite configurations, frequency sum | `P0AnalyticEstimateAt` (`Li2Lean/LayerInterfaces.lean`), `alphaGamma` (`Li2Lean/P0/Contour.lean`), `AlphaUnconditional`, `CellBound`, `ActualReference*` |
| §8, Prop. 1.1 (1.3) | clearing denominators, `D_m G_m(T) ∈ Z[T]` | `Li2Lean/P0/Integerization*`, `Li2Lean/IntegerizationTables/` |
| §9, Prop. 1.1 (1.4) | nonvanishing along `m = 32·83^k` (Lucas congruence modulo 83) | `p0A2_nonvanishing` (`Li2Lean/P0/NonvanishingScaledLucas.lean`) |
| §10 | proof of Theorem 1 | `Li2Lean/Kit/EndpointCriterion.lean`, `Li2Lean/P0/RateEndpoint.lean`, `Li2Lean/P0/FinalEnvelopeWiring.lean` |

Constants:

| Quantity | Paper | Lean |
|---|---|---|
| `alpha` in (1.2), same error terms `10 m log m + 56 m + 301`, `m ≥ 8`, `4 ∣ m` | `1992909/10^6 = 1.992909` | `397/200 = 1.985` |
| lower bound for the variational value `alpha_Gamma` (§3) | `> 1992909/10^6` (dual certificate, §5) | `> 199/100 = 1.99` |
| integerizer rate in (1.3) | `tau < 1.979` | `248/125 = 1.984` |
| final margin | `1.979 < 1.992909` | `1.984 < 1.985` |

This package does not claim the paper's sharper `1.992909` analytic target or
its integerizer bound `tau < 1.979`; both are proved in the paper, and the Lean
proof uses the weaker values above, which already suffice.

Source comments cite the manuscript by LaTeX labels (for example
`eq:contour-alpha`, `lem:dual-lower`, `sec-tube.tex`); these refer to the
paper above. Some comments also cite unshipped development notes (`docs/NNNN`)
or a later general write-up of the same construction ("paper v13"); they are
historical development notes, not part of this release.

The Lean finite-energy domain is an auxiliary domain sufficient for the
formal argument. This package does not claim a separate equivalence theorem
between that domain and every convention for finite energy in the manuscript.

Several historical interfaces remain in the source closure for development
and comparison, including the old `hS4` coefficient bridge, finite-configuration
coefficient records, `CAReceiptSlack`, `Config.CAReceipt`, and
`P0DualCertificate`. They are not inputs to the final declaration
`li2_half_irrational`; `verification/declaration-closure.txt` records a
declaration-level dependency scan with a positive control.

## Verification status

This v6 package includes the Boolean numerator/denominator certificate repair
in `ActualReferencePinnedData.lean`. Status is stated separately for the proof
build, axioms, comparator, and nanoda so a completed build is not confused with
independent-kernel acceptance.

* Lake build: PASS, 9727/9727 jobs, exit code 0, with `autoImplicit=false`.
  This v6-local receipt is an incremental replay of the retained build cache,
  not a clean build; its command, toolchain, UTC receipt time, and source-
  closure manifest hash are recorded in `verification/lake-build-v6.log`.
* `#print axioms li2_half_irrational`: PASS, exit code 0; raw output is
  `[propext, Classical.choice, Quot.sound]`. The single retained 19:38Z run
  is bound to the 695-file build-source manifest SHA
  `3c5c3f85c7a7302961b2bc706cf76cb3ec9047b2c2a29513a7b324e399ef5fbe`.
  Command and toolchain provenance are in `verification/axioms-provenance.txt`.
* Lean-kernel comparator: PASS, exit code 0. The comparator's own output ends
  with `Lean default kernel accepts the solution` and `Your solution is okay!`
  (run 2026-10-12T20:30Z to 2026-10-13T01:59Z, real landrun sandbox,
  `verification/comparator-leankernel.json`, nanoda disabled in that run).
  It ran in this package directory with its retained Lake build; inside the
  sandbox the comparator rebuilt (replayed) Challenge and Solution itself and
  exported both before the kernel check. Input and tool SHA-256 values and the
  tool output are in `verification/comparator-leankernel-result.txt`.
* Nanoda C1: PASS on the exact v6 export, exit code 0, with
  `Checked 106317 declarations with no typechecker errors`. The only note is
  nanoda's harmless pretty-printer message `Unable to print axioms`. A one-thread
  replica stopped at its 4 h time limit without a result and is not counted;
  earlier OOM, direct-export, and zero-declaration attempts are not counted.
* The v6 exporter returned exit code 0 and the root theorem record is present,
  but `verification/export.log` retains two non-fatal exporter PANIC
  diagnostics (`Option.get! none` and `Constant [anonymous] not found`). The
  nanoda receipt, export hashes, and RSS log are shipped under
  `verification/`. These diagnostics do not suppress a nanoda typechecking
  error: C1 reported zero typechecker errors.
* Colab comparator probe: BLOCKED because that runtime has no Lean toolchain;
  no fake sandbox was used.

The supplied `comparator.json` requests comparison of Challenge and Solution,
checks the permitted axiom set, and enables nanoda. The separate
`verification/comparator-leankernel.json` requests the Lean-kernel-only run.
Configuration files describe requested checks; the acceptance status above
is taken only from logs that contain the tools' own success messages.

`verification/DeclarationClosureScan.lean` is a separate, non-build audit
driver. Its receipt traverses declaration types and values and expands the
constructors/recursors encountered for local inductive declarations; it is
not an axiom report and does not replace the kernel checks.

## Errata

- The v4 `Challenge.lean` comment incorrectly wrote
  `Solution.li2_half_irrational`; the theorem is root-namespace
  `li2_half_irrational` in the `Solution` module. The v5 statement is
  unchanged.
- The contour comments now point to the proved frequency-diagonal nullity
  result. The S08 overview now describes the actual `a = 2` specialization
  without asserting a general-base factor for the lower block. These are
  documentation corrections; the theorem statements are unchanged.
- `LogMonomial.lean` points to `THIRD_PARTY_NOTICES.md` for its recorded
  upstream provenance. Its adapted lemma is unchanged.
- Historical source comments intentionally remain unchanged to avoid rebuilding
  the proof closure: `Li2Lean/Statement.lean` describes the broader all-`n`
  target, `Li2Lean/Main.lean` mentions unresolved P0 inputs, and
  `Li2Lean/Bridges.lean` points to an unshipped `LEDGER.md`. These comments are
  conditional/development notes, not claims made by this release.
- `Li2Lean/Vendor/PNT/Wiener.lean` uses historical wording about the first two
  theorems lacking upstream proofs; the package notice identifies the precise
  `prelim_decay_*` names. The vendored source is left byte-for-byte unchanged.
