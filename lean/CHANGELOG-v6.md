# v6 changelog

This release is a fresh source export based on v5 plus the verified R-RESHARD
certificate implementation. Versions v1 through v5 remain unchanged.

## Source change

- Replaced `Li2Lean/P0/ActualReferencePinnedData.lean` with the body from
  `root/reshard@39bb302`, retaining the five-line Ruiyi Zhang header.
  The 151 public theorem statements are byte-identical; Rat `decide +kernel`
  recurrence certificates now use Boolean numerator/denominator comparisons
  with soundness through `Rat.ext`.
- The development-only `tools/nanoda/rewrite_rpd.py` and all git metadata
  are excluded from this package. The 68 non-target Lean files removed in v5
  remain removed.

## Verification delta

- R-RESHARD's complete source build reports 9727/9727 Lake jobs with zero
  errors. The v6-local incremental Lake build is rerun separately.
- R-RESHARD's independent nanoda export reports 106321 declarations with no
  typechecker errors and exit code 0; its export SHA is recorded only as
  an intermediate receipt until the v6 export is regenerated.
- v6 axioms and declaration-closure receipts are recorded in the verification
  section of README. The fresh landrun comparator and exact-v6 nanoda remain
  pending until their own success markers and exit receipts are available; no
  pending result is described as accepted.

## Release evidence and documentation pass

- Kept one axioms receipt, the 19:38Z run, and bound it to the relative source
  closure manifest SHA; removed host and absolute-worktree details from the
  receipt metadata and regenerated its relative SHA256SUMS.
- Replaced the root PNT directory copy with a package-level NOTICE; the
  original vendored notice remains at `Li2Lean/Vendor/PNT/NOTICE`.
- Recorded historical source comments as errata rather than editing the Lean
  build closure.
- Added command, toolchain, UTC, source-manifest, incremental-replay, and
  comparator-rebuild provenance to `verification/lake-build-v6.log`.
- Extended the separate declaration closure driver to traverse declaration
  types and encountered local inductive constructors/recursors, then reran it
  with a positive control.
- Added the exact v6 C1 nanoda receipt and export hashes. The exporter log
  retains two non-fatal PANIC diagnostics; nanoda itself reported zero
  typechecker errors and exit code 0.
