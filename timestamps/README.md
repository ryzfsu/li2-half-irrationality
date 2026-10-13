# Timestamps

[OpenTimestamps](https://opentimestamps.org) proofs for the assets of release `v1`.
Each proof commits to the SHA-256 of the file below and is anchored in Bitcoin block
970653 (2026-10-09 15:43:29 UTC).

| file | SHA-256 |
|---|---|
| `li2-half-irrationality-v1.pdf` | `d427ed2ea97fbc3119bdb90c8ebeca76df183ba27e7b0d21b1a382319607283e` |
| `li2-half-irrationality-v1.tar.gz` | `85e80c3f9115f814f09e71f01afb749097342955aa480366280dbb96d784f022` |

Proofs for the assets of release `v2` (anchored in Bitcoin block 971174, 2026-10-13 02:37:22 UTC):

| file | SHA-256 |
|---|---|
| `li2-half-irrationality-v2.pdf` | `d427ed2ea97fbc3119bdb90c8ebeca76df183ba27e7b0d21b1a382319607283e` |
| `li2-half-irrationality-v2-lean.tar.gz` | `2a4b030c8bd20c1b14f22d36a374e81ef96d50ea7b05469d4aa0fd9a7c9826e5` |
| `li2-half-irrationality-v2.tar.gz` | `ec30734d06534ac38fc09f0b1d24ebfa1251cda0861eff13e9d85372356057d8` |

To verify, download the release asset into this directory and run

    pip install opentimestamps-client
    ots verify timestamps/<file>.ots
