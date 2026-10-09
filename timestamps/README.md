# Timestamps

[OpenTimestamps](https://opentimestamps.org) proofs for the assets of release `v1`.
Each proof commits to the SHA-256 of the file below.

| file | SHA-256 |
|---|---|
| `li2-half-irrationality-v1.pdf` | `d427ed2ea97fbc3119bdb90c8ebeca76df183ba27e7b0d21b1a382319607283e` |
| `li2-half-irrationality-v1.tar.gz` | `85e80c3f9115f814f09e71f01afb749097342955aa480366280dbb96d784f022` |

To verify, download the release asset into this directory and run

    pip install opentimestamps-client
    ots verify timestamps/<file>.ots
