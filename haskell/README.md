# haskell/ — the untrusted analyzer

Empty at M0. Everything here is **outside** the trusted base: a fixpoint
engine, a widening, label instrumentation, a certificate emitter, and a repair
loop driven by the checker's diagnostic (M5).

The point of writing it in a different language from the checker is that the
trust boundary becomes architectural rather than a comment. A disagreement
between the two transfer implementations is caught by the checker — and is
itself data (the differential test, M5.7).

## Toolchain (verified on this machine)

| Tool | Version | Location |
|---|---|---|
| GHC | 9.10.3 | `C:\ghcup\bin` |
| cabal-install | 3.16.1.0 | `C:\ghcup\bin` |
| stack | 3.11.1 | `C:\ghcup\bin` |
| HLS | 9.10.3 | `C:\ghcup\bin` |

`C:\ghcup\bin` is on the user `PATH` but not on this session's `PATH`; build
scripts must prepend it explicitly.

**Open decision (M5):** `stack` versus `cabal`. The project plan's verification
pipeline (plan §10.2) writes `stack build`; nothing else depends on the choice.
Decide before M5.1 so CI is written once.
