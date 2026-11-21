/-!
# `CertCore.Cert` — trusted

The Lean-side certificate type, its JSON encoding, and the **total** decoder
(project plan §4.1, §10.3; wire format frozen in `docs/certificate-v1.md`).

Status: **stub** (M0). Filled in by M4.

The decoder is part of the TCB and has an adversarial input model: malformed
JSON must produce `Diagnostic.malformed`, never a crash, and must not be able
to induce super-linear work (T10, M4.2–M4.3). No partial functions anywhere on
the decode path.

Planned contents:

* `Certificate` — entry state, sparse `(point, label) → Abs` map, domain tag,
  format version, program hash.
* `encode : Certificate → Json` (M4.1).
* `decode : Json → Except Diagnostic Certificate` (M4.2), total.
* T10 `decode_sound` (M4.3) and the round-trip property (M4.4).
-/
