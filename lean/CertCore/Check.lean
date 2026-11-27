/-!
# `CertCore.Check` — trusted

The checker: three obligation families, a typed diagnostic, and **no search**
(project plan §4.1, §5).

Status: **planned** (M3). The M2 tree has the semantics, edges, and the interval
`CertDomain` (including `initOf`, `entails`, and `P_step`), but no checker.

Obligations (each decided by a `ble` or `entails` call):

* **init** — `ble (initOf p) (at entry)`
* **edge** — for every CFG edge `(p, c, q)`: `ble (transfer c (at p)) (at q)`
* **safety** — at every assert and every partial operation:
  `entails (at p) (safePred p)`

`check` returns `Except Diagnostic Certificate`, where the diagnostic names the
point, the edge, the obligation kind, and the expected/actual abstract states —
a first-class value that an untrusted driver can consume programmatically
(R6). The checker performs no search, which is what makes checker time linear
and predictable (R4).
-/
