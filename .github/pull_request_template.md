## Summary

<!-- What the change does and why, and how it was tested. -->

## Proof fields

<!--
The proof guard, `cargo xtask formal guard`, reads every line of the
description that starts with the name of a field and a colon (section
Guard of docs/formal-verification.md), so give each field only on its line
at the end. Write a value after its colon on the same line and leave the
other lines empty; a field given twice counts as missing.

- `Phase`: `statement`, `proof` or `rewrite`, the phase of the proof work
  that the change belongs to. Needed with the label `spec` or `proof`.
- `Author`: the opaque id of the author, 1 to 64 ASCII letters and
  digits. Needed with the label `spec` or `proof`.
- `Review`, `Approval` and `Approved-Statement-Hash`: the ids of the
  review and of the owner's approval of a statement change, and the
  statement hash that was approved. Needed with the label `spec`.
- `Heartbeats-Review`: the id of the review of a raised heartbeat limit.

The ids are opaque; the records that they name are kept in the project's
coordination records, outside this repository. Add the label `ai-proof`
when an AI system wrote proofs in this change.
-->

Phase:
Author:
Review:
Approval:
Approved-Statement-Hash:
Heartbeats-Review:
