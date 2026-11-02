# Historical audit record

This is a summary of the preserved audit record, not a new build result.

The independent October 2026 audit identified source revision
`23f53ae238d01b1be52c981434c6abaef5cd49c9` and reported:

- A clean 3,205-job build with all final command exit codes zero.
- 27 remaining-route consumer, direct-edge, and family checks.
- 13 cokernel assembly stages and four direct proof-edge checks.
- A whole-project trust scan over 76 Faithful modules and 3,923 declarations,
  with a 40,751-declaration union dependency closure.
- Only `propext`, `Classical.choice`, and `Quot.sound` in those axiom closures.
- Preservation of 1,759 earlier definition types/values and every earlier public
  theorem type, with generated auxiliaries and module moves accounted for.
- Exact dependency revisions matching the nine-package lockfile.

These are historical measurements and historical preservation findings, not
fresh measurements of this public export. The audit allowed harmless compiler
linter warnings; it did not establish a zero-warning guarantee.

The 11 October reference reconciliation bound the main technical audit to the
six source inputs of arXiv:2610.08768v1. An earlier author-review PDF had been
misidentified as authoritative; its designation was corrected without changing
the Lean source. This package identifies the public versioned arXiv source
rather than redistributing historical manuscript renderings and internal
reconciliation material.

## Scope and limits

The audit covered the main technical statements, essential mathematical seeds,
construction, and written proof routes. It was not a blanket whole-manuscript
certificate. Illustrative numerical instances, simulations, practical
extraction complexity, and blanket correctness of literature discussion were
not certified. The separately excluded universal-machine representation theorem
for the host order-to-code compiler is additional machine-model certification.

The six independent probe sources are included for repeatable statement and
dependency checks. The old cross-revision preservation comparison is not
repeatable from this source subset alone; it required earlier repository and
audit inputs. No fresh result should be inferred merely from this summary or
from a successful manifest check. Consult `STATUS.json` and the logs from an
actual reproduction run.
