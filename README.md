# Erdős Problem 654: verified negative near-linear part

This project reproduces the known two-axis counterexample to the near-linear
part of [Erdős Problem 654](https://www.erdosproblems.com/654). For every natural
number `m`, it constructs `4*m` distinct points in the Euclidean complex plane.
No circle contains four selected points. Each selected point determines fewer
than `3*m` distinct distances to the other points. This disproves the assertion
that no-four-concyclic alone forces a pinned count of `(1-o(1))*n`.

The project also proves the elementary bound `n-1 ≤ 3*R(p)` at every selected
point. It does not prove a fixed improvement above one third. The weaker
question and general-position variants remain unproved here.

## Sources and authorship

The mathematical construction is due to Aletheia, reported by Feng et al.,
[arXiv:2601.22401v3, Section 3.1](https://arxiv.org/abs/2601.22401v3).
The proof in `Erdos654/TwoAxis.lean` substantially reproduces the formalization
by GitHub user `ketianzhang1-lang` from
[`jsp-000301-lean` at fb8577233935d1ff4533418ff8ea33a4d7dab101](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/fb8577233935d1ff4533418ff8ea33a4d7dab101/projects/jsp-000530/JSP000530.lean).
Its MIT licence and copyright notice are preserved in `LICENSE`.

That formalization replaces the source's powers of two and three with even
horizontal and odd vertical integer coordinates. A circle meeting both axes
in two selected points would force incompatible products of coordinates.
Opposite cross-axis points determine equal distances, giving the upper bound.
This package adds module visibility, independently stated registry targets,
the elementary lower bound, and a map of the unsolved variants. It claims no
new mathematical result or independent rediscovery of the existing proof.

The human user directing this submission attests that they are an author or
maintainer of the substantive formalization. The responsible account for this
package is `AItoBit`. Codex prepared the adaptation and ran automated audits;
these are not human expert review or endorsement.

## Mathematical scope

`Erdos654/Target.lean` defines the extremal function as the minimum attained
largest pinned-distance count at a fixed size. It records the strong, weak,
and general-position questions as propositions, with no purported proofs of
the open questions. It also records the website's near-linear centered-circle
suggestion, with a source caveat. The supplied forum PDF points out that the
1988 source asks for an improvement above one half under that centered-circle
hypothesis, rather than the near-linear conclusion.

`Challenge.lean` independently states the three registered results and their
definitions using only Mathlib. Its three deliberate statement placeholders
are excluded from proof-status counts. `Solution.lean` proves the matching
declarations. `comparator.json` names both definitions and all three results.
The proof development has no placeholders, added mathematical axioms,
`native_decide`, or unsafe verification shortcuts.

## Verification

The source development was first reproduced locally on Lean 4.33.1 and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. Palomar currently requires the
Comparator bundled with Lean 4.35.0-rc2 or later, so the submission snapshot
uses Lean and Mathlib 4.35.0-rc2. Its pinned full mechanical workflow is the
submission verification authority; local 4.33.1 checks are separate evidence.

Build the development with `lake --wfail build`. Inspect principal axioms with
`lake env lean Audit.lean`. The intended permitted foundation is exactly
`propext`, `Classical.choice`, and `Quot.sound`.

Submission is through [Palomar](https://submit.palomar-registry.org/).
The reusable workflow runs the full mechanical preflight at one immutable
source commit before intake. Registration requires the user to see the actual
review and explicitly request its permanent publication.

## Research coverage

The requested Mathematics Research Studio campaign defaults to 100 full-text
paper reviews. This checkpoint does not complete that corpus. `papers.jsonl`
records only the sources actually screened and sections inspected; no full
paper review or novelty survey is claimed. The broader estimation problem
remains unresolved in this development.
