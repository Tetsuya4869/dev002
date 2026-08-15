# Moore57 research limit report — 2026-08-15

## Executive status

The degree-57 diameter-2 Moore graph problem itself is **not solved**. The current branch reaches a defensible stopping point for the present method stack: the graph-to-permutation reduction is kernel-checked in Lean, the restricted all-involution search is solver-independent at the logical boundary, independently verified certificates exist through `t = 10` selected non-base branches, and several genuinely different exact-search encodings/solvers all hit an unresolved `t = 10 -> 11` extension wall.

The remaining step is not plausibly just “run the same search longer”. A new global invariant, a much stronger symmetry-breaking theorem, or a substantially different proof-producing search formulation is needed.

## 1. Formal results now kernel-checked

The Lean development uses mathlib's standard strongly-regular graph interface and proves the following chain without `sorry`:

`SimpleGraph.IsSRGWith 3250 57 0 1`

→ Moore local relation (`triangle-free`, unique common neighbour for distinct nonadjacent vertices)

→ degree-57 rooted decomposition

→ exactly 56 leaves in every branch and `Fin 56` coordinates

→ perfect matchings between distinct branches

→ raw permutation system

→ triangle and quadrilateral holonomy restrictions

→ gauge normalization at a chosen base branch

→ `ShortCycleSystem`

→ order-56 injective Latin cube / finite Latin cube

→ route-exhaustion bijection in the full 56-branch case.

Relevant modules include:

- `Moore57/GraphReduction.lean`
- `Moore57/GraphToRaw.lean`
- `Moore57/Degree57Coordinates.lean`
- `Moore57/GaugeNormalization.lean`
- `Moore57/SRGBridge.lean`
- `Moore57/SRGConsequences.lean`
- `Moore57/RestrictedSystem.lean`
- `Moore57/SRGRestricted.lean`
- `Moore57/DualMatching.lean`

The restriction theorem is deliberately solver-independent. If the graph-derived normalized system has involutive matchings on all pairs of non-base branches, then for every `t ≤ 56` an injectively selected `Fin t` inherits the exact abstract restricted certificate used by the computational search. Hence an independently established nonexistence of such a restricted certificate for any single `t ≤ 56` would rule out the full all-involution subcase.

In the full `t = n = 56` case, the Lean development also derives a dual matching structure: fixing two distinct symbols gives a fixed-point-free involution on the branch set. Thus branch pairs induce perfect matchings of symbols and symbol pairs induce perfect matchings of branches.

## 2. Axiom / trust audit

CI runs `lake build` and then an explicit `#print axioms` audit. The central theorems tested depend only on standard Lean foundations such as `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` is present. A repository search also found no intentional custom axiom used to bridge the hard graph-to-permutation step.

The latest Lean verification before this report is green on the research branch. Earlier milestone runs include:

- `31782710681`: SRG bridge accepted.
- `31782867910`: end-to-end SRG consequences accepted.
- `31782933742`: axiom audit accepted.
- `31783327319`: weakened non-base-only involution hypothesis accepted.
- `31783649938`: restricted contradiction theorem and audit accepted.
- `31786941034`: later branch head accepted after the dual-matching additions.

## 3. Independent computational verification

The search code and verifier are separate implementations. `search/verify_solution.py` does not call the solver. It checks the returned matching tables directly, including:

- permutation/bijection,
- fixed-point-free involution conditions in the all-involution model,
- star injectivity,
- triangle holonomy,
- quadrilateral holonomy,
- route distinctness / exhaustion where applicable.

The same verification pipeline was regression-tested on known smaller successful extensions before being trusted on the 56-symbol instances.

## 4. Current exact-search frontier

### Verified SAT frontier

Independent certificates exist through:

- `n = 56, t = 8`,
- `n = 56, t = 9`,
- `n = 56, t = 10`.

Two separately obtained `t = 10` certificates are stored:

- `search/seeds/moore56-t10.json`
- `search/seeds/moore56-t10-cadical.json`

Both pass the independent verifier with zero triangle- and quadrilateral-holonomy violations.

### The `t = 10 -> 11` wall

Several encodings and solvers were tried on the extension problem.

1. **Integer / element-constraint CP-SAT extension**
   - 180 s run from a verified `t=10` seed.
   - status `UNKNOWN`.
   - approximately 782k branches and 82k conflicts.

2. **Boolean edge exact-cover CP-SAT v2**
   - 12,880 Boolean variables.
   - about 973k holonomy binary clauses plus 30,800 route-at-most-one constraints.
   - 300 s, four workers.
   - representative run: about 23.3 million branches and 1.09 million conflicts.
   - status `UNKNOWN`.
   - multiple random seeds were attempted.

3. **Direct DIMACS CNF + CaDiCaL**
   - 12,880 variables.
   - approximately 2.575 million clauses (about 36 MB CNF for the original seed).
   - 600 s wall limit.
   - peak memory roughly 716 MB in the recorded run.
   - status `UNKNOWN`.
   - the same encoding pipeline successfully found and decoded `8 -> 9` and `9 -> 10` SAT witnesses, which were independently verified.

4. **Direct DIMACS CNF + CryptoMiniSat 5.11.15**
   - same order of CNF size.
   - 4 threads, 600 s wall limit.
   - original `t=10` seed: about 1.805 million conflicts and 5.75 million decisions; solver ended `INDETERMINATE` / `UNKNOWN`.
   - independently obtained alternative `t=10` seed: about 1.780 million conflicts and 5.92 million decisions; again `UNKNOWN`.

No solver produced either a `t=11` witness or an UNSAT certificate.

Therefore **`t=11` is not known to be impossible**. The correct status is computationally unresolved for the present formulations.

## 5. Algebraic diagnostics of the SAT certificates

Every fixed-point-free involution on 56 points is a product of 28 transpositions and hence an even permutation. More importantly, this is not merely a low-order parity phenomenon.

SymPy Schreier-Sims calculations on the independently verified certificates show:

- the `t=8` matching generators generate the full alternating group `A_56`;
- the original `t=10` certificate's 45 matching generators generate `A_56`;
- the independently obtained CaDiCaL `t=10` certificate's 45 matching generators also generate `A_56`.

Thus the local certificates are not trapped in a small cyclic, abelian, affine, or otherwise visibly low-order permutation group. This sharply reduces the plausibility that extending the earlier “common small derangement group” obstruction will resolve the unrestricted all-involution search.

## 6. Theory avenues checked and why they did not close the case

### Cyclic / common group constructions

Smith–Montemanni (Axioms 2026, 15(5), 332) rule out the cyclic derangement-group construction. Their paper explicitly leaves non-cyclic groups and derangement sets that are not a group. The present certificates generate `A_56`, so they lie far outside the cyclic model.

### Parity of Latin structures

All matching involutions are even permutations, suggesting an “all-even” Latin-cube obstruction. This does not immediately work: all-even Latin squares are known to exist, and the checked multiary-quasigroup / Latin-hypercube literature does not provide a general theorem forbidding the required order-56 ternary structure solely from line parity.

### One-factorization / Room / Howell type reductions

The full all-involution case produces a strong family of one-factorizations, with a dual family on symbols. But the bare phenomenon “many one-factorizations pairwise share a factor” is not contradictory: the classical Sylvester `K_6` configuration has six one-factorizations and any two share exactly one one-factor; its associated construction is triangle- and quadrilateral-free. Hence a proof for order 56 must use constraints beyond this incidence pattern alone.

### Automorphism involutions

Ishida (arXiv:2606.29183, 2026) proves that a hypothetical degree-57 Moore graph has no involutory automorphisms. The all-involution search here concerns branch-to-branch matching permutations, not automorphisms of the entire graph, so that theorem does not directly eliminate the subcase.

## 7. What would constitute a real next breakthrough

Continuing the same solver runs is no longer the highest-value move. At least one of the following is needed:

1. **A new global invariant** of the four-variable incidence relation `p_ab(x)=y`, strong enough to use both branch/symbol duality and girth-5 holonomy.
2. **A structural classification** of the full self-dual one-factorization family, analogous to but substantially stronger than the Sylvester `K_6` phenomenon.
3. **A new algebraic obstruction** operating even when the local matching generators are as large as `A_56`.
4. **A proof-producing SAT formulation with fundamentally stronger quotienting**, not merely a longer run of the current `t10 -> t11` CNF. If it proves UNSAT for some `t≤56`, the Lean restriction theorem already supplies the mathematical implication to the full all-involution subcase.
5. A way to leave the all-involution subcase entirely and control general derangements without assuming involutivity.

## 8. Limit judgment

This is the stopping point for the current approach.

What is rigorously established is considerably stronger than the starting conditional permutation model: the reduction now starts from mathlib's standard `SRG(3250,57,0,1)` hypothesis and reaches the computational certificate model through Lean-checked constructions. The computational frontier is independently certified through `t=10`, and the `t=11` wall has been reproduced across substantially different encodings, solvers, seeds, and search mechanisms.

What is **not** established is nonexistence of the degree-57 Moore graph, nonexistence of the all-involution subcase, or even nonexistence of a restricted `t=11` certificate.

Without a genuinely new theorem or a new proof-search representation, more iterations of the existing machinery would mostly buy additional CPU time rather than additional mathematical information. That is the reason for declaring the present method stack exhausted here.
