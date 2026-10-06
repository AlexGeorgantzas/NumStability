# Limitations and unresolved questions

This audit is a read-only structural and usability audit of commit
`045daf28056a6e4358d5de7c22c7a9d7acc2e80e`. The points below are part of the
result, not incidental disclaimers. Each states the additional evidence needed
to remove or narrow the uncertainty.

## Build evidence

1. **A complete clean-output library build did not fit on the audit host.** A
   build begun with `.lake/build` absent reached 4,232 of 6,031 tasks and then
   failed with `ENOSPC`; a second fresh-output attempt was stopped before the
   same failure when measured growth projected roughly 8.2 GiB of outputs
   against roughly 7.1 GiB then free. A full same-commit cached verification did
   exit 0. This proves that the retained exact-commit outputs are accepted by
   Lake/Lean, but its 2.80 s wall time is not a clean compilation time.
   **Needed:** at least 9 GiB of genuinely free output capacity (preferably 12
   GiB headroom), absent NumStability outputs, the same pinned dependencies, and
   an uninterrupted `lake build` with a retained task log.

2. **Module timing percentiles are sample percentiles.** Every one of the 30
   predeclared targets received a fresh `.olean`/`.ilean`, but imported
   dependencies were exact-commit cached outputs. The sample is deterministic
   and stratified, not all 2,839 source modules or a random sample. **Needed:** a
   quiet sequential fresh-target run for all 2,839 modules, or a documented
   probability sample if population inference is desired; a second host/run is
   needed to estimate timing variability.

3. **Wall-clock timings are host-specific.** They include filesystem and system
   load effects. Two observations overlapping an accidental read-only scan were
   retained as superseded attempts and replaced by quiet reruns. **Needed:**
   repeated trials with a predeclared warm-up policy and reported dispersion on
   a controlled host.

## Historical comparison

4. **The Phase 10A aggregate schema was recovered, but its raw declaration TSV
   was not.** Exact-tool replay makes selected aggregate fields comparable, but
   public-name additions/removals, stable logical-edge diffs, fingerprint-based
   moves/renames, and per-declaration chain survival cannot be reconstructed
   from the historical JSON. **Needed:** build effective Phase 10A source commit
   `d21a4ed5b91008a8a5bc60741765f27fcdf86edf` with its pinned toolchain, rerun
   recovered extractor SHA-256
   `30186d3470320983e2ada2e61fce7efaa7e6230c71348c5d37a9801526be2acd`,
   retain format-2 raw TSV, and compare it with the current exact-schema TSV.

5. **Cross-module historical changes are boundary-confounded.** Phase 10A and
   current exact-schema edges are logical name pairs, but whether a pair is
   cross-module depends on current ownership. The declaration-bearing module
   count more than doubled. **Needed:** the missing historical raw name/edge
   rows plus a statement/name correspondence map; report stable logical pairs
   separately from edges whose cross-module status changed only because an
   owner moved.

6. **The later recovered `tools/library_audit/analyze_graph.py` has a DFS
   defect.** A sibling-cross-edge DAG regression showed that its iterative
   finishing order can create false SCCs. Its SCC identifiers/counts and exact
   transitive counts are inadmissible; a notice is stored with that output.
   Direct-edge, incoming, cross-module, isolate, and weak-component calculations
   do not use that routine. **Needed:** use the corrected current-schema
   iterator-stack implementation, or patch and separately version the recovered
   tool; never silently replace the recovered bytes when describing history.

7. **The recovered post-Phase-10A library-audit tree is not the Phase 10A
   schema.** It differs in public-name filtering, recursor body handling,
   self-edge treatment, and public-component semantics. **Needed:** use only
   exact Phase 10A extractor/generator replay for Phase 10A numeric comparison,
   or define a new two-snapshot comparison after rebuilding both commits under
   one new schema.

## Declaration universes and authorship

8. **Environment-public is not source-written.** Lean-reserved, equation,
   recursor, constructor, projection, deriving, tactic-generated, and other
   names can be public. This audit keeps environment visibility, reserved
   status, and source-token confirmation separate. **Needed:** for a stronger
   human-authorship claim, inspect command syntax/provenance for every candidate
   rather than relying only on declaration range and selected-token agreement.

9. **The source-written classifier is deliberately conservative and
   operational.** A declaration is source-token-confirmed only when Lean gives
   it a direct source selection range and the selected token agrees with its
   environment name. It therefore excludes unnamed generated constructors,
   derived instances, recursors, equation lemmas, and a generated
   `native_decide` axiom even when they inherit a surrounding range. Explicitly
   named structure fields/projections can match because their public field name
   is written in source. **Needed:** parser/InfoTree-level command provenance
   linking every environment declaration to a declaration command, field, or
   deriving/tactic expansion, followed by a documented policy for whether
   explicit field names count as source-written declarations.

10. **Reserved status is a signal, not a complete generator classifier.** Six
    `native_decide`-generated internal axioms are non-reserved, demonstrating
    why `isReservedName=false` cannot mean handwritten. **Needed:** retain the
    range/token and name-origin checks, and audit future syntax generators
    individually if complete generator taxonomy is required.

11. **Compiled declaration kinds do not reproduce surface syntax perfectly.**
    Reducibility hints identify abbreviations among definition values; instance,
    structure, class, partial, and safety metadata are separate facets. A Lean
    theorem is not classified by whether its source keyword was `lemma` or
    `theorem` in the kernel environment. **Needed:** join parser-level source
    command kinds to environment names for an exact surface-syntax inventory.

## Dependency and cohesion metrics

12. **Elaborated constant references omit elaboration-only requirements.** The
    graph sees constants in elaborated types and bodies/proofs. It does not
    fully encode syntax, notation, macros, tactics, attributes, scoped commands,
    or instances used only while elaborating. **Needed:** controlled import
    deletion probes or elaborator instrumentation for any claim that an import
    is unnecessary.

13. **An import edge is not a logical theorem dependency.** An import with no
    direct declaration edge remains only a review candidate. Conversely, a
    logical module dependency without a direct import can be supplied through a
    valid transitive import. **Needed:** per-import removal experiments in an
    isolated copy, with fresh elaboration, before changing imports.

14. **No incoming project edge is not “unused.”** Such a declaration may be a
    public endpoint deliberately intended for external consumers. **Needed:**
    API intent, documentation, downstream repository search, and human review
    before assigning `genuinely_unused`.

15. **No outgoing project edge does not imply mathematical primitiveness.** It
    may depend on Lean/Mathlib or use elaboration-only facilities. **Needed:**
    include external dependencies and inspect its statement/body before calling
    it foundational.

16. **Weak connectedness is not reuse.** A large weak component means an
    undirected path exists after forgetting dependency direction. It does not
    show that each member is consumed, useful, or part of a deep chain.
    **Needed:** incoming coverage, directional paths, fan-in/fan-out, depth, and
    representative verified chains—the audit reports these separately.

17. **Direct and transitive dependencies answer different questions.** Direct
    rows are retained losslessly; transitive reach is derived only on the
    NumStability project graph after SCC condensation. **Needed:** cite the raw
    direct rows for every claimed edge and the path artifact for every claimed
    transitive relationship.

18. **Layer, domain, and chapter are deterministic classifications, not kernel
    facts.** Layer and chapter mainly follow module paths; domain uses recorded
    path/name rules. Cross-domain percentages depend on that taxonomy. **Needed:**
    a reviewed manifest assigning every module/declaration to one semantic
    domain if those categories are to carry stronger interpretive weight.

19. **High fan-in measures internal consumption, not interface quality.** A
    heavily referenced generated helper or implementation detail can have high
    fan-in, while a good final theorem can have no in-library consumers.
    **Needed:** combine graph rank with authorship, visibility, documentation,
    public probes, and API-role review.

20. **“Low in the hierarchy” is graph-relative.** Dependency depth is computed
    on the SCC-condensed project graph and depends on edge inclusion and root
    universe. **Needed:** cite schema, universe, direction, and depth definition
    whenever using that phrase.

## Architecture and reorganization

21. **Declaration-free shims are established statically and checked against
    compiled ownership only within the imported root closure.** The complete
    static scan includes 710 declaration-free modules not reached by
    `NumStability.All`; they cannot own imported-environment declarations in
    this audit because they were not loaded. **Needed:** import each omitted
    module or scan its independent compiled environment if an environment-level
    zero-declaration claim is required for every file.

22. **Source-wrapper thinness has several meanings.** Few source lines, few
    declarations, direct proof delegation, and logical dependence on canonical
    declarations are separate signals. A wrapper may restate a source result
    and prove it independently. **Needed:** member-by-member proof-body edges and
    source review before classifying an individual theorem as a delegating
    wrapper.

23. **Exact elaborated statement equality is not redundancy.** Equal
    propositions can be intentional source aliases, compatibility names,
    theorem-family endpoints, or distinct source items. **Needed:** inspect
    source identity, name/API role, body delegation, consumers, and external-user
    risk before selecting a canonical declaration.

24. **The intended layer order is an architectural policy.** Apparent reverse
    imports or logical edges are factual relative to the recorded classification,
    but they are not automatically defects; legacy ownership and deliberate
    bridges can explain them. **Needed:** per-edge ownership review before a
    reorganization proposal. No such proposal or source edit is part of this
    audit.

25. **The audit has no external-usage telemetry.** In-library consumers and 15
    probes cannot reveal downstream code in private repositories or user
    expectations. **Needed:** public code search, dependent-package builds, or a
    declared support policy before removing or renaming public names/imports.

## Public API probes

26. **The 15-API sample is predeclared and stratified, not random.** Its 100%
    success rate applies only to those declarations and imports. **Needed:** a
    larger sampling frame with a reproducible random/stratified draw, or an
    exhaustive generated-client suite, for a library-wide rate.

27. **`#check` establishes visibility only.** The separate client theorem is
    stronger but most probes intentionally forward an existing theorem rather
    than discover a proof from first principles. **Needed:** task-based user
    studies or independent client developments for ergonomic/discoverability
    claims.

28. **The exhaustive direct-type scan is not a complete ergonomic signature
    audit.** The requested scan has now been run over all 58,120
    environment-public declarations and, separately, all 47,890
    confirmed-source-written public declarations. It retains every unique
    direct project type pair and further isolates the 17,547-declaration
    canonical `FloatingPoint`/`Analysis`/`Algorithms` universe. It found 2,259
    environment-public sources with a nonpublic direct type target and 650 in
    the conservative source-written-public universe; the canonical review
    union is 743 declarations and 1,304 overlapping signal edges. These are
    review candidates, not automatic defects. The scan does not pretty-print
    the client-visible signature, unfold transitive dependencies, test
    namespace discovery, or decide whether a generated helper or Source target
    is an intentional abstraction. **Needed:** manually inspect the retained
    per-declaration and edge rows, pretty-print representative and high-risk
    signatures from narrow imports, follow transitive type exposure where
    unfolding is user-visible, and compile targeted external clients for each
    materially distinct exception class.

29. **Docstring presence is not documentation quality.** It does not measure
    accuracy, examples, naming consistency, or source faithfulness. **Needed:**
    qualitative documentation review against a rubric and, for source claims,
    the cited paper/book.

## Proof trust and mathematical interpretation

30. **Compilation proves kernel acceptance in the recorded Lean environment,
    not faithfulness to Higham.** This task did not compare theorem statements
    with the book. **Needed:** an independent source-faithfulness audit with
    exact page/equation evidence.

31. **Formal reuse proves compositional typechecking, not correctness of the
    informal translation.** Error propagation through dependency paths is
    integration evidence only. **Needed:** source-faithfulness judgments for
    every statement in a chain before claiming that the chain faithfully
    formalizes the corresponding mathematical argument.

32. **Axiom reports are proof-term-local.** `#print axioms` reports constants
    occurring transitively in a selected proof term; it does not certify every
    possible downstream use. Ordinary Lean principles (for example classical
    choice or propositional extensionality) must be distinguished from
    project-owned assumptions and generated native-decision axioms. **Needed:**
    exhaustive environment traversal if a theorem-by-theorem trust matrix is
    required.

33. **`opaque` and `partial` are not placeholders by themselves.** They are
    reported as declaration/reducibility facets. **Needed:** inspect bodies,
    source intent, and consumers before making a quality judgment.

## Snapshot boundary

34. **All results are commit-specific.** `origin/higham_v01` can move after the
    recorded resolution. **Needed:** resolve the remote ref again, use a new
    isolated worktree, and create a new audit label for any later claim.

35. **This audit preserves rather than resolves architectural concerns.** No
    Lean source, import, name, path, module, commit, or remote state was changed.
    **Needed:** a separately authorized review/propose/fix task, with the skill's
    approval gates, for any reorganization.
