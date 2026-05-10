# PolicyUp

## Carrier sketch

A $\PolicyUp$ token is a single finite-history carrier for action-selection
certificates: a $\mathsf{BHist}$ source row records the visible history
prefix, an action row records the selected finite action code, a classifier
row records the $\hsame$-stable observation class used for the choice, and a
ledger row records the visible reason packet that made this action admissible.
The Lean carrier is planned as one `inductive PolicyUp : Type`, not a family
of carriers: each constructor contributes one policy token whose
`BHistCarrier.toEventFlow` display is a finite event flow, and the same single
carrier then enters `ChapterTasteGate`. Equivalence is controlled by $\hsame$
on the classifier row after fixing the source prefix; $\mathsf{Cont}$ links
the source prefix to the displayed action row; $\mathsf{Pkg}$ carries the
finite reason packet; transport preserves the classifier and ledger rows
under $\hsame$ replacement. The dependency anchors are
\NameCert{BeliefUp} for history-conditioned information states,
\NameCert{MarkovChainUp} for finite transition histories,
\NameCert{RandomVarUp} for finite outcome rows, and \NameCert{EstimatorUp}
for visible score or loss certificates.

## TasteGate sketch

1. **Conservativity**: introducing $\PolicyUp$ does not change any
   baseline-only formula about the dependency chapters or the BEDC kernel,
   because a policy token is exposed only through its compiled finite
   `EventFlow`. The proof outline instantiates
   `BEDC.Meta.TasteGate.ChapterTasteGate.conservativity`, whose proof invokes
   the ground-compiler `event_flow_conservativity` theorem on
   `BHistCarrier.toEventFlow x`; every displayed mark in the policy source,
   classifier, ledger, and action packet is therefore a ground display mark,
   not a new baseline rule.

2. **No hidden input**: every $\PolicyUp$ token is reconstructed from its own
   finite display. The planned `fromEventFlow` parser accepts exactly the
   four tagged rows source / classifier / ledger / action, checks their
   `Cont` and `Pkg` tags, and returns the corresponding constructor; the
   witness for no hidden input is then
   `BEDC.Meta.TasteGate.ChapterTasteGate.no_hidden_input`, applied to the
   token and its `toEventFlow` image. No oracle policy, unlogged reward, or
   external model parameter enters the carrier.

3. **Round trip**: display readback followed by reconstruction is the
   identity on the single carrier. The proof is by cases on the constructors
   of `PolicyUp`: the empty source policy reads back to the empty constructor;
   the deterministic choice constructor reads back by matching the source,
   classifier, ledger, and action tags; and the transported choice
   constructor reads back by the stored $\hsame$ transport witness. Each case
   reduces to definitional equality of the row tags plus the visible
   `Cont`/`Pkg` packet.

4. **Layer separation**: source, channel, and display roles stay disjoint
   because the row tags are role-specific and the classifier cannot be read as
   either an action row or a ledger row. The proof outline establishes
   injectivity of `BHistCarrier.toEventFlow` for distinct tokens, using the
   first mismatching tag among source / classifier / ledger / action; this is
   the `ChapterTasteGate.layer_separation` field. The intended ground
   compiler alignment is that the same encoded rows can also instantiate the
   source-channel separation lemma for role recognizers, while the class field
   needed by the hard schema is the direct event-flow injectivity statement.

## Five NameCert obligations sketch

**Source**: the source obligation accepts only finite $\mathsf{BHist}$
histories: a visible history prefix, a finite action code, and the local rows
needed to certify the choice. The chapter does not import an ambient
state-space object; the source is exactly the event history that the
`BHistCarrier` compiler can display.

**Classifier**: the classifier is $\hsame$ on the observation-class row after
the source prefix is fixed. Two policy tokens classify the same choice only
when their classifier rows are $\hsame$ and their action rows are connected to
the same source by $\mathsf{Cont}$.

**Pattern**: the pattern obligation says that a policy packet has the tagged
shape source / classifier / ledger / action, that the ledger is a visible
$\mathsf{Pkg}$, and that the selected action is $\mathsf{Cont}$-reachable from
the source prefix. This is structural policy admissibility, not optimality.

**Ledger**: the ledger records the reason packet used by the classifier:
visible belief-state reference, transition-history reference, outcome-row
reference, and score-row reference. The ledger is part of the token display,
so transport and readback can inspect it.

**Extension**: extension transport replaces source or classifier rows by
$\hsame$ rows while preserving the same action row and ledger packet. The
NameCert extension boundary asserts that such transport keeps the token inside
$\PolicyUp$ and preserves the compiled `EventFlow` recognition class.

## Why this is a real theory, not combinatorial padding

$\PolicyUp$ introduces the constructive BEDC object corresponding to a policy
in sequential decision theory: a finite-history rule that selects actions
from visible information. This is not a renaming of \NameCert{BeliefUp},
which records information states without action commitment, and not a
renaming of \NameCert{MarkovChainUp}, which records transition structure
without a choice rule. The mathematical motivation is standard and
independent: Bellman's dynamic programming principle in *Dynamic Programming*
(1957) and Sutton and Barto's policy-based formulation in *Reinforcement
Learning: An Introduction* (2018) both treat policies as central objects,
while Russell's *Human Compatible* (2019) motivates making the policy object
auditable for alignment. The BEDC contribution is the finite-history,
ledger-visible, zero-axiom version whose TasteGate carrier is a single
compiler-facing type.

## Cannot-claim

The chapter does not close optimality, convergence of reinforcement learning,
existence of stationary optimal policies, stochastic policy gradients,
measure-theoretic Markov decision processes, equilibrium selection, alignment,
deception detection, or any bridge to analytic control theory. It only
proposes the finite-history policy carrier, its NameCert surface, and the
TasteGate plan needed before downstream chapters can reason about value,
reward, oversight, or alignment.

proposed_chapter: policy
proposed_dependencies: BeliefUp, MarkovChainUp, RandomVarUp, EstimatorUp
