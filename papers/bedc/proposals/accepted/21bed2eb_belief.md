# BeliefUp

## Carrier sketch

A $\BeliefUp$ token carries a finite $\mathsf{BHist}$ history of
(observation, evidence-ledger, posterior-credence) rows together with
a $\SeqUp$-typed update trace. The carrier accepts a sequence $(o_0,
\ldots, o_n)$ of observations together with a credence assignment
$\rho_n : \mathsf{Hyp} \to \NatUp$ (unary credence levels, normalised
in the displayed pattern row) when there is a finite update trace
each of whose one-step entries records an evidence row that justifies
moving from $\rho_{i}$ to $\rho_{i+1}$ given observation $o_{i+1}$.
The classifier is $\hsame$ on the credence rows after fixing the
observation prefix; transport repacks the update trace through a
classifier-stable observation transport. Depends on $\NameCert_{\NatUp}$
(\autoref{ch:concrete-instances-nat-namecert}, for unary credence
levels), $\NameCert_{\SeqUp}$ (\autoref{ch:concrete-instances-seq-namecert},
for the update trace), and $\NameCert_{\ProbSpaceUp}$
(\autoref{ch:concrete-instances-probspace-namecert}, for the
hypothesis-distribution semantics).

## TasteGate sketch

1. **Conservativity**: introducing $\BeliefUp$ enriches the kernel
   only by adding a finite-history credence carrier; baseline-only
   formulas (about $\NatUp$, $\SeqUp$, $\ProbSpaceUp$) remain
   provable iff already provable, witnessed by induction on the
   update trace and the observation that the credence row reduces
   to $\NatUp$ readback under $\hsame$. Outline: instantiate the
   ground-compiler `event_flow_conservativity` template with the
   `BeliefUpdate` event flow.

2. **No hidden input**: every $\BeliefUp$-token reduces to a finite
   event flow over the display alphabet by encoding (observation,
   evidence, credence) rows as ground-compiler `RawEvent` lists.
   Use `RecognizesEventFlow` from `RecognizerFlows.lean` with
   role `RecognitionRole.belief`. No external probability measure
   leaks in; the credence is unary and observations are display
   rows.

3. **Round trip**: $\mathsf{BeliefReadback} \circ
   \mathsf{BeliefReconstruct} = \mathsf{id}$ on tokens. Outline: by
   induction on the update trace, base case is the empty prior
   (trivial reconstruction), step case repacks the new evidence
   row's $\hsame$ witness.

4. **Layer separation**: observation rows (source), update rows
   (channel), and credence rows (display) do not collapse — an
   observation row never matches an update row's evidence-ledger
   shape, and a credence row never matches an observation row's
   pattern. Outline: instantiate `source_channel_separation` with
   the three role-specific recognizers.

## Five NameCert obligations sketch

- **Source**: the carrier accepts unary observations, unary credence
  levels, $\SeqUp$ update traces, and finite evidence rows. No
  measure-theoretic hypothesis space, no infinitary credences, no
  oracle priors.
- **Classifier**: $\hsame$ on the credence row after fixing the
  observation prefix; transport repacks update traces through a
  classifier-stable observation transport.
- **Pattern**: prior-admissibility, evidence-coherence, posterior-
  normalisation, update-step admissibility, observation-determinism
  rows.
- **Ledger**: the update trace, the evidence rows, and the prior /
  posterior credence values are all visible to the certificate.
- **Extension**: the boundary fixes that two updates over the same
  observation prefix yield $\hsame$-classified posteriors (no path-
  dependence below the observation classifier).

## Why this is a real theory, not combinatorial padding

$\BeliefUp$ is the BEDC reformulation of Bayesian belief revision
(Pearl 1988, *Probabilistic Reasoning in Intelligent Systems*) and
its descendants in active inference and AI alignment (Soares & Fallenstein
2014, *Aligning Superintelligence with Human Interests*; Bostrom 2014,
*Superintelligence*; Russell 2019, *Human Compatible*). It is *not*
a renaming of $\ProbSpaceUp$ — that chapter formalises measure-
theoretic probability over a fixed sample space, while $\BeliefUp$
formalises *update dynamics* over a finite-history observation flow,
giving a constructive, unary-credence carrier that does not require
measure completion. It is *not* a renaming of $\MarkovChainUp$ — that
chapter has no posterior structure, only transition probabilities. The
chapter is a substrate for downstream chapters covering policy,
world-model alignment, and deceptive vs honest belief reporting, which
are central open problems in AI safety formalisation.

## Cannot-claim

The chapter does not close: continuous-credence Bayesian update,
infinite hypothesis spaces, measure-theoretic posteriors, the de
Finetti representation theorem, the Cox-Jaynes derivation of
probability from coherent beliefs, or any standard bridge to
classical probability theory. The chapter does not claim that
$\BeliefUp$ is *the* unique formalisation of belief; it is the
finite-history constructive variant compatible with BEDC zero-axiom
discipline.

proposed_chapter: belief
proposed_dependencies: NatUp, SeqUp, ProbSpaceUp
