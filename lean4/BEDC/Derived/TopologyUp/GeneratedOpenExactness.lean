import BEDC.Derived.TopologyUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem BHistUnaryTopologyLedgerRow_generated_open_exactness
    (T : BHistIndexedOpenCarrier) {i : T.OpenIx} {U : BHist -> Prop} :
    BHistUnaryTopologyLedgerRow T i U ->
      BHistGeneratedOpenExact T U ∧
        (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
          (U x <-> U y)) := by
  intro row
  cases row with
  | singletonMetricBall ledger unaryLedger carries =>
      exact And.intro (Exists.intro i carries)
        (BHistCarriesOpen_classifier_transport T carries)
  | finiteListIntersection ledger unaryLedger carries =>
      exact And.intro (Exists.intro i carries)
        (BHistCarriesOpen_classifier_transport T carries)
  | binaryGeneratedMeet ledger unaryLedger carries =>
      exact And.intro (Exists.intro i carries)
        (BHistCarriesOpen_classifier_transport T carries)
  | arbitraryUnion ledger unaryLedger carries =>
      exact And.intro (Exists.intro i carries)
        (BHistCarriesOpen_classifier_transport T carries)
  | bottom ledger unaryLedger carries =>
      exact And.intro (Exists.intro i carries)
        (BHistCarriesOpen_classifier_transport T carries)
  | top ledger unaryLedger carries =>
      exact And.intro (Exists.intro i carries)
        (BHistCarriesOpen_classifier_transport T carries)

theorem TopologyPublicOpenTree_generated_open_exactness (T : BHistIndexedOpenCarrier)
    {i : T.OpenIx} {U : BHist -> Prop} :
    TopologyPublicOpenTree T i U ->
      BHistGeneratedOpenExact T U ∧
        (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
          (U x <-> U y)) := by
  intro tree
  have carries : BHistCarriesOpen T i U := by
    induction tree with
    | basic carried =>
        exact carried
    | binaryMeet leftTree rightTree leftCarries rightCarries =>
        exact (BHistIndexedOpen_finite_intersection_closure T leftCarries rightCarries).left
    | arbitraryUnion children unionLaw childCarries =>
        exact (BHistIndexedOpen_arbitrary_union_closure T unionLaw childCarries).left
    | bottom boundary =>
        exact (BHistIndexedOpen_boundary_closure T boundary).left
    | top boundary =>
        exact (BHistIndexedOpen_boundary_closure T boundary).right.left
  exact And.intro (Exists.intro i carries) (BHistCarriesOpen_classifier_transport T carries)

theorem BHistGeneratedOpen_semantic_name_certificate (T : BHistIndexedOpenCarrier)
    {U : BHist -> Prop} (generated : BHistGeneratedOpenExact T U)
    (source : exists h : BHist, UnaryHistory h ∧ U h) :
    SemanticNameCert (fun h : BHist => UnaryHistory h ∧ U h) (fun h : BHist => U h)
      (fun h : BHist => BHistGeneratedOpenExact T U ∧ U h)
      (fun h k : BHist => UnaryHistory h ∧ UnaryHistory k ∧ hsame h k) := by
  exact {
    core := {
      carrier_inhabited := source
      equiv_refl := by
        intro h sourceH
        exact And.intro sourceH.left (And.intro sourceH.left (hsame_refl h))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      carrier_respects_equiv := by
        intro h k classified sourceH
        have transport :
            U h <-> U k :=
          BHistGeneratedOpen_classifier_transport T generated sourceH.left
            classified.right.left classified.right.right
        exact And.intro classified.right.left (Iff.mp transport sourceH.right)
    }
    pattern_sound := by
      intro h sourceH
      exact sourceH.right
    ledger_sound := by
      intro h sourceH
      exact And.intro generated sourceH.right
  }

theorem BHistGeneratedOpen_six_row_exactness_package
    (T : BHistIndexedOpenCarrier) {i j : T.OpenIx} {U V : BHist -> Prop} :
    BHistUnaryTopologyLedgerRow T i U ->
      BHistUnaryTopologyLedgerRow T j V ->
        BHistGeneratedOpenExact T U /\
          BHistGeneratedOpenExact T V /\
            BHistGeneratedOpenExact T (fun x : BHist => U x /\ V x) /\
              (exists ledger : BHist, UnaryHistory ledger) /\
                (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
                  (U x <-> U y)) := by
  intro rowU rowV
  have exactUAndTransport := BHistUnaryTopologyLedgerRow_generated_open_exactness T rowU
  have exactVAndTransport := BHistUnaryTopologyLedgerRow_generated_open_exactness T rowV
  have meetExact :=
    (BHistGeneratedOpen_binary_meet_admission T exactUAndTransport.left
      exactVAndTransport.left).left
  have ledgerWitness : exists ledger : BHist, UnaryHistory ledger := by
    cases rowU with
    | singletonMetricBall ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | finiteListIntersection ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | binaryGeneratedMeet ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | arbitraryUnion ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | bottom ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | top ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
  exact And.intro exactUAndTransport.left
    (And.intro exactVAndTransport.left
      (And.intro meetExact (And.intro ledgerWitness exactUAndTransport.right)))

end BEDC.Derived.TopologyUp
