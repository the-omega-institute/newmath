import BEDC.Derived.TopologyUp

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Hist
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

end BEDC.Derived.TopologyUp
