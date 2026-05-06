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

end BEDC.Derived.TopologyUp
