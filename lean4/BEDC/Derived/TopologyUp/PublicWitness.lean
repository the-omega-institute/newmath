import BEDC.Derived.TopologyUp

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TopologySingleton_public_open_row_coverage :
    (BHistUnaryTopologyLedgerRow TopologySingletonIndexedOpenCarrier (BHist.e0 BHist.Empty)
        (fun _ : BHist => False) ∧
      BHistCarriesOpen TopologySingletonIndexedOpenCarrier (BHist.e0 BHist.Empty)
        (fun _ : BHist => False)) ∧
    (BHistUnaryTopologyLedgerRow TopologySingletonIndexedOpenCarrier BHist.Empty
        TopologySingletonCarrier ∧
      BHistCarriesOpen TopologySingletonIndexedOpenCarrier BHist.Empty
        TopologySingletonCarrier) := by
  have boundaryRows := TopologySingleton_semantic_name_certificate.right
  have bottomLaw :
      forall h : BHist, TopologySingletonOpenAt (BHist.e0 BHist.Empty) h <-> False :=
    boundaryRows.left
  have topLaw :
      forall h : BHist, TopologySingletonOpenAt BHist.Empty h <-> TopologySingletonCarrier h :=
    boundaryRows.right
  have bottomCarries :
      BHistCarriesOpen TopologySingletonIndexedOpenCarrier (BHist.e0 BHist.Empty)
        (fun _ : BHist => False) := by
    intro x _unaryX
    have bottomAt : TopologySingletonOpenAt (BHist.e0 BHist.Empty) x <-> False :=
      bottomLaw x
    constructor
    · intro impossible
      exact False.elim impossible
    · intro openBottom
      exact Iff.mp bottomAt openBottom
  have topCarries :
      BHistCarriesOpen TopologySingletonIndexedOpenCarrier BHist.Empty
        TopologySingletonCarrier := by
    intro x _unaryX
    have topAt : TopologySingletonOpenAt BHist.Empty x <-> TopologySingletonCarrier x :=
      topLaw x
    constructor
    · intro carrierX
      exact Iff.mpr topAt carrierX
    · intro openTop
      exact Iff.mp topAt openTop
  have bottomRow :
      BHistUnaryTopologyLedgerRow TopologySingletonIndexedOpenCarrier (BHist.e0 BHist.Empty)
        (fun _ : BHist => False) :=
    BHistUnaryTopologyLedgerRow.bottom BHist.Empty unary_empty bottomCarries
  have topRow :
      BHistUnaryTopologyLedgerRow TopologySingletonIndexedOpenCarrier BHist.Empty
        TopologySingletonCarrier :=
    BHistUnaryTopologyLedgerRow.top BHist.Empty unary_empty topCarries
  exact And.intro (And.intro bottomRow bottomCarries) (And.intro topRow topCarries)

theorem BHistGeneratedOpenExact_public_open_witness (T : BHistIndexedOpenCarrier)
    {U : BHist -> Prop} :
    BHistGeneratedOpenExact T U ->
      exists i : T.OpenIx, exists ledger : BHist,
        hsame ledger BHist.Empty ∧ BHistCarriesOpen T i U ∧ TopologyPublicOpenTree T i U := by
  intro generated
  cases generated with
  | intro i carries =>
      exact Exists.intro i
        (Exists.intro BHist.Empty
          (And.intro (hsame_refl BHist.Empty)
            (And.intro carries (TopologyPublicOpenTree.basic carries))))

end BEDC.Derived.TopologyUp
