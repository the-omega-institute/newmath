import BEDC.Derived.RingedSpaceUp

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Hist
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp
open BEDC.Derived.SheafUp
open BEDC.Derived.TopologyUp

theorem SchemeSingleton_affine_cover_nerve_empty_boundary
    {point ambient member overlap route germ operationA operationB operationC : BHist} :
    TopologySingletonOpenAt BHist.Empty point ->
      SheafBHistCoverNerveLedger ambient member overlap route germ ->
        hsame germ BHist.Empty ->
          CommRingSingletonClassifier operationA operationB ->
            CommRingSingletonClassifier operationB operationC ->
              hsame overlap BHist.Empty ∧ hsame route BHist.Empty ∧
                CommRingSingletonClassifier operationA operationC ∧
                  TopologySingletonOpenAt BHist.Empty point := by
  intro openPoint ledger germEmpty commAB commBC
  have ringedBoundary :=
    RingedSpaceSingleton_cover_nerve_empty_boundary openPoint ledger germEmpty commAB
  have commAC : CommRingSingletonClassifier operationA operationC :=
    And.intro commAB.left
      (And.intro commBC.right.left
        (hsame_trans commAB.right.right commBC.right.right))
  exact And.intro ringedBoundary.left
    (And.intro ringedBoundary.right.left
      (And.intro commAC ringedBoundary.right.right.right))

end BEDC.Derived.SchemeUp
