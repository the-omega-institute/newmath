import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.RatUp

theorem SOneHistoryCarrier_public_constructor_compatibility
    {x y equation point x' y' equation' point' : BHist} :
    SOneHistoryCarrier x y equation point -> hsame x x' -> hsame y y' ->
      hsame equation equation' -> hsame point point' ->
        SOneSourceSpec x y equation point ∧
          SOneLedgerPolicy x y equation point x' y' equation' point' ∧
            SemanticNameCert
              (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
              (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
              (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
              hsame ∧
              SOneProductHistoryCarrier point' ∧ hsame equation' SOneUnitHistory ∧
                Cont x' y' point' := by
  intro carrier sameX sameY sameEquation samePoint
  have sourceSpec : SOneSourceSpec x y equation point :=
    SOneSourceSpec_history_carrier_fields carrier
  have transportedCarrier : SOneHistoryCarrier x' y' equation' point' :=
    SOneHistoryCarrier_coordinate_transport carrier sameX sameY sameEquation samePoint
  have componentClassifier : SOneComponentClassifier x y equation point x' y' equation' point' :=
    And.intro carrier
      (And.intro transportedCarrier (And.intro sameX sameY))
  have ledgerPolicy : SOneLedgerPolicy x y equation point x' y' equation' point' :=
    SOneLedgerPolicy_component_readback componentClassifier
  have semanticCert :
      SemanticNameCert
        (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
        (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
        (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
        hsame :=
    sone_history_semantic_name_certificate carrier
  have transportedReadback :
      SOneProductHistoryCarrier point' ∧ hsame equation' SOneUnitHistory ∧
        ∃ dx dy : BHist,
          hsame x' (BHist.e1 dx) ∧ RatHistoryCarrier dx ∧
            hsame y' (BHist.e1 dy) ∧ RatHistoryCarrier dy ∧ Cont x' y' point' :=
    SOneHistoryCarrier_public_readback transportedCarrier
  exact And.intro sourceSpec
    (And.intro ledgerPolicy
      (And.intro semanticCert
        (And.intro transportedReadback.left
          (And.intro transportedReadback.right.left
            transportedCarrier.right.right.right))))

end BEDC.Derived.S1Up
