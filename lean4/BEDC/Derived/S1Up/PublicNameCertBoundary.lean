import BEDC.Derived.S1Up.RealMetricBridgeBoundary

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem SOneHistoryCarrier_public_certificate_boundary {x y equation point metricLedger : BHist} :
    SOneHistoryCarrier x y equation point -> Cont point equation metricLedger ->
      SemanticNameCert
          (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
          (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
          (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
          hsame ∧
        UnaryHistory metricLedger ∧ SOneProductHistoryCarrier point ∧
          hsame equation SOneUnitHistory ∧
            exists dx dy : BHist,
              hsame x (BHist.e1 dx) ∧ RatHistoryCarrier dx ∧
                hsame y (BHist.e1 dy) ∧ RatHistoryCarrier dy ∧ Cont x y point := by
  intro carrier metricCont
  have cert :
      SemanticNameCert
          (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
          (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
          (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
          hsame :=
    sone_history_semantic_name_certificate carrier
  have metricRows :=
    SOneRegSeqRatMetricObservationBoundary_public_rows carrier metricCont
  exact And.intro cert
    (And.intro metricRows.left
      (And.intro metricRows.right.left
        (And.intro metricRows.right.right.left metricRows.right.right.right)))

end BEDC.Derived.S1Up
