import BEDC.Derived.DiffFormUp.RootConsumerFace

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DiffFormRootBoundaryConsumer_exactness {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger dplus outDegree rightLedger tensorLedger :
      BHist} :
    InBundle probe probes -> ScalarCarrier scalar -> UnaryHistory degree -> UnaryHistory probe ->
      Cont degree probe tensor -> UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          Cont degree (BHist.e1 BHist.Empty) dplus -> Cont degree dplus outDegree ->
            UnaryHistory rightLedger -> hsame ledger rightLedger -> UnaryHistory tensorLedger ->
              DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym
                  ledger degree probe tensor scalar antisym ledger ∧
                DiffFormExteriorDerivativeLedger scalar dplus degree dplus probe probe tensor
                  tensor scalar scalar antisym ledger ∧
                  DiffFormWedgeDegreeLedger degree dplus outDegree ledger rightLedger
                    tensorLedger ∧
                    UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧
                      UnaryHistory scalar := by
  intro probeIn scalarCarrier degreeUnary probeUnary tensorRoute antisymUnary scalarRoute
    ledgerRoute degreeSuccessor wedgeRoute rightLedgerUnary sameRightLedger tensorLedgerUnary
  have routed :
      DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym ledger
          degree probe tensor scalar antisym ledger ∧
        DiffFormExteriorDerivativeLedger scalar dplus degree dplus probe probe tensor tensor
          scalar scalar antisym ledger ∧
          DiffFormWedgeDegreeLedger degree dplus outDegree ledger rightLedger tensorLedger :=
    DiffFormRootConsumerPackage_operation_routing scalarCert probeIn scalarCarrier degreeUnary
      probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute degreeSuccessor wedgeRoute
      rightLedgerUnary sameRightLedger tensorLedgerUnary
  have carrierRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  exact And.intro routed.left
    (And.intro routed.right.left
      (And.intro routed.right.right
        (And.intro carrierRows.left
          (And.intro carrierRows.right.left
            (And.intro carrierRows.right.right.left carrierRows.right.right.right.left)))))

theorem DiffFormRootBoundaryConsumer_classifier_scope
    {omega domega degree degreePlus probe probe' tensor tensor' scalar scalar' antisym source
      omega2 domega2 degree2 degreePlus2 probe2 probe2' tensor2 tensor2' scalar2 scalar2'
      antisym2 source2 wedge wedge2 : BHist} :
    hsame omega omega2 -> hsame domega domega2 -> hsame degree degree2 ->
      hsame degreePlus degreePlus2 -> hsame probe probe2 -> hsame probe' probe2' ->
        hsame tensor tensor2 -> hsame tensor' tensor2' -> hsame scalar scalar2 ->
          hsame scalar' scalar2' -> hsame antisym antisym2 -> hsame source source2 ->
            hsame wedge wedge2 ->
              DiffFormExteriorDerivativeLedger omega domega degree degreePlus probe probe'
                  tensor tensor' scalar scalar' antisym source ->
                DiffFormWedgeDegreeLedger degree degreePlus wedge omega domega tensor ->
                  DiffFormExteriorDerivativeLedger omega2 domega2 degree2 degreePlus2 probe2
                      probe2' tensor2 tensor2' scalar2 scalar2' antisym2 source2 ∧
                    DiffFormWedgeDegreeLedger degree2 degreePlus2 wedge2 omega domega tensor ∧
                      UnaryHistory degree2 ∧ UnaryHistory degreePlus2 ∧
                        Cont degree2 (BHist.e1 BHist.Empty) degreePlus2 := by
  intro sameOmega sameDomega sameDegree sameDegreePlus sameProbe sameProbe' sameTensor
    sameTensor' sameScalar sameScalar' sameAntisym sameSource sameWedge derivativeLedger
    wedgeLedger
  have transportedDerivative :=
    DiffFormExteriorDerivativeLedger_hsame_transport_degree_raise sameOmega sameDomega
      sameDegree sameDegreePlus sameProbe sameProbe' sameTensor sameTensor' sameScalar
      sameScalar' sameAntisym sameSource derivativeLedger
  have transportedWedge :=
    DiffFormWedgeDegreeLedger_classifier_stability wedgeLedger sameDegree sameDegreePlus
      sameWedge
  exact
    ⟨transportedDerivative.left,
      transportedWedge.left,
      transportedDerivative.right.left,
      transportedDerivative.right.right.left,
      transportedDerivative.right.right.right⟩

end BEDC.Derived.DiffFormUp
