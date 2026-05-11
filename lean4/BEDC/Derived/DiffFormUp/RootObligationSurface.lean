import BEDC.Derived.DiffFormUp.ExteriorDerivativeBoundary
import BEDC.Derived.DiffFormUp.RootConsumerFace

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DiffFormRootExteriorDerivative_boundary_obligation
    {probes : ProbeBundle BHist}
    {omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source omega2
      domega2 d2 dplus2 probe2 probe2' tensor2 tensor2' scalar2 scalar2' antisym2 source2 :
        BHist} :
    DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor' scalar
      scalar' antisym source ->
    DiffFormBHistClassifier hsame probes d probe tensor scalar antisym source d2 probe2 tensor2
      scalar2 antisym2 source2 ->
    hsame omega omega2 -> hsame domega domega2 -> hsame d d2 -> hsame dplus dplus2 ->
    hsame probe' probe2' -> hsame tensor' tensor2' -> hsame scalar' scalar2' ->
      DiffFormExteriorDerivativeLedger omega2 domega2 d2 dplus2 probe2 probe2' tensor2
          tensor2' scalar2 scalar2' antisym2 source2 ∧
        DiffFormBHistClassifier hsame probes d probe tensor scalar antisym source d2 probe2
          tensor2 scalar2 antisym2 source2 ∧
          Cont d2 (BHist.e1 BHist.Empty) dplus2 ∧
            (hsame dplus2 BHist.Empty -> False) := by
  intro ledger classified sameOmega sameDomega sameD sameDplus sameProbe' sameTensor'
    sameScalar'
  have transported :
      DiffFormExteriorDerivativeLedger omega2 domega2 d2 dplus2 probe2 probe2' tensor2
        tensor2' scalar2 scalar2' antisym2 source2 :=
    DiffFormExteriorDerivativeLedger_classifier_transport ledger classified sameOmega sameDomega
      sameD sameDplus sameProbe' sameTensor' sameScalar'
  have boundaryRows :=
    DiffFormExteriorDerivativeLedger_degree_successor_nonempty transported
  exact
    ⟨transported,
      classified,
      boundaryRows.right.right.left,
      boundaryRows.right.right.right⟩

theorem DiffFormRootWedgeAntisymmetry_obligation {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger dplus outDegree rightLedger tensorLedger :
      BHist} :
    InBundle probe probes -> ScalarCarrier scalar -> UnaryHistory degree -> UnaryHistory probe ->
      UnaryHistory antisym -> Cont degree probe tensor -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          Cont degree (BHist.e1 BHist.Empty) dplus ->
            DiffFormWedgeDegreeLedger degree dplus outDegree ledger rightLedger tensorLedger ->
              DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym
                  ledger degree probe tensor scalar antisym ledger ∧
                DiffFormWedgeDegreeLedger degree dplus outDegree ledger rightLedger
                  tensorLedger ∧
                  UnaryHistory tensor ∧ UnaryHistory scalar ∧
                    (hsame dplus BHist.Empty -> False) := by
  intro probeIn scalarCarrier degreeUnary probeUnary antisymUnary tensorRoute scalarRoute
    ledgerRoute degreeSuccessor wedgeLedger
  have coverage :
      DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym ledger
          degree probe tensor scalar antisym ledger ∧
        UnaryHistory dplus ∧
          DiffFormExteriorDerivativeLedger scalar dplus degree dplus probe probe tensor tensor
            scalar scalar antisym ledger :=
    DiffFormRootConsumerFace_coverage scalarCert probeIn scalarCarrier degreeUnary probeUnary
      tensorRoute antisymUnary scalarRoute ledgerRoute degreeSuccessor
  have coordinateRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  have boundaryRows :=
    DiffFormExteriorDerivativeLedger_degree_successor_nonempty coverage.right.right
  exact
    ⟨coverage.left,
      wedgeLedger,
      coordinateRows.right.right.left,
      coordinateRows.right.right.right.left,
      boundaryRows.right.right.right⟩

end BEDC.Derived.DiffFormUp
