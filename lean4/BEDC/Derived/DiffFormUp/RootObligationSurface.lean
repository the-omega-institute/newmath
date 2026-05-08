import BEDC.Derived.DiffFormUp.ExteriorDerivativeBoundary

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

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

end BEDC.Derived.DiffFormUp
