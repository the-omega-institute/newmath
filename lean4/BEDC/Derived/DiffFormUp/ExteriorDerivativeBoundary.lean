import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormExteriorDerivativeLedger_classifier_transport_nonempty_boundary
    {omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source omega2 domega2
      d2 dplus2 probe2 probe2' tensor2 tensor2' scalar2 scalar2' antisym2 source2 : BHist}
    {probes : ProbeBundle BHist} :
    DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor' scalar
      scalar' antisym source ->
    DiffFormBHistClassifier hsame probes d probe tensor scalar antisym source d2 probe2 tensor2
      scalar2 antisym2 source2 ->
    hsame omega omega2 -> hsame domega domega2 -> hsame d d2 -> hsame dplus dplus2 ->
    hsame probe' probe2' -> hsame tensor' tensor2' -> hsame scalar' scalar2' ->
      DiffFormExteriorDerivativeLedger omega2 domega2 d2 dplus2 probe2 probe2' tensor2 tensor2'
          scalar2 scalar2' antisym2 source2 ∧
        (hsame dplus2 BHist.Empty -> False) ∧ UnaryHistory d2 ∧ UnaryHistory antisym2 := by
  intro ledger classified sameOmega sameDomega sameD sameDplus sameProbe' sameTensor'
    sameScalar'
  have transported :
      DiffFormExteriorDerivativeLedger omega2 domega2 d2 dplus2 probe2 probe2' tensor2
        tensor2' scalar2 scalar2' antisym2 source2 :=
    DiffFormExteriorDerivativeLedger_classifier_transport ledger classified sameOmega sameDomega
      sameD sameDplus sameProbe' sameTensor' sameScalar'
  have boundaryRows :=
    DiffFormExteriorDerivativeLedger_degree_successor_nonempty transported
  exact And.intro transported
    (And.intro boundaryRows.right.right.right
      (And.intro boundaryRows.left transported.right.right.right.right.right.right.right.right.left))

end BEDC.Derived.DiffFormUp
