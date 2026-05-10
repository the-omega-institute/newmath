import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormExteriorInputBoundary_obligation
    {ScalarClassifier : BHist -> BHist -> Prop} {probes : ProbeBundle BHist}
    {omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source d2 probe2
      tensor2 scalar2 antisym2 source2 : BHist} :
    DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor' scalar
      scalar' antisym source ->
    DiffFormBHistClassifier ScalarClassifier probes d probe tensor scalar antisym source d2 probe2
      tensor2 scalar2 antisym2 source2 ->
      UnaryHistory omega ∧ UnaryHistory domega ∧ UnaryHistory d ∧ UnaryHistory dplus ∧
        Cont d (BHist.e1 BHist.Empty) dplus ∧ hsame probe probe' ∧
          hsame tensor tensor' ∧ hsame scalar scalar' ∧ hsame source source2 := by
  intro ledger classified
  exact
    ⟨ledger.left,
      ledger.right.left,
      ledger.right.right.left,
      ledger.right.right.right.left,
      ledger.right.right.right.right.left,
      ledger.right.right.right.right.right.left,
      ledger.right.right.right.right.right.right.left,
      ledger.right.right.right.right.right.right.right.left,
      classified.right.right.right.right.right.right.right⟩

theorem DiffFormRootConsumerWedgeInput_readback
    {leftDegree rightDegree outDegree leftLedger rightLedger tensorLedger omega domega d dplus
      probe probe' tensor tensor' scalar scalar' antisym source : BHist} :
    DiffFormWedgeDegreeLedger leftDegree rightDegree outDegree leftLedger rightLedger tensorLedger ->
    DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor' scalar
      scalar' antisym source ->
      UnaryHistory outDegree ∧ UnaryHistory tensorLedger ∧ hsame leftLedger rightLedger ∧
        UnaryHistory dplus ∧ Cont d (BHist.e1 BHist.Empty) dplus := by
  intro wedgeLedger exteriorLedger
  exact
    ⟨wedgeLedger.right.right.right.left,
      wedgeLedger.right.right.right.right.left,
      wedgeLedger.right.right.right.right.right,
      exteriorLedger.right.right.right.left,
      exteriorLedger.right.right.right.right.left⟩

end BEDC.Derived.DiffFormUp
