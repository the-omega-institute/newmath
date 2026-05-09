import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormDownstreamBoundary_exterior_wedge_common_rows
    {omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source leftDegree
      rightDegree wedge leftLedger rightLedger tensorLedger : BHist} :
    DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor' scalar
        scalar' antisym source ->
      DiffFormWedgeDegreeLedger leftDegree rightDegree wedge leftLedger rightLedger
          tensorLedger ->
        hsame d leftDegree ->
          UnaryHistory domega ∧ UnaryHistory dplus ∧ UnaryHistory wedge ∧
            Cont d (BHist.e1 BHist.Empty) dplus ∧ Cont leftDegree rightDegree wedge ∧
              hsame leftLedger rightLedger := by
  intro exterior wedgeLedger _sameDegree
  exact
    ⟨exterior.right.left, exterior.right.right.right.left,
      wedgeLedger.right.right.right.left, exterior.right.right.right.right.left,
      wedgeLedger.right.right.left, wedgeLedger.right.right.right.right.right⟩

end BEDC.Derived.DiffFormUp
