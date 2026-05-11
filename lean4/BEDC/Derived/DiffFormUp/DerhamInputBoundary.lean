import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormDerhamInputBoundary_source_scope
    {omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source leftLedger
      rightLedger tensorLedger : BHist} :
    DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor' scalar
        scalar' antisym source ->
      DiffFormWedgeDegreeLedger d (BHist.e1 BHist.Empty) dplus leftLedger rightLedger
          tensorLedger ->
        UnaryHistory omega ∧ UnaryHistory domega ∧ UnaryHistory d ∧ UnaryHistory dplus ∧
          UnaryHistory antisym ∧ UnaryHistory source ∧ Cont d (BHist.e1 BHist.Empty) dplus ∧
            hsame probe probe' ∧ hsame tensor tensor' ∧ hsame scalar scalar' ∧
              hsame leftLedger rightLedger := by
  intro derivativeLedger wedgeLedger
  exact And.intro derivativeLedger.left
    (And.intro derivativeLedger.right.left
      (And.intro derivativeLedger.right.right.left
        (And.intro derivativeLedger.right.right.right.left
          (And.intro derivativeLedger.right.right.right.right.right.right.right.right.left
            (And.intro derivativeLedger.right.right.right.right.right.right.right.right.right
              (And.intro wedgeLedger.right.right.left
                (And.intro derivativeLedger.right.right.right.right.right.left
                  (And.intro derivativeLedger.right.right.right.right.right.right.left
                    (And.intro derivativeLedger.right.right.right.right.right.right.right.left
                      wedgeLedger.right.right.right.right.right)))))))))

end BEDC.Derived.DiffFormUp
