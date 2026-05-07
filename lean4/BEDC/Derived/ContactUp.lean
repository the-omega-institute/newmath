import BEDC.Derived.DiffFormUp
import BEDC.Derived.ManifoldUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ContactUp

open BEDC.Derived.DiffFormUp
open BEDC.Derived.ManifoldUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ContactUpFormRow_wedge_derivative_surface
    {manifold omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source
      rightDegree outDegree leftLedger rightLedger tensorLedger chart : BHist} :
    ManifoldSingletonCarrier manifold ->
      DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor'
        scalar scalar' antisym source ->
        DiffFormWedgeDegreeLedger d rightDegree outDegree leftLedger rightLedger
          tensorLedger ->
          Cont BHist.Empty manifold chart ->
            hsame chart BHist.Empty ∧ UnaryHistory omega ∧ UnaryHistory domega ∧
              UnaryHistory d ∧ UnaryHistory dplus ∧ Cont d (BHist.e1 BHist.Empty) dplus ∧
                UnaryHistory outDegree ∧ hsame leftLedger rightLedger := by
  intro manifoldCarrier derivativeLedger wedgeLedger chartRow
  have chartManifold : hsame chart manifold :=
    cont_left_unit_result chartRow
  have chartEmpty : hsame chart BHist.Empty :=
    hsame_trans chartManifold manifoldCarrier
  have degreeRaise :
      UnaryHistory d ∧ UnaryHistory dplus ∧ Cont d (BHist.e1 BHist.Empty) dplus :=
    DiffFormExteriorDerivativeLedger_degree_raise derivativeLedger
  exact And.intro chartEmpty
    (And.intro derivativeLedger.left
      (And.intro derivativeLedger.right.left
        (And.intro degreeRaise.left
          (And.intro degreeRaise.right.left
            (And.intro degreeRaise.right.right
              (And.intro wedgeLedger.right.right.right.left
                wedgeLedger.right.right.right.right.right))))))

end BEDC.Derived.ContactUp
