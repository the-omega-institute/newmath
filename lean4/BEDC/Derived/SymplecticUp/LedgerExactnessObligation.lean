import BEDC.Derived.SymplecticUp

namespace BEDC.Derived.SymplecticUp

open BEDC.Derived.DiffFormUp
open BEDC.Derived.ManifoldUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SymplecticObligationBoundary_ledger_exactness_obligation
    {manifold degree probe tensor scalar antisym ledger derivative raised closedWitness
      nondegWitness : BHist} :
    SymplecticObligationBoundary manifold degree probe tensor scalar antisym ledger derivative
        raised closedWitness nondegWitness ->
      ManifoldSingletonCarrier manifold ∧
        DiffFormExteriorDerivativeLedger scalar derivative degree raised probe probe tensor tensor
          scalar scalar antisym ledger ∧
        Cont raised BHist.Empty closedWitness ∧ Cont manifold scalar nondegWitness ∧
          hsame degree (BHist.e1 (BHist.e1 BHist.Empty)) ∧ UnaryHistory raised ∧
            UnaryHistory closedWitness ∧ UnaryHistory nondegWitness ∧
              (hsame closedWitness BHist.Empty -> False) := by
  intro boundary
  have obligations := SymplecticObligationBoundary_carrier_classifier_obligations boundary
  have closedRow := SymplecticObligationBoundary_closed_two_form_row boundary
  have nondegRow := SymplecticObligationBoundary_nondegeneracy_row boundary
  have closedNonempty := SymplecticObligationBoundary_closed_successor_not_empty boundary
  exact And.intro obligations.left
    (And.intro obligations.right.left
      (And.intro closedRow.left
        (And.intro nondegRow.left
          (And.intro obligations.right.right.left
            (And.intro obligations.right.right.right.right.left
              (And.intro closedRow.right.right
                (And.intro nondegRow.right.right.right closedNonempty)))))))

end BEDC.Derived.SymplecticUp
