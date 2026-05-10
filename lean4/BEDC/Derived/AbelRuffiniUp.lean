import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.AbelRuffiniUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem AbelRuffiniDerivedSeriesLedger_assoc_surface
    {galois sym commutator subgroup next : BHist} :
    UnaryHistory galois -> UnaryHistory sym -> UnaryHistory commutator ->
      Cont galois sym subgroup -> Cont subgroup commutator next ->
        ∃ tail : BHist, ∃ packed : BHist,
          Cont sym commutator tail ∧ Cont galois tail packed ∧ UnaryHistory subgroup ∧
            UnaryHistory tail ∧ UnaryHistory next ∧ UnaryHistory packed ∧ hsame next packed := by
  intro galoisUnary symUnary commutatorUnary subgroupRow nextRow
  have subgroupUnary : UnaryHistory subgroup :=
    unary_cont_closed galoisUnary symUnary subgroupRow
  have nextUnary : UnaryHistory next :=
    unary_cont_closed subgroupUnary commutatorUnary nextRow
  cases cont_assoc_left_exists subgroupRow nextRow with
  | intro tail repacked =>
      have tailUnary : UnaryHistory tail :=
        unary_cont_closed symUnary commutatorUnary repacked.left
      exact
        ⟨tail, next, repacked.left, repacked.right, subgroupUnary, tailUnary, nextUnary,
          nextUnary, hsame_refl next⟩

theorem AbelRuffiniPolynomialGaloisObligation_source_surface
    {polynomial base splittingField galoisRow s5Row coefficientLedger galoisLedger
      sourceSurface : BHist} :
    UnaryHistory polynomial ->
      UnaryHistory base ->
        UnaryHistory splittingField ->
          UnaryHistory galoisRow ->
            Cont polynomial base coefficientLedger ->
              Cont splittingField galoisRow galoisLedger ->
                Cont coefficientLedger galoisLedger sourceSurface ->
                  UnaryHistory coefficientLedger ∧ UnaryHistory galoisLedger ∧
                    UnaryHistory sourceSurface ∧
                      hsame coefficientLedger (append polynomial base) ∧
                        hsame galoisLedger (append splittingField galoisRow) ∧
                          hsame sourceSurface (append coefficientLedger galoisLedger) := by
  intro polynomialUnary baseUnary splittingFieldUnary galoisRowUnary
  intro coefficientRow galoisLedgerRow sourceSurfaceRow
  have coefficientUnary : UnaryHistory coefficientLedger :=
    unary_cont_closed polynomialUnary baseUnary coefficientRow
  have galoisLedgerUnary : UnaryHistory galoisLedger :=
    unary_cont_closed splittingFieldUnary galoisRowUnary galoisLedgerRow
  have sourceSurfaceUnary : UnaryHistory sourceSurface :=
    unary_cont_closed coefficientUnary galoisLedgerUnary sourceSurfaceRow
  exact
    ⟨coefficientUnary,
      galoisLedgerUnary,
      sourceSurfaceUnary,
      coefficientRow,
      galoisLedgerRow,
      sourceSurfaceRow⟩

theorem AbelRuffiniDerivedSeriesLedger_finite_transport
    {galois s5 subgroup commutator next obstruction endpoint : BHist} :
    UnaryHistory galois -> UnaryHistory s5 -> UnaryHistory subgroup ->
      UnaryHistory commutator -> UnaryHistory obstruction ->
        Cont galois s5 subgroup -> Cont subgroup commutator next ->
          Cont next obstruction endpoint ->
            UnaryHistory next ∧ UnaryHistory endpoint ∧
              hsame subgroup (append galois s5) ∧ hsame next (append subgroup commutator) ∧
                hsame endpoint (append next obstruction) := by
  intro galoisUnary s5Unary subgroupUnary commutatorUnary obstructionUnary
  intro subgroupRow nextRow endpointRow
  have nextUnary : UnaryHistory next :=
    unary_cont_closed subgroupUnary commutatorUnary nextRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed nextUnary obstructionUnary endpointRow
  exact ⟨nextUnary, endpointUnary, subgroupRow, nextRow, endpointRow⟩

theorem AbelRuffiniNonradicalBoundary_obligation
    {polynomial base splittingField galoisRow s5Row coefficientLedger galoisLedger
      sourceSurface commutator subgroup next obstruction boundary : BHist} :
    UnaryHistory polynomial -> UnaryHistory base -> UnaryHistory splittingField ->
      UnaryHistory galoisRow -> UnaryHistory s5Row -> UnaryHistory commutator ->
        UnaryHistory obstruction -> Cont polynomial base coefficientLedger ->
          Cont splittingField galoisRow galoisLedger ->
            Cont coefficientLedger galoisLedger sourceSurface ->
              Cont galoisRow s5Row subgroup -> Cont subgroup commutator next ->
                Cont next obstruction boundary ->
                  UnaryHistory sourceSurface ∧ UnaryHistory subgroup ∧ UnaryHistory next ∧
                    UnaryHistory boundary ∧
                      hsame sourceSurface (append coefficientLedger galoisLedger) ∧
                        hsame subgroup (append galoisRow s5Row) ∧
                          hsame next (append subgroup commutator) ∧
                            hsame boundary (append next obstruction) := by
  intro polynomialUnary baseUnary splittingFieldUnary galoisRowUnary s5RowUnary
  intro commutatorUnary obstructionUnary coefficientRow galoisLedgerRow sourceSurfaceRow
  intro subgroupRow nextRow boundaryRow
  have coefficientUnary : UnaryHistory coefficientLedger :=
    unary_cont_closed polynomialUnary baseUnary coefficientRow
  have galoisLedgerUnary : UnaryHistory galoisLedger :=
    unary_cont_closed splittingFieldUnary galoisRowUnary galoisLedgerRow
  have sourceSurfaceUnary : UnaryHistory sourceSurface :=
    unary_cont_closed coefficientUnary galoisLedgerUnary sourceSurfaceRow
  have subgroupUnary : UnaryHistory subgroup :=
    unary_cont_closed galoisRowUnary s5RowUnary subgroupRow
  have nextUnary : UnaryHistory next :=
    unary_cont_closed subgroupUnary commutatorUnary nextRow
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed nextUnary obstructionUnary boundaryRow
  exact
    ⟨sourceSurfaceUnary, subgroupUnary, nextUnary, boundaryUnary, sourceSurfaceRow, subgroupRow,
      nextRow, boundaryRow⟩

end BEDC.Derived.AbelRuffiniUp
