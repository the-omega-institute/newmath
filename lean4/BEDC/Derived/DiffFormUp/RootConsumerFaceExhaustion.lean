import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def DiffFormRootConsumerFaceExhaustionSource
    (root carrier classifier wedge derivative ledger endpoint : BHist) : Prop :=
  UnaryHistory root ∧ UnaryHistory carrier ∧ UnaryHistory classifier ∧
    UnaryHistory derivative ∧ Cont carrier classifier wedge ∧ Cont wedge derivative ledger ∧
      Cont root ledger endpoint

theorem DiffFormRootConsumerFaceExhaustionSource_boundary_exactness
    {root carrier classifier wedge derivative ledger endpoint : BHist} :
    DiffFormRootConsumerFaceExhaustionSource root carrier classifier wedge derivative ledger
        endpoint ->
      UnaryHistory wedge ∧ UnaryHistory ledger ∧ UnaryHistory endpoint ∧
        hsame wedge (append carrier classifier) ∧ hsame ledger (append wedge derivative) ∧
          hsame endpoint (append root ledger) := by
  intro source
  have rootUnary : UnaryHistory root := source.left
  have carrierUnary : UnaryHistory carrier := source.right.left
  have classifierUnary : UnaryHistory classifier := source.right.right.left
  have derivativeUnary : UnaryHistory derivative := source.right.right.right.left
  have wedgeRow : Cont carrier classifier wedge := source.right.right.right.right.left
  have ledgerRow : Cont wedge derivative ledger := source.right.right.right.right.right.left
  have endpointRow : Cont root ledger endpoint := source.right.right.right.right.right.right
  have wedgeUnary : UnaryHistory wedge :=
    unary_cont_closed carrierUnary classifierUnary wedgeRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed wedgeUnary derivativeUnary ledgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed rootUnary ledgerUnary endpointRow
  exact ⟨wedgeUnary, ledgerUnary, endpointUnary, wedgeRow, ledgerRow, endpointRow⟩

theorem DiffFormRootConsumerFaceExhaustionSource_exhaustion
    {root carrier classifier wedge derivative ledger endpoint : BHist} :
    DiffFormRootConsumerFaceExhaustionSource root carrier classifier wedge derivative ledger
        endpoint ->
      UnaryHistory root ∧ UnaryHistory carrier ∧ UnaryHistory classifier ∧
        UnaryHistory derivative ∧ UnaryHistory wedge ∧ UnaryHistory ledger ∧
          UnaryHistory endpoint ∧ Cont carrier classifier wedge ∧
            Cont wedge derivative ledger ∧ Cont root ledger endpoint := by
  intro source
  have rootUnary : UnaryHistory root := source.left
  have carrierUnary : UnaryHistory carrier := source.right.left
  have classifierUnary : UnaryHistory classifier := source.right.right.left
  have derivativeUnary : UnaryHistory derivative := source.right.right.right.left
  have wedgeRow : Cont carrier classifier wedge := source.right.right.right.right.left
  have ledgerRow : Cont wedge derivative ledger := source.right.right.right.right.right.left
  have endpointRow : Cont root ledger endpoint := source.right.right.right.right.right.right
  have wedgeUnary : UnaryHistory wedge :=
    unary_cont_closed carrierUnary classifierUnary wedgeRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed wedgeUnary derivativeUnary ledgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed rootUnary ledgerUnary endpointRow
  exact
    ⟨rootUnary, carrierUnary, classifierUnary, derivativeUnary, wedgeUnary, ledgerUnary,
      endpointUnary, wedgeRow, ledgerRow, endpointRow⟩

end BEDC.Derived.DiffFormUp
