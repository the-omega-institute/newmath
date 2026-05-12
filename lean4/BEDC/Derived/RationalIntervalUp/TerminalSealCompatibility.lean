import BEDC.Derived.RationalIntervalUp

namespace BEDC.Derived.RationalIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RationalIntervalPacket_terminal_seal_reassociation_witness [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint read folded terminal :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      UnaryHistory read ->
        Cont endpoint read folded ->
          Cont folded provenance terminal ->
            exists tail : BHist, exists terminal' : BHist,
              Cont read provenance tail ∧ Cont endpoint tail terminal' ∧
                hsame terminal terminal' ∧ UnaryHistory tail ∧ UnaryHistory terminal' := by
  intro packet readUnary endpointReadRow foldedProvenanceRow
  obtain ⟨_leftUnary, _rightUnary, _orderUnary, _containmentUnary, _transportUnary,
    _routeUnary, provenanceUnary, _nameUnary, endpointUnary, _orderRow, _containmentRow,
    _provenanceRow, _endpointRow, _endpointPkg⟩ := packet
  cases cont_assoc_left_exists endpointReadRow foldedProvenanceRow with
  | intro tail reassociated =>
      have tailUnary : UnaryHistory tail :=
        unary_cont_closed readUnary provenanceUnary reassociated.left
      have terminalUnary : UnaryHistory terminal :=
        unary_cont_closed
          (unary_cont_closed endpointUnary readUnary endpointReadRow) provenanceUnary
          foldedProvenanceRow
      exact
        ⟨tail, terminal, reassociated.left, reassociated.right, hsame_refl terminal,
          tailUnary, terminalUnary⟩

end BEDC.Derived.RationalIntervalUp
