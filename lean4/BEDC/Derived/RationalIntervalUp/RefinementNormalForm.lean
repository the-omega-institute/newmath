import BEDC.Derived.RationalIntervalUp

namespace BEDC.Derived.RationalIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RationalIntervalRefinement_terminal_seal_compatibility [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint width containmentRead
      boundary terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      Cont left right width ->
        Cont containment route containmentRead ->
          Cont endpoint width boundary ->
            Cont boundary containmentRead terminal ->
              PkgSig bundle terminal pkg ->
                UnaryHistory width ∧ UnaryHistory containmentRead ∧ UnaryHistory boundary ∧
                  UnaryHistory terminal ∧ hsame width order ∧
                    Cont boundary containmentRead terminal ∧ PkgSig bundle terminal pkg := by
  intro packet widthRow containmentReadRow boundaryRow terminalRow terminalPkg
  obtain ⟨leftUnary, rightUnary, _orderUnary, containmentUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameUnary, endpointUnary, orderRow, _containmentRow, _provenanceRow,
    _endpointRow, _endpointPkg⟩ := packet
  have widthUnary : UnaryHistory width :=
    unary_cont_closed leftUnary rightUnary widthRow
  have sameWidthOrder : hsame width order :=
    cont_deterministic widthRow orderRow
  have containmentReadUnary : UnaryHistory containmentRead :=
    unary_cont_closed containmentUnary routeUnary containmentReadRow
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed endpointUnary widthUnary boundaryRow
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed boundaryUnary containmentReadUnary terminalRow
  exact
    ⟨widthUnary, containmentReadUnary, boundaryUnary, terminalUnary, sameWidthOrder,
      terminalRow, terminalPkg⟩

end BEDC.Derived.RationalIntervalUp
