import BEDC.Derived.RationalIntervalUp

namespace BEDC.Derived.RationalIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RationalIntervalPacket_normal_form_terminal_seal_compatibility
    [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint terminal
      normalTerminal containmentRead terminalSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      UnaryHistory terminal ->
        Cont endpoint terminal normalTerminal ->
          Cont containment route containmentRead ->
            Cont normalTerminal containmentRead terminalSeal ->
              PkgSig bundle terminalSeal pkg ->
                UnaryHistory normalTerminal ∧ UnaryHistory containmentRead ∧
                  UnaryHistory terminalSeal ∧ Cont endpoint terminal normalTerminal ∧
                    Cont containment route containmentRead ∧
                      Cont normalTerminal containmentRead terminalSeal ∧
                        PkgSig bundle terminalSeal pkg := by
  intro packet terminalUnary normalTerminalRow containmentReadRow sealRow sealPkg
  obtain ⟨_leftUnary, _rightUnary, _orderUnary, containmentUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameUnary, endpointUnary, _orderRow, _containmentRow, _provenanceRow,
    _endpointRow, _endpointPkg⟩ := packet
  have normalTerminalUnary : UnaryHistory normalTerminal :=
    unary_cont_closed endpointUnary terminalUnary normalTerminalRow
  have containmentReadUnary : UnaryHistory containmentRead :=
    unary_cont_closed containmentUnary routeUnary containmentReadRow
  have terminalSealUnary : UnaryHistory terminalSeal :=
    unary_cont_closed normalTerminalUnary containmentReadUnary sealRow
  exact
    ⟨normalTerminalUnary, containmentReadUnary, terminalSealUnary, normalTerminalRow,
      containmentReadRow, sealRow, sealPkg⟩

end BEDC.Derived.RationalIntervalUp
