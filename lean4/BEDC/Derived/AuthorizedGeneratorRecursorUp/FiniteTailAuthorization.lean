import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorFiniteTailAuthorization [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N tailRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A tailRead ->
        Cont tailRead N terminalRead ->
          PkgSig bundle terminalRead pkg ->
            UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory N ∧ UnaryHistory tailRead ∧
              UnaryHistory terminalRead ∧ Cont O A tailRead ∧
                Cont tailRead N terminalRead ∧ hsame H (append A C) ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputAuditTail tailTerminal terminalPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH,
      _unaryC, _unaryP, _unaryG, unaryN, _contIEM, _contMBD, _contDOA,
      sameTransport, provenancePkg⟩
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed unaryO unaryA outputAuditTail
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed tailUnary unaryN tailTerminal
  exact
    ⟨unaryO, unaryA, unaryN, tailUnary, terminalUnary, outputAuditTail,
      tailTerminal, sameTransport, provenancePkg, terminalPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
