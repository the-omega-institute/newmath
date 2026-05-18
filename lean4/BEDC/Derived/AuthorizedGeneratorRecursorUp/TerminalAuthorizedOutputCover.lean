import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCarrier_terminal_authorized_output_cover
    [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead auditRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont B D outputRead →
        Cont outputRead A auditRead →
          Cont auditRead N terminalRead →
            PkgSig bundle terminalRead pkg →
              UnaryHistory B ∧ UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory A ∧
                UnaryHistory N ∧ UnaryHistory outputRead ∧ UnaryHistory auditRead ∧
                  UnaryHistory terminalRead ∧ Cont B D outputRead ∧
                    Cont outputRead A auditRead ∧ Cont auditRead N terminalRead ∧
                      hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputCont auditCont terminalCont terminalPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, unaryB, unaryD, unaryO, unaryA, _unaryH, _unaryC,
      _unaryP, _unaryG, unaryN, _contIEM, _contMBD, _contDOA, sameTransport,
      provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryB unaryD outputCont
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed outputUnary unaryA auditCont
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed auditUnary unaryN terminalCont
  exact
    ⟨unaryB, unaryD, unaryO, unaryA, unaryN, outputUnary, auditUnary, terminalUnary,
      outputCont, auditCont, terminalCont, sameTransport, provenancePkg, terminalPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
