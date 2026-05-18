import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorTerminalOutputReadiness [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead terminalRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead N terminalRead ->
          Cont terminalRead G auditRead ->
            PkgSig bundle auditRead pkg ->
              UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory N ∧ UnaryHistory outputRead ∧
                UnaryHistory terminalRead ∧ UnaryHistory auditRead ∧ Cont D O A ∧
                  Cont O A outputRead ∧ Cont outputRead N terminalRead ∧
                    Cont terminalRead G auditRead ∧ hsame H (append A C) ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputReadRow terminalReadRow auditReadRow auditReadPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, unaryD, unaryO, unaryA, _unaryH, unaryC,
      packageUnary, unaryG, unaryN, _rootMotive, _branchDescent, descentOutputAudit,
      transportSame, packagePkg⟩
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputReadRow
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed outputReadUnary unaryN terminalReadRow
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed terminalReadUnary unaryG auditReadRow
  exact
    ⟨unaryO, unaryA, unaryN, outputReadUnary, terminalReadUnary, auditReadUnary,
      descentOutputAudit, outputReadRow, terminalReadRow, auditReadRow, transportSame,
      packagePkg, auditReadPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
