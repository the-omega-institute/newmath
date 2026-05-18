import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorTerminalReaderNonescape [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead outputRead terminalRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont B D branchRead ->
        Cont O A outputRead ->
          Cont outputRead N terminalRead ->
            Cont terminalRead G auditRead ->
              PkgSig bundle auditRead pkg ->
                UnaryHistory B ∧ UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory A ∧
                  UnaryHistory N ∧ UnaryHistory branchRead ∧ UnaryHistory outputRead ∧
                    UnaryHistory terminalRead ∧ UnaryHistory auditRead ∧
                      Cont B D branchRead ∧ Cont O A outputRead ∧
                        Cont outputRead N terminalRead ∧ Cont terminalRead G auditRead ∧
                          hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier branchRow outputRow terminalRow auditRow auditPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, unaryB, unaryD, unaryO, unaryA, _unaryH, _unaryC,
      _provenanceUnary, unaryG, unaryN, _rootMotive, _branchDescent, _descentOutputAudit,
      transportSame, provenancePkg⟩
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryB unaryD branchRow
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRow
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed outputUnary unaryN terminalRow
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed terminalUnary unaryG auditRow
  exact
    ⟨unaryB, unaryD, unaryO, unaryA, unaryN, branchUnary, outputUnary,
      terminalUnary, auditUnary, branchRow, outputRow, terminalRow, auditRow,
      transportSame, provenancePkg, auditPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
