import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorAcceptanceBudgetCover
    [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N budgetRead auditRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont B D budgetRead →
        Cont O A auditRead →
          Cont auditRead N terminalRead →
            PkgSig bundle terminalRead pkg →
              UnaryHistory I ∧ UnaryHistory E ∧ UnaryHistory M ∧ UnaryHistory B ∧
                UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory G ∧
                  UnaryHistory N ∧ UnaryHistory budgetRead ∧ UnaryHistory auditRead ∧
                    UnaryHistory terminalRead ∧ Cont B D budgetRead ∧
                      Cont O A auditRead ∧ Cont auditRead N terminalRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier budgetCont auditCont terminalCont terminalPkg
  rcases carrier with
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, _unaryH, _unaryC,
      _unaryP, unaryG, unaryN, _contIEM, _contMBD, _contDOA, _sameTransport,
      provenancePkg⟩
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed unaryB unaryD budgetCont
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed unaryO unaryA auditCont
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed auditUnary unaryN terminalCont
  exact
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryG, unaryN,
      budgetUnary, auditUnary, terminalUnary, budgetCont, auditCont, terminalCont,
      provenancePkg, terminalPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
