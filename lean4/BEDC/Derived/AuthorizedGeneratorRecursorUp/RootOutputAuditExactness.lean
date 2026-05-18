import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootOutputAuditExactness [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead auditRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont O A outputRead →
        Cont outputRead N auditRead →
          Cont auditRead G terminalRead →
            PkgSig bundle terminalRead pkg →
              UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧
                UnaryHistory P ∧ UnaryHistory G ∧ UnaryHistory N ∧
                  UnaryHistory outputRead ∧ UnaryHistory auditRead ∧
                    UnaryHistory terminalRead ∧ Cont O A outputRead ∧
                      Cont outputRead N auditRead ∧ Cont auditRead G terminalRead ∧
                        hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputRoute auditRoute terminalRoute terminalPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, unaryH,
      unaryC, unaryP, unaryG, unaryN, _rootMotive, _branchDescent, _descentAudit,
      transportSame, packagePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed outputUnary unaryN auditRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed auditUnary unaryG terminalRoute
  exact
    ⟨unaryO, unaryA, unaryH, unaryC, unaryP, unaryG, unaryN, outputUnary, auditUnary,
      terminalUnary, outputRoute, auditRoute, terminalRoute, transportSame, packagePkg,
      terminalPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
