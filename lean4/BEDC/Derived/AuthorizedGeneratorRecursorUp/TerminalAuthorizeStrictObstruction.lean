import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorTerminalAuthorizeStrictObstruction [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead outputRead auditRead terminalUse obstruction : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont B D branchRead →
        Cont branchRead O outputRead →
          Cont A G auditRead →
            Cont outputRead auditRead terminalUse →
              Cont terminalUse N obstruction →
                PkgSig bundle obstruction pkg →
                  UnaryHistory branchRead ∧ UnaryHistory outputRead ∧
                    UnaryHistory auditRead ∧ UnaryHistory terminalUse ∧
                      UnaryHistory obstruction ∧ Cont B D branchRead ∧
                        Cont branchRead O outputRead ∧ Cont A G auditRead ∧
                          Cont outputRead auditRead terminalUse ∧
                            Cont terminalUse N obstruction ∧ hsame H (append A C) ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle obstruction pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier branchRoute outputRoute auditRoute terminalRoute obstructionRoute obstructionPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, unaryB, unaryD, unaryO, unaryA, _unaryH, _unaryC,
      provenanceUnary, unaryG, unaryN, _rootMotive, _branchDescent, _descentAudit,
      transportSame, provenancePkg⟩
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryB unaryD branchRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed branchUnary unaryO outputRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed unaryA unaryG auditRoute
  have terminalUnary : UnaryHistory terminalUse :=
    unary_cont_closed outputUnary auditUnary terminalRoute
  have obstructionUnary : UnaryHistory obstruction :=
    unary_cont_closed terminalUnary unaryN obstructionRoute
  exact
    ⟨branchUnary, outputUnary, auditUnary, terminalUnary, obstructionUnary, branchRoute,
      outputRoute, auditRoute, terminalRoute, obstructionRoute, transportSame, provenancePkg,
      obstructionPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
