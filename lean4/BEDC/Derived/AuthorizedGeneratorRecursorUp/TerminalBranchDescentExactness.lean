import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorTerminalBranchDescentExactness [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead outputRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont M B branchRead →
        Cont branchRead D outputRead →
          Cont outputRead O terminalRead →
            PkgSig bundle terminalRead pkg →
              UnaryHistory B ∧ UnaryHistory D ∧ UnaryHistory branchRead ∧
                UnaryHistory outputRead ∧ UnaryHistory terminalRead ∧ Cont M B branchRead ∧
                  Cont branchRead D outputRead ∧ Cont outputRead O terminalRead ∧
                    hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier branchRoute outputRoute terminalRoute terminalPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, unaryM, unaryB, unaryD, unaryO, _unaryA, _unaryH, _unaryC,
      _unaryP, _unaryG, _unaryN, _contIEM, _contMBD, _contDOA, transportSame,
      provenancePkg⟩
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryM unaryB branchRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed branchReadUnary unaryD outputRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed outputReadUnary unaryO terminalRoute
  exact
    ⟨unaryB, unaryD, branchReadUnary, outputReadUnary, terminalReadUnary, branchRoute,
      outputRoute, terminalRoute, transportSame, provenancePkg, terminalPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
