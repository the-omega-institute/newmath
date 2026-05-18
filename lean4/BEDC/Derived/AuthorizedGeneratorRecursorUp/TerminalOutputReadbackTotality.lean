import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorTerminalOutputReadbackTotality [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead outputRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont B D branchRead ->
        Cont O A outputRead ->
          Cont outputRead N terminalRead ->
            UnaryHistory branchRead ∧ UnaryHistory outputRead ∧ UnaryHistory terminalRead ∧
              Cont B D branchRead ∧ Cont O A outputRead ∧
                Cont outputRead N terminalRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier branchRoute outputRoute terminalRoute
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, unaryB, unaryD, unaryO, unaryA, _unaryH, _unaryC,
      unaryP, _unaryG, unaryN, _iem, _mbd, _doa, _sameTransport, pkgSig⟩
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryB unaryD branchRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed outputUnary unaryN terminalRoute
  exact
    ⟨branchUnary, outputUnary, terminalUnary, branchRoute, outputRoute, terminalRoute, pkgSig⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
