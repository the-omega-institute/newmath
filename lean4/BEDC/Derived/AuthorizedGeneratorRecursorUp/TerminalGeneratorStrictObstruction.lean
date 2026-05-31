import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorTerminalGeneratorStrictObstruction [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N terminalRead outputRead gate : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont I E terminalRead ->
        Cont terminalRead O outputRead ->
          Cont outputRead G gate ->
            PkgSig bundle gate pkg ->
              UnaryHistory I ∧ UnaryHistory E ∧ UnaryHistory O ∧ UnaryHistory G ∧
                UnaryHistory terminalRead ∧ UnaryHistory outputRead ∧ UnaryHistory gate ∧
                  Cont I E terminalRead ∧ Cont terminalRead O outputRead ∧
                    Cont outputRead G gate ∧ hsame H (append A C) ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle gate pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier terminalRoute outputRoute gateRoute gatePkg
  rcases carrier with
    ⟨unaryI, unaryE, _unaryM, _unaryB, _unaryD, unaryO, _unaryA, _unaryH,
      _unaryC, provenanceUnary, unaryG, _unaryN, _iem, _mbd, _doa, transport,
      provenancePkg⟩
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed unaryI unaryE terminalRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed terminalUnary unaryO outputRoute
  have gateUnary : UnaryHistory gate :=
    unary_cont_closed outputUnary unaryG gateRoute
  exact
    ⟨unaryI, unaryE, unaryO, unaryG, terminalUnary, outputUnary, gateUnary,
      terminalRoute, outputRoute, gateRoute, transport, provenancePkg, gatePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
