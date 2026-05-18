import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursor_root_consumer_readiness_surface [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead outputRead publicRead boundaryRead
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont I E branchRead →
        Cont branchRead D descentRead →
          Cont descentRead O outputRead →
            Cont outputRead C publicRead →
              Cont G N boundaryRead →
                Cont publicRead boundaryRead terminalRead →
                  PkgSig bundle terminalRead pkg →
                    UnaryHistory publicRead ∧ UnaryHistory boundaryRead ∧
                      UnaryHistory terminalRead ∧ Cont outputRead C publicRead ∧
                        Cont G N boundaryRead ∧ Cont publicRead boundaryRead terminalRead ∧
                          hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier branchRoute descentRoute outputRoute publicRoute boundaryRoute terminalRoute
    terminalPkg
  rcases carrier with
    ⟨unaryI, unaryE, _unaryM, _unaryB, unaryD, unaryO, _unaryA, _unaryH, unaryC,
      _unaryP, unaryG, unaryN, _contIEM, _contMBD, _contDOA, sameTransport,
      provenancePkg⟩
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryI unaryE branchRoute
  have descentUnary : UnaryHistory descentRead :=
    unary_cont_closed branchUnary unaryD descentRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary unaryO outputRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed outputUnary unaryC publicRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryG unaryN boundaryRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed publicUnary boundaryUnary terminalRoute
  exact
    ⟨publicUnary, boundaryUnary, terminalUnary, publicRoute, boundaryRoute, terminalRoute,
      sameTransport, provenancePkg, terminalPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
