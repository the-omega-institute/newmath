import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorObligationTriad [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead outputRead auditRead boundaryRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont I E branchRead ->
        Cont M D descentRead ->
          Cont O A outputRead ->
            Cont outputRead N auditRead ->
              Cont G N boundaryRead ->
                Cont auditRead boundaryRead publicRead ->
                  PkgSig bundle publicRead pkg ->
                    UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
                      UnaryHistory outputRead ∧ UnaryHistory auditRead ∧
                        UnaryHistory boundaryRead ∧ UnaryHistory publicRead ∧
                          Cont I E M ∧ Cont M B D ∧ Cont D O A ∧
                            Cont I E branchRead ∧ Cont M D descentRead ∧
                              Cont O A outputRead ∧ Cont outputRead N auditRead ∧
                                Cont G N boundaryRead ∧ Cont auditRead boundaryRead publicRead ∧
                                  hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                                    PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame
  intro carrier branchRoute descentRoute outputRoute auditRoute boundaryRoute publicRoute publicPkg
  obtain ⟨unaryI, unaryE, unaryM, _unaryB, unaryD, unaryO, unaryA, _unaryH,
    _unaryC, _unaryP, unaryG, unaryN, carrierBranch, carrierDescent, carrierOutput,
    transportSame, provenancePkg⟩ := carrier
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryI unaryE branchRoute
  have descentUnary : UnaryHistory descentRead :=
    unary_cont_closed unaryM unaryD descentRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed outputUnary unaryN auditRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryG unaryN boundaryRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed auditUnary boundaryUnary publicRoute
  exact
    ⟨branchUnary, descentUnary, outputUnary, auditUnary, boundaryUnary, publicUnary,
      carrierBranch, carrierDescent, carrierOutput, branchRoute, descentRoute, outputRoute,
      auditRoute, boundaryRoute, publicRoute, transportSame, provenancePkg, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
