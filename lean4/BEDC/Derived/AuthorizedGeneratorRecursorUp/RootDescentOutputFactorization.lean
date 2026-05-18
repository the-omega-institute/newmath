import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootDescentOutputFactorization [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N motiveRead descentRead outputRead auditRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont M B motiveRead ->
        Cont motiveRead D descentRead ->
          Cont descentRead O outputRead ->
            Cont outputRead A auditRead ->
              Cont auditRead N terminal ->
                PkgSig bundle terminal pkg ->
                  UnaryHistory M ∧ UnaryHistory D ∧ UnaryHistory O ∧
                    UnaryHistory motiveRead ∧ UnaryHistory descentRead ∧
                      UnaryHistory outputRead ∧ UnaryHistory auditRead ∧
                        UnaryHistory terminal ∧ Cont I E M ∧ Cont M B motiveRead ∧
                          Cont motiveRead D descentRead ∧ Cont descentRead O outputRead ∧
                            Cont outputRead A auditRead ∧ Cont auditRead N terminal ∧
                              hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier motiveRoute descentRoute outputRoute auditRoute terminalRoute terminalPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, _unaryH, _unaryC,
      _unaryP, _unaryG, unaryN, carrierIEM, _carrierMBD, _carrierDOA, sameTransport,
      provenancePkg⟩
  have motiveUnary : UnaryHistory motiveRead :=
    unary_cont_closed unaryM unaryB motiveRoute
  have descentUnary : UnaryHistory descentRead :=
    unary_cont_closed motiveUnary unaryD descentRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary unaryO outputRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed outputUnary unaryA auditRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed auditUnary unaryN terminalRoute
  exact
    ⟨unaryM, unaryD, unaryO, motiveUnary, descentUnary, outputUnary, auditUnary,
      terminalUnary, carrierIEM, motiveRoute, descentRoute, outputRoute, auditRoute,
      terminalRoute, sameTransport, provenancePkg, terminalPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
