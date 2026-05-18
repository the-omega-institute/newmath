import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootReadinessExhaustion [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead publicRead outputRead auditRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont B D branchRead ->
        Cont branchRead C publicRead ->
          Cont O A outputRead ->
            Cont outputRead N auditRead ->
              Cont G N boundaryRead ->
                PkgSig bundle auditRead pkg ->
                  UnaryHistory I ∧ UnaryHistory E ∧ UnaryHistory M ∧ UnaryHistory B ∧
                    UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory C ∧
                      UnaryHistory G ∧ UnaryHistory N ∧ UnaryHistory publicRead ∧
                        UnaryHistory auditRead ∧ UnaryHistory boundaryRead ∧ Cont I E M ∧
                          Cont M B D ∧ Cont D O A ∧ Cont B D branchRead ∧
                            Cont branchRead C publicRead ∧ Cont O A outputRead ∧
                              Cont outputRead N auditRead ∧ Cont G N boundaryRead ∧
                                hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame
  intro carrier branchRoute publicRoute outputRoute auditRoute boundaryRoute auditPkg
  rcases carrier with
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, sameUnary, unaryC,
      provenanceUnary, unaryG, unaryN, contIEM, contMBD, contDOA, sameTransport,
      provenancePkg⟩
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryB unaryD branchRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed branchUnary unaryC publicRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed outputUnary unaryN auditRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryG unaryN boundaryRoute
  exact
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryC, unaryG, unaryN,
      publicUnary, auditUnary, boundaryUnary, contIEM, contMBD, contDOA, branchRoute,
      publicRoute, outputRoute, auditRoute, boundaryRoute, sameTransport, provenancePkg,
      auditPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
