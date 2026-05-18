import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootNameCertConsumerReadiness [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead auditRead boundaryRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead N auditRead ->
          Cont G N boundaryRead ->
            Cont auditRead boundaryRead consumerRead ->
              PkgSig bundle consumerRead pkg ->
                UnaryHistory I ∧ UnaryHistory E ∧ UnaryHistory M ∧ UnaryHistory B ∧
                  UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory H ∧
                    UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory G ∧ UnaryHistory N ∧
                      UnaryHistory outputRead ∧ UnaryHistory auditRead ∧
                        UnaryHistory boundaryRead ∧ UnaryHistory consumerRead ∧
                          Cont I E M ∧ Cont M B D ∧ Cont D O A ∧
                            Cont O A outputRead ∧ Cont outputRead N auditRead ∧
                              Cont G N boundaryRead ∧
                                Cont auditRead boundaryRead consumerRead ∧
                                  hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                                    PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame
  intro carrier outputRoute auditRoute boundaryRoute consumerRoute consumerPkg
  rcases carrier with
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC,
      unaryP, unaryG, unaryN, contIEM, contMBD, contDOA, sameTransport,
      provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed outputUnary unaryN auditRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryG unaryN boundaryRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed auditUnary boundaryUnary consumerRoute
  exact
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC,
      unaryP, unaryG, unaryN, outputUnary, auditUnary, boundaryUnary, consumerUnary,
      contIEM, contMBD, contDOA, outputRoute, auditRoute, boundaryRoute, consumerRoute,
      sameTransport, provenancePkg, consumerPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
