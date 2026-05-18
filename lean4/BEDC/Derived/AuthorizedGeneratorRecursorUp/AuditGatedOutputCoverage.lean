import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorAuditGatedOutputCoverage [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead auditPublic localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead C auditPublic ->
          Cont auditPublic N localRead ->
            PkgSig bundle localRead pkg ->
              UnaryHistory I ∧ UnaryHistory E ∧ UnaryHistory M ∧ UnaryHistory B ∧
                UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory A ∧
                  UnaryHistory outputRead ∧ UnaryHistory auditPublic ∧
                    UnaryHistory localRead ∧ hsame H (append A C) ∧ Cont I E M ∧
                      Cont M B D ∧ Cont D O A ∧ Cont O A outputRead ∧
                        Cont outputRead C auditPublic ∧ Cont auditPublic N localRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle localRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame PkgSig
  intro carrier outputRoute auditRoute localRoute localPkg
  rcases carrier with
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, _unaryH, unaryC,
      _provenanceUnary, _unaryG, unaryN, contIEM, contMBD, contDOA, sameTransport,
      provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have auditPublicUnary : UnaryHistory auditPublic :=
    unary_cont_closed outputUnary unaryC auditRoute
  have localReadUnary : UnaryHistory localRead :=
    unary_cont_closed auditPublicUnary unaryN localRoute
  exact
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, outputUnary,
      auditPublicUnary, localReadUnary, sameTransport, contIEM, contMBD, contDOA,
      outputRoute, auditRoute, localRoute, provenancePkg, localPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
