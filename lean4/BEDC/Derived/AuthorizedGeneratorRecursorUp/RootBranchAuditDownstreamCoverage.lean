import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootBranchAuditDownstreamCoverage [AskSetup]
    [PackageSetup]
    {I E M B D O A H C P G N branchRead auditRead publicRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont B D branchRead ->
        Cont A C auditRead ->
          Cont branchRead auditRead publicRead ->
            Cont G N boundaryRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory branchRead ∧ UnaryHistory auditRead ∧
                  UnaryHistory publicRead ∧ UnaryHistory boundaryRead ∧
                    Cont B D branchRead ∧ Cont A C auditRead ∧
                      Cont branchRead auditRead publicRead ∧ Cont G N boundaryRead ∧
                        hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame
  intro carrier branchRoute auditRoute publicRoute boundaryRoute publicPkg
  obtain
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, branchUnary, descentUnary,
      _outputUnary, auditUnary, transportUnary, continuationUnary, provenanceUnary,
      boundaryUnary, localNameUnary, _signatureMotiveRoute, _motiveBranchRoute,
      _descentAuditRoute, transportSame, provenancePkg⟩ := carrier
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary descentUnary branchRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed auditUnary continuationUnary auditRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed branchReadUnary auditReadUnary publicRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed boundaryUnary localNameUnary boundaryRoute
  exact
    ⟨branchReadUnary, auditReadUnary, publicReadUnary, boundaryReadUnary,
      branchRoute, auditRoute, publicRoute, boundaryRoute, transportSame, provenancePkg,
      publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
