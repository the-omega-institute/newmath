import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RecursionAuthorizationLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RecursionAuthorizationLedgerCarrier [AskSetup] [PackageSetup]
    (signature recursor motive branches descent output transport routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  UnaryHistory signature ∧ UnaryHistory recursor ∧ UnaryHistory motive ∧
    UnaryHistory branches ∧ UnaryHistory descent ∧ UnaryHistory output ∧
      UnaryHistory transport ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont signature recursor motive ∧ Cont branches descent output ∧
          Cont transport routes provenance ∧ PkgSig bundle provenance pkg ∧
            SemanticNameCert
              (fun row : BHist => hsame row signature ∧ UnaryHistory row)
              (fun row : BHist => hsame row signature)
              (fun row : BHist => hsame row signature ∧ PkgSig bundle provenance pkg)
              hsame

theorem RecursionAuthorizationLedgerCarrier_signature_acceptance [AskSetup] [PackageSetup]
    {signature recursor motive branches descent output transport routes provenance name
      branchAudit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RecursionAuthorizationLedgerCarrier signature recursor motive branches descent output
        transport routes provenance name bundle pkg ->
      Cont recursor branches branchAudit ->
        PkgSig bundle branchAudit pkg ->
          UnaryHistory signature ∧ UnaryHistory recursor ∧ UnaryHistory branches ∧
            UnaryHistory branchAudit ∧ Cont signature recursor motive ∧
              Cont recursor branches branchAudit ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle branchAudit pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier branchRoute branchPkg
  obtain ⟨signatureUnary, recursorUnary, _motiveUnary, branchesUnary, _descentUnary,
    _outputUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    signatureRoute, _outputRoute, _provenanceRoute, provenancePkg, _semanticCert⟩ := carrier
  have branchAuditUnary : UnaryHistory branchAudit :=
    unary_cont_closed recursorUnary branchesUnary branchRoute
  exact
    ⟨signatureUnary,
      recursorUnary,
      branchesUnary,
      branchAuditUnary,
      signatureRoute,
      branchRoute,
      provenancePkg,
      branchPkg⟩

end BEDC.Derived.RecursionAuthorizationLedgerUp
