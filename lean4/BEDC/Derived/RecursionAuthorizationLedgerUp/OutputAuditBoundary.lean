import BEDC.Derived.RecursionAuthorizationLedgerUp.Carrier

namespace BEDC.Derived.RecursionAuthorizationLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RecursionAuthorizationLedgerCarrier_output_audit_boundary [AskSetup] [PackageSetup]
    {signature recursor motive branches descent output transport routes provenance name
      outputRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RecursionAuthorizationLedgerCarrier signature recursor motive branches descent output
        transport routes provenance name bundle pkg →
      Cont descent output outputRead →
        Cont outputRead routes auditRead →
          PkgSig bundle auditRead pkg →
            UnaryHistory descent ∧ UnaryHistory output ∧ UnaryHistory outputRead ∧
              UnaryHistory auditRead ∧ Cont branches descent output ∧
                Cont descent output outputRead ∧ Cont outputRead routes auditRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier descentOutputRead outputReadRoutesAudit auditReadPkg
  obtain ⟨_signatureUnary, _recursorUnary, _motiveUnary, _branchesUnary, descentUnary,
    outputUnary, _transportUnary, routesUnary, _provenanceUnary, _nameUnary,
    _signatureRecursorMotive, branchesDescentOutput, _outputTransportRoutes,
    _transportRoutesProvenance, provenancePkg, _namePkg, _semanticCert⟩ := carrier
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary outputUnary descentOutputRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary routesUnary outputReadRoutesAudit
  exact
    ⟨descentUnary,
      outputUnary,
      outputReadUnary,
      auditReadUnary,
      branchesDescentOutput,
      descentOutputRead,
      outputReadRoutesAudit,
      provenancePkg,
      auditReadPkg⟩

end BEDC.Derived.RecursionAuthorizationLedgerUp
