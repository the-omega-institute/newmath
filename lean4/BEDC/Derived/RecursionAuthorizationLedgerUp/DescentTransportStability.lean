import BEDC.Derived.RecursionAuthorizationLedgerUp.Carrier

namespace BEDC.Derived.RecursionAuthorizationLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RecursionAuthorizationLedgerCarrier_descent_transport_stability
    [AskSetup] [PackageSetup]
    {signature recursor motive branches descent output transport routes provenance name
      descentRead transportedOutput : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RecursionAuthorizationLedgerCarrier signature recursor motive branches descent output
        transport routes provenance name bundle pkg ->
      Cont descent transport descentRead ->
        Cont descentRead output transportedOutput ->
          PkgSig bundle transportedOutput pkg ->
            UnaryHistory branches ∧ UnaryHistory descent ∧ UnaryHistory output ∧
              UnaryHistory transport ∧ UnaryHistory descentRead ∧
                UnaryHistory transportedOutput ∧ Cont branches descent output ∧
                  Cont descent transport descentRead ∧
                    Cont descentRead output transportedOutput ∧
                      PkgSig bundle provenance pkg ∧
                        PkgSig bundle transportedOutput pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier descentTransport descentReadOutput transportedPkg
  obtain ⟨_signatureUnary, _recursorUnary, _motiveUnary, branchesUnary, descentUnary,
    outputUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _signatureRecursorMotive, branchesDescentOutput, _outputTransportRoutes,
    _transportRoutesProvenance, provenancePkg, _namePkg, _semanticCert⟩ := carrier
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed descentUnary transportUnary descentTransport
  have transportedOutputUnary : UnaryHistory transportedOutput :=
    unary_cont_closed descentReadUnary outputUnary descentReadOutput
  exact
    ⟨branchesUnary,
      descentUnary,
      outputUnary,
      transportUnary,
      descentReadUnary,
      transportedOutputUnary,
      branchesDescentOutput,
      descentTransport,
      descentReadOutput,
      provenancePkg,
      transportedPkg⟩

end BEDC.Derived.RecursionAuthorizationLedgerUp
