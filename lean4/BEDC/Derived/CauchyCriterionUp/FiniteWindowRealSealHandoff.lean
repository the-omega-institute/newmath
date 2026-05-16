import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_finite_window_real_seal_handoff [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      limitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg →
      Cont modulus regseq transport →
        Cont transport window realSeal →
          Cont realSeal route limitRead →
            PkgSig bundle limitRead pkg →
              UnaryHistory modulus ∧ UnaryHistory regseq ∧ UnaryHistory transport ∧
                UnaryHistory window ∧ UnaryHistory realSeal ∧ UnaryHistory route ∧
                  UnaryHistory provenance ∧ UnaryHistory localCert ∧ UnaryHistory endpoint ∧
                    UnaryHistory limitRead ∧ Cont modulus regseq transport ∧
                      Cont transport window realSeal ∧ Cont realSeal route limitRead ∧
                        PkgSig bundle endpoint pkg ∧ PkgSig bundle limitRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier modulusRegseqTransport transportWindowRealSeal realSealRouteLimit limitPkg
  obtain ⟨windowUnary, modulusUnary, _toleranceUnary, _ledgerUnary, regseqUnary,
    _realSealUnary, _transportUnary, routeUnary, provenanceUnary, localCertUnary,
    endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    endpointPkg⟩ := carrier
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed modulusUnary regseqUnary modulusRegseqTransport
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed transportUnary windowUnary transportWindowRealSeal
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed realSealUnary routeUnary realSealRouteLimit
  exact
    ⟨modulusUnary, regseqUnary, transportUnary, windowUnary, realSealUnary, routeUnary,
      provenanceUnary, localCertUnary, endpointUnary, limitUnary, modulusRegseqTransport,
      transportWindowRealSeal, realSealRouteLimit, endpointPkg, limitPkg⟩

end BEDC.Derived.CauchyCriterionUp
