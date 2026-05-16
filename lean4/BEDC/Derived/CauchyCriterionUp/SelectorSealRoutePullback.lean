import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_selector_seal_route_pullback [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      diagonalSource selectorSeal pullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg →
      UnaryHistory diagonalSource →
        Cont endpoint diagonalSource selectorSeal →
          Cont selectorSeal provenance pullback →
            PkgSig bundle pullback pkg →
              UnaryHistory endpoint ∧ UnaryHistory diagonalSource ∧
                UnaryHistory selectorSeal ∧ UnaryHistory pullback ∧
                  Cont endpoint diagonalSource selectorSeal ∧
                    Cont selectorSeal provenance pullback ∧ PkgSig bundle endpoint pkg ∧
                      PkgSig bundle pullback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier diagonalSourceUnary endpointDiagonalSelector selectorProvenancePullback
    pullbackPkg
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _regseqUnary,
    _realSealUnary, _transportUnary, _routeUnary, provenanceUnary, _localCertUnary,
    endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    endpointPkg⟩ := carrier
  have selectorSealUnary : UnaryHistory selectorSeal :=
    unary_cont_closed endpointUnary diagonalSourceUnary endpointDiagonalSelector
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed selectorSealUnary provenanceUnary selectorProvenancePullback
  exact
    ⟨endpointUnary, diagonalSourceUnary, selectorSealUnary, pullbackUnary,
      endpointDiagonalSelector, selectorProvenancePullback, endpointPkg, pullbackPkg⟩

end BEDC.Derived.CauchyCriterionUp
