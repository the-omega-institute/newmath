import BEDC.Derived.CauchyCriterionUp
import BEDC.Derived.MonotoneCauchyUp

namespace BEDC.Derived.MonotoneCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MonotoneCauchyCarrier_cauchycriterion_seal_handoff [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow
      criterionTolerance criterionRegseq criterionTransport criterionRoute criterionEndpoint sealRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg →
      BEDC.Derived.CauchyCriterionUp.CauchyCriterionCarrier schedule modulus
          criterionTolerance ledger criterionRegseq realSeal criterionTransport criterionRoute
          provenance nameRow criterionEndpoint bundle pkg →
        Cont interval realSeal sealRead →
          Cont sealRead criterionEndpoint publicRead →
            PkgSig bundle sealRead pkg →
              PkgSig bundle publicRead pkg →
                UnaryHistory sealRead ∧ UnaryHistory publicRead ∧
                  Cont regular schedule modulus ∧ Cont schedule modulus criterionTolerance ∧
                    Cont criterionTolerance ledger criterionRegseq ∧
                      Cont interval realSeal sealRead ∧
                        Cont sealRead criterionEndpoint publicRead ∧
                          Cont transportRow route provenance ∧ PkgSig bundle nameRow pkg ∧
                            PkgSig bundle criterionEndpoint pkg ∧
                              PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro monotone criterion intervalRealSealRead sealEndpointPublic _sealPkg publicPkg
  obtain ⟨_regularUnary, _scheduleUnary, _modulusUnary, _ledgerUnary, intervalUnary,
    realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    regularScheduleModulus, _modulusLedgerInterval, _intervalRealSealNameRow,
    transportRouteProvenance, nameRowPkg⟩ := monotone
  obtain ⟨_scheduleUnary, _modulusUnary, _criterionToleranceUnary, _ledgerUnary,
    _criterionRegseqUnary, _realSealUnary, _criterionTransportUnary, _criterionRouteUnary,
    _provenanceUnary, _localCertUnary, criterionEndpointUnary, scheduleModulusTolerance,
    toleranceLedgerRegseq, _regseqRealSealTransport, _transportLocalCertRoute,
    _routeProvenanceEndpoint, criterionEndpointPkg⟩ := criterion
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed intervalUnary realSealUnary intervalRealSealRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary criterionEndpointUnary sealEndpointPublic
  exact
    ⟨sealReadUnary, publicReadUnary, regularScheduleModulus, scheduleModulusTolerance,
      toleranceLedgerRegseq, intervalRealSealRead, sealEndpointPublic,
      transportRouteProvenance, nameRowPkg, criterionEndpointPkg, publicPkg⟩

end BEDC.Derived.MonotoneCauchyUp
