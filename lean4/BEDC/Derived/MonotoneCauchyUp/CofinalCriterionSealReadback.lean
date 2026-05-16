import BEDC.Derived.CauchyCriterionUp
import BEDC.Derived.MonotoneCauchyUp

namespace BEDC.Derived.MonotoneCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MonotoneCauchyCarrier_cofinal_criterion_seal_readback [AskSetup] [PackageSetup]
    {regular schedule modulus ledger interval realSeal transportRow route provenance nameRow
      cofinalSchedule commonWindow tailWindow sealRead publicRead criterionTolerance
      criterionRegseq criterionTransport criterionRoute criterionEndpoint terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyCarrier regular schedule modulus ledger interval realSeal transportRow route
        provenance nameRow bundle pkg ->
      BEDC.Derived.CauchyCriterionUp.CauchyCriterionCarrier schedule modulus
          criterionTolerance ledger criterionRegseq realSeal criterionTransport criterionRoute
          provenance nameRow criterionEndpoint bundle pkg ->
        UnaryHistory cofinalSchedule ->
          Cont schedule modulus commonWindow ->
            Cont commonWindow cofinalSchedule tailWindow ->
              Cont interval realSeal sealRead ->
                Cont tailWindow sealRead publicRead ->
                  Cont publicRead criterionEndpoint terminalRead ->
                    PkgSig bundle terminalRead pkg ->
                      UnaryHistory commonWindow ∧ UnaryHistory tailWindow ∧
                        UnaryHistory sealRead ∧ UnaryHistory publicRead ∧
                          UnaryHistory terminalRead ∧ Cont schedule modulus commonWindow ∧
                            Cont commonWindow cofinalSchedule tailWindow ∧
                              Cont schedule modulus criterionTolerance ∧
                                Cont criterionTolerance ledger criterionRegseq ∧
                                  Cont interval realSeal sealRead ∧
                                    Cont tailWindow sealRead publicRead ∧
                                      Cont publicRead criterionEndpoint terminalRead ∧
                                        Cont transportRow route provenance ∧
                                          PkgSig bundle nameRow pkg ∧
                                            PkgSig bundle criterionEndpoint pkg ∧
                                              PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro monotone criterion cofinalUnary scheduleModulusCommon commonCofinalTail
    intervalRealSealRead tailSealPublic publicCriterionTerminal terminalPkg
  obtain ⟨_regularUnary, scheduleUnary, modulusUnary, _ledgerUnary, intervalUnary,
    realSealUnary, _transportRowUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    _regularScheduleModulus, _modulusLedgerInterval, _intervalRealSealNameRow,
    transportRouteProvenance, nameRowPkg⟩ := monotone
  obtain ⟨_scheduleUnary, _modulusUnary, _criterionToleranceUnary, _ledgerUnary,
    _criterionRegseqUnary, _realSealUnary, _criterionTransportUnary, _criterionRouteUnary,
    _provenanceUnary, _localCertUnary, criterionEndpointUnary, scheduleModulusTolerance,
    toleranceLedgerRegseq, _regseqRealSealTransport, _transportLocalCertRoute,
    _routeProvenanceEndpoint, criterionEndpointPkg⟩ := criterion
  have commonWindowUnary : UnaryHistory commonWindow :=
    unary_cont_closed scheduleUnary modulusUnary scheduleModulusCommon
  have tailWindowUnary : UnaryHistory tailWindow :=
    unary_cont_closed commonWindowUnary cofinalUnary commonCofinalTail
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed intervalUnary realSealUnary intervalRealSealRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed tailWindowUnary sealReadUnary tailSealPublic
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed publicReadUnary criterionEndpointUnary publicCriterionTerminal
  exact
    ⟨commonWindowUnary, tailWindowUnary, sealReadUnary, publicReadUnary, terminalReadUnary,
      scheduleModulusCommon, commonCofinalTail, scheduleModulusTolerance,
      toleranceLedgerRegseq, intervalRealSealRead, tailSealPublic, publicCriterionTerminal,
      transportRouteProvenance, nameRowPkg, criterionEndpointPkg, terminalPkg⟩

end BEDC.Derived.MonotoneCauchyUp
