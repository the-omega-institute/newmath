import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_fixed_point_ledger_boundary [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      scheduled ledgerBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates endpoint scheduled ->
        Cont scheduled modulus ledgerBoundary ->
          PkgSig bundle scheduled pkg ->
            PkgSig bundle ledgerBoundary pkg ->
              UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
                UnaryHistory scheduled ∧ UnaryHistory ledgerBoundary ∧
                  Cont iterates modulus endpoint ∧ Cont iterates endpoint scheduled ∧
                    Cont scheduled modulus ledgerBoundary ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle scheduled pkg ∧ PkgSig bundle ledgerBoundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet iteratesEndpointScheduled scheduledModulusLedger scheduledPkg ledgerPkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have scheduledUnary : UnaryHistory scheduled :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointScheduled
  have ledgerUnary : UnaryHistory ledgerBoundary :=
    unary_cont_closed scheduledUnary modulusUnary scheduledModulusLedger
  exact
    ⟨iteratesUnary, modulusUnary, endpointUnary, scheduledUnary, ledgerUnary,
      iteratesModulusEndpoint, iteratesEndpointScheduled, scheduledModulusLedger, namePkg,
      scheduledPkg, ledgerPkg⟩

end BEDC.Derived.PicardContractionUp
