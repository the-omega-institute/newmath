import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_public_seal_export [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      sealExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg →
      Cont modulus endpoint sealExport →
        PkgSig bundle sealExport pkg →
          UnaryHistory modulus ∧ UnaryHistory endpoint ∧ UnaryHistory sealExport ∧
            Cont iterates modulus endpoint ∧ Cont modulus endpoint sealExport ∧
              PkgSig bundle name pkg ∧ PkgSig bundle sealExport pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet modulusEndpointSealExport sealExportPkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, _iteratesUnary,
    modulusUnary, endpointUnary, _transportUnary, _routesUnary, _provenanceUnary,
    _nameUnary, _banachContractionLipschitz, iteratesModulusEndpoint,
    _endpointTransportRoutes, _routesProvenanceName, namePkg⟩ := packet
  have sealExportUnary : UnaryHistory sealExport :=
    unary_cont_closed modulusUnary endpointUnary modulusEndpointSealExport
  exact
    ⟨modulusUnary, endpointUnary, sealExportUnary, iteratesModulusEndpoint,
      modulusEndpointSealExport, namePkg, sealExportPkg⟩

end BEDC.Derived.PicardContractionUp
