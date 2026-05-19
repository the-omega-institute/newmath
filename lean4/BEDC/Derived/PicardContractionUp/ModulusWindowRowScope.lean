import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_modulus_window_row_scope [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont endpoint transport sealRead ->
        PkgSig bundle sealRead pkg ->
          UnaryHistory modulus ∧ UnaryHistory endpoint ∧ UnaryHistory transport ∧
            UnaryHistory sealRead ∧ Cont iterates modulus endpoint ∧
              Cont endpoint transport sealRead ∧ PkgSig bundle name pkg ∧
                PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet endpointTransportSealRead sealReadPkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, _iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportSealRead
  exact
    ⟨modulusUnary, endpointUnary, transportUnary, sealReadUnary, iteratesModulusEndpoint,
      endpointTransportSealRead, namePkg, sealReadPkg⟩

end BEDC.Derived.PicardContractionUp
