import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_real_seal_noncompletion [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont endpoint transport sealRead ->
        PkgSig bundle sealRead pkg ->
          UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
            UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
              UnaryHistory sealRead ∧ Cont banach contraction lipschitz ∧
                Cont iterates modulus endpoint ∧ Cont endpoint transport sealRead ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet endpointTransportSealRead sealReadPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportSealRead
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
      endpointUnary, sealReadUnary, banachContractionLipschitz, iteratesModulusEndpoint,
      endpointTransportSealRead, namePkg, sealReadPkg⟩

end BEDC.Derived.PicardContractionUp
