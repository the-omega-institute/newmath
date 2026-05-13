import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_public_iterate_ledger [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      iterateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates modulus iterateRead ->
        PkgSig bundle iterateRead pkg ->
          UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory iterateRead ∧
            Cont iterates modulus endpoint ∧ Cont iterates modulus iterateRead ∧
              PkgSig bundle name pkg ∧ PkgSig bundle iterateRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet iteratesModulusRead iterateReadPkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, iteratesUnary, modulusUnary,
    _endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have iterateReadUnary : UnaryHistory iterateRead :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRead
  exact
    ⟨iteratesUnary, modulusUnary, iterateReadUnary, iteratesModulusEndpoint,
      iteratesModulusRead, namePkg, iterateReadPkg⟩

end BEDC.Derived.PicardContractionUp
