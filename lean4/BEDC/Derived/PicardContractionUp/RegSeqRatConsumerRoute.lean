import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_regseqrat_consumer_route [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      regseqRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates modulus regseqRead ->
        Cont regseqRead routes consumerRead ->
          PkgSig bundle regseqRead pkg ->
            PkgSig bundle consumerRead pkg ->
              UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory regseqRead ∧
                UnaryHistory consumerRead ∧ Cont iterates modulus endpoint ∧
                  Cont iterates modulus regseqRead ∧ Cont regseqRead routes consumerRead ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle regseqRead pkg ∧
                      PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet iteratesModulusRegseqRead regseqReadRoutesConsumerRead regseqReadPkg
    consumerReadPkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, iteratesUnary, modulusUnary,
    _endpointUnary, _transportUnary, routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRegseqRead
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed regseqReadUnary routesUnary regseqReadRoutesConsumerRead
  exact
    ⟨iteratesUnary, modulusUnary, regseqReadUnary, consumerReadUnary,
      iteratesModulusEndpoint, iteratesModulusRegseqRead, regseqReadRoutesConsumerRead,
      namePkg, regseqReadPkg, consumerReadPkg⟩

end BEDC.Derived.PicardContractionUp
