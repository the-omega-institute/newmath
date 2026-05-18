import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionRealRegSeqRatConsumerHandoff [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      regRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates modulus regRead ->
        Cont regRead endpoint realRead ->
          PkgSig bundle realRead pkg ->
            UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
              UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
                UnaryHistory regRead ∧ UnaryHistory realRead ∧ Cont banach contraction lipschitz ∧
                  Cont iterates modulus regRead ∧ Cont regRead endpoint realRead ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet iteratesModulusRegRead regReadEndpointRealRead realReadPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have regReadUnary : UnaryHistory regRead :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRegRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regReadUnary endpointUnary regReadEndpointRealRead
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
      endpointUnary, regReadUnary, realReadUnary, banachContractionLipschitz,
      iteratesModulusRegRead, regReadEndpointRealRead, namePkg, realReadPkg⟩

end BEDC.Derived.PicardContractionUp
