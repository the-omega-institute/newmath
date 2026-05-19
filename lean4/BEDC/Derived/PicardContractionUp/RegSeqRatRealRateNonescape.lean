import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_regseqrat_real_rate_nonescape [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      regRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg →
      Cont iterates modulus regRead →
        Cont regRead endpoint realRead →
          PkgSig bundle realRead pkg →
            UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
              UnaryHistory regRead ∧ UnaryHistory realRead ∧
                Cont iterates modulus regRead ∧ Cont regRead endpoint realRead ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet iteratesModulusRegRead regReadEndpointRealRead realReadPkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have regReadUnary : UnaryHistory regRead :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRegRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regReadUnary endpointUnary regReadEndpointRealRead
  exact
    ⟨iteratesUnary, modulusUnary, endpointUnary, regReadUnary, realReadUnary,
      iteratesModulusRegRead, regReadEndpointRealRead, namePkg, realReadPkg⟩

end BEDC.Derived.PicardContractionUp
