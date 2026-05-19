import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_regseqrat_real_seal_package [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      sealRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg →
      Cont modulus endpoint sealRead →
        Cont sealRead provenance realRead →
          PkgSig bundle realRead pkg →
            UnaryHistory modulus ∧ UnaryHistory endpoint ∧ UnaryHistory sealRead ∧
              UnaryHistory realRead ∧ Cont iterates modulus endpoint ∧
                Cont modulus endpoint sealRead ∧ Cont sealRead provenance realRead ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet modulusEndpointSealRead sealReadProvenanceRealRead realReadPkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, _iteratesUnary,
    modulusUnary, endpointUnary, _transportUnary, _routesUnary, provenanceUnary,
    _nameUnary, _banachContractionLipschitz, iteratesModulusEndpoint,
    _endpointTransportRoutes, _routesProvenanceName, namePkg⟩ := packet
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed modulusUnary endpointUnary modulusEndpointSealRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed sealReadUnary provenanceUnary sealReadProvenanceRealRead
  exact
    ⟨modulusUnary, endpointUnary, sealReadUnary, realReadUnary, iteratesModulusEndpoint,
      modulusEndpointSealRead, sealReadProvenanceRealRead, namePkg, realReadPkg⟩

end BEDC.Derived.PicardContractionUp
