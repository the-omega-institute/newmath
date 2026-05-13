import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_finite_rate_seal_triangle [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      rateSource sealRead publicSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg →
      Cont iterates modulus rateSource →
        Cont rateSource endpoint routes →
          Cont endpoint transport sealRead →
            Cont modulus endpoint publicSeal →
              PkgSig bundle rateSource pkg →
                PkgSig bundle sealRead pkg →
                  PkgSig bundle publicSeal pkg →
                    UnaryHistory rateSource ∧ UnaryHistory sealRead ∧
                      UnaryHistory publicSeal ∧ Cont iterates modulus rateSource ∧
                        Cont rateSource endpoint routes ∧ Cont endpoint transport sealRead ∧
                          Cont modulus endpoint publicSeal ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle rateSource pkg ∧ PkgSig bundle sealRead pkg ∧
                              PkgSig bundle publicSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet iteratesModulusRateSource rateSourceEndpointRoutes endpointTransportSealRead
    modulusEndpointPublicSeal rateSourcePkg sealReadPkg publicSealPkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have rateSourceUnary : UnaryHistory rateSource :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRateSource
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportSealRead
  have publicSealUnary : UnaryHistory publicSeal :=
    unary_cont_closed modulusUnary endpointUnary modulusEndpointPublicSeal
  exact
    ⟨rateSourceUnary, sealReadUnary, publicSealUnary, iteratesModulusRateSource,
      rateSourceEndpointRoutes, endpointTransportSealRead, modulusEndpointPublicSeal,
      namePkg, rateSourcePkg, sealReadPkg, publicSealPkg⟩

end BEDC.Derived.PicardContractionUp
