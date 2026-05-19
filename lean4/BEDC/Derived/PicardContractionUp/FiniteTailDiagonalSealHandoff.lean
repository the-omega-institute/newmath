import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_finite_tail_diagonal_seal_handoff [AskSetup]
    [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      rateSource sealRead finiteTailSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates modulus rateSource ->
        Cont rateSource endpoint routes ->
          Cont endpoint transport sealRead ->
            Cont sealRead routes finiteTailSeal ->
              PkgSig bundle rateSource pkg ->
                PkgSig bundle sealRead pkg ->
                  PkgSig bundle finiteTailSeal pkg ->
                    UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
                      UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
                        UnaryHistory rateSource ∧ UnaryHistory sealRead ∧
                          UnaryHistory finiteTailSeal ∧ Cont banach contraction lipschitz ∧
                            Cont iterates modulus rateSource ∧
                              Cont rateSource endpoint routes ∧
                                Cont endpoint transport sealRead ∧
                                  Cont sealRead routes finiteTailSeal ∧
                                    PkgSig bundle name pkg ∧
                                      PkgSig bundle rateSource pkg ∧
                                        PkgSig bundle sealRead pkg ∧
                                          PkgSig bundle finiteTailSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet iteratesModulusRateSource rateSourceEndpointRoutes endpointTransportSealRead
    sealRoutesFiniteTail rateSourcePkg sealReadPkg finiteTailPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have rateSourceUnary : UnaryHistory rateSource :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRateSource
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportSealRead
  have finiteTailUnary : UnaryHistory finiteTailSeal :=
    unary_cont_closed sealReadUnary routesUnary sealRoutesFiniteTail
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
      endpointUnary, rateSourceUnary, sealReadUnary, finiteTailUnary,
      banachContractionLipschitz, iteratesModulusRateSource, rateSourceEndpointRoutes,
      endpointTransportSealRead, sealRoutesFiniteTail, namePkg, rateSourcePkg, sealReadPkg,
      finiteTailPkg⟩

end BEDC.Derived.PicardContractionUp
