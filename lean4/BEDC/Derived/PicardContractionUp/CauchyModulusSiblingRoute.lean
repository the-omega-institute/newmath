import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_cauchy_modulus_sibling_route [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      sourceRead modulusRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont banach contraction sourceRead ->
        Cont iterates modulus modulusRead ->
          Cont modulusRead endpoint sealRead ->
            PkgSig bundle sourceRead pkg ->
              PkgSig bundle modulusRead pkg ->
                PkgSig bundle sealRead pkg ->
                  UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
                    UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
                      UnaryHistory sourceRead ∧ UnaryHistory modulusRead ∧
                        UnaryHistory sealRead ∧ Cont banach contraction lipschitz ∧
                          Cont banach contraction sourceRead ∧
                            Cont iterates modulus endpoint ∧
                              Cont iterates modulus modulusRead ∧
                                Cont modulusRead endpoint sealRead ∧ PkgSig bundle name pkg ∧
                                  PkgSig bundle sourceRead pkg ∧
                                    PkgSig bundle modulusRead pkg ∧
                                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet sourceCont modulusCont sealCont sourcePkg modulusPkg sealPkg
  rcases packet with
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
      endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
      banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
      _routesProvenanceName, namePkg⟩
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed banachUnary contractionUnary sourceCont
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed iteratesUnary modulusUnary modulusCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed modulusReadUnary endpointUnary sealCont
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
      endpointUnary, sourceUnary, modulusReadUnary, sealUnary, banachContractionLipschitz,
      sourceCont, iteratesModulusEndpoint, modulusCont, sealCont, namePkg, sourcePkg,
      modulusPkg, sealPkg⟩

end BEDC.Derived.PicardContractionUp
