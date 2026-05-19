import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_metric_complete_lipschitz_consumer_route [AskSetup]
    [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      odeConsumer newtonConsumer realConsumer routeSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont banach lipschitz odeConsumer ->
        Cont banach endpoint newtonConsumer ->
          Cont modulus endpoint realConsumer ->
            Cont realConsumer transport routeSeal ->
              PkgSig bundle routeSeal pkg ->
                UnaryHistory banach ∧ UnaryHistory lipschitz ∧ UnaryHistory modulus ∧
                  UnaryHistory endpoint ∧ UnaryHistory odeConsumer ∧
                    UnaryHistory newtonConsumer ∧ UnaryHistory realConsumer ∧
                      UnaryHistory routeSeal ∧ Cont banach lipschitz odeConsumer ∧
                        Cont banach endpoint newtonConsumer ∧
                          Cont modulus endpoint realConsumer ∧
                            Cont realConsumer transport routeSeal ∧
                              PkgSig bundle name pkg ∧ PkgSig bundle routeSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet banachLipschitzOde banachEndpointNewton modulusEndpointReal
    realTransportSeal routeSealPkg
  obtain ⟨banachUnary, _contractionUnary, lipschitzUnary, _iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have odeUnary : UnaryHistory odeConsumer :=
    unary_cont_closed banachUnary lipschitzUnary banachLipschitzOde
  have newtonUnary : UnaryHistory newtonConsumer :=
    unary_cont_closed banachUnary endpointUnary banachEndpointNewton
  have realUnary : UnaryHistory realConsumer :=
    unary_cont_closed modulusUnary endpointUnary modulusEndpointReal
  have sealUnary : UnaryHistory routeSeal :=
    unary_cont_closed realUnary transportUnary realTransportSeal
  exact
    ⟨banachUnary, lipschitzUnary, modulusUnary, endpointUnary, odeUnary, newtonUnary,
      realUnary, sealUnary, banachLipschitzOde, banachEndpointNewton, modulusEndpointReal,
      realTransportSeal, namePkg, routeSealPkg⟩

end BEDC.Derived.PicardContractionUp
