import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionRootUnblockPackage [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      odeConsumer sealConsumer rootConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg →
      Cont iterates endpoint odeConsumer →
        Cont iterates modulus sealConsumer →
          Cont sealConsumer endpoint rootConsumer →
            PkgSig bundle odeConsumer pkg →
              PkgSig bundle rootConsumer pkg →
                UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
                  UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
                    UnaryHistory odeConsumer ∧ UnaryHistory sealConsumer ∧
                      UnaryHistory rootConsumer ∧ Cont banach contraction lipschitz ∧
                        Cont iterates modulus endpoint ∧ Cont iterates endpoint odeConsumer ∧
                          Cont iterates modulus sealConsumer ∧
                            Cont sealConsumer endpoint rootConsumer ∧ PkgSig bundle name pkg ∧
                              PkgSig bundle odeConsumer pkg ∧
                                PkgSig bundle rootConsumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro packet iteratesEndpointOdeConsumer iteratesModulusSealConsumer
    sealConsumerEndpointRootConsumer odeConsumerPkg rootConsumerPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have odeConsumerUnary : UnaryHistory odeConsumer :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointOdeConsumer
  have sealConsumerUnary : UnaryHistory sealConsumer :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusSealConsumer
  have rootConsumerUnary : UnaryHistory rootConsumer :=
    unary_cont_closed sealConsumerUnary endpointUnary sealConsumerEndpointRootConsumer
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
      endpointUnary, odeConsumerUnary, sealConsumerUnary, rootConsumerUnary,
      banachContractionLipschitz, iteratesModulusEndpoint, iteratesEndpointOdeConsumer,
      iteratesModulusSealConsumer, sealConsumerEndpointRootConsumer, namePkg, odeConsumerPkg,
      rootConsumerPkg⟩

end BEDC.Derived.PicardContractionUp
