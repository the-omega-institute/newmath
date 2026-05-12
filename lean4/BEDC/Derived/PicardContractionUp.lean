import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PicardContractionPacket [AskSetup] [PackageSetup]
    (banach contraction lipschitz iterates modulus endpoint transport routes provenance name :
      BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
    UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
      UnaryHistory transport ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont banach contraction lipschitz ∧
          Cont iterates modulus endpoint ∧ Cont endpoint transport routes ∧
            Cont routes provenance name ∧ PkgSig bundle name pkg

theorem PicardContractionPacket_finite_iterate_closure [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      nextIterates concatenatedIterates concatenatedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      hsame endpoint nextIterates ->
        Cont iterates nextIterates concatenatedIterates ->
          Cont concatenatedIterates modulus concatenatedEndpoint ->
            Cont concatenatedEndpoint transport routes ->
              PicardContractionPacket banach contraction lipschitz concatenatedIterates modulus
                  concatenatedEndpoint transport routes provenance name bundle pkg ∧
                hsame endpoint nextIterates ∧ UnaryHistory concatenatedIterates ∧
                  UnaryHistory concatenatedEndpoint := by
  intro packet sameEndpointNextIterates iteratesNextIteratesConcatenated
    concatenatedIteratesModulusEndpoint concatenatedEndpointTransportRoutes
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, routesUnary, provenanceUnary, nameUnary,
    banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    routesProvenanceName, namePkg⟩ := packet
  have nextIteratesUnary : UnaryHistory nextIterates :=
    unary_transport endpointUnary sameEndpointNextIterates
  have concatenatedIteratesUnary : UnaryHistory concatenatedIterates :=
    unary_cont_closed iteratesUnary nextIteratesUnary iteratesNextIteratesConcatenated
  have concatenatedEndpointUnary : UnaryHistory concatenatedEndpoint :=
    unary_cont_closed concatenatedIteratesUnary modulusUnary concatenatedIteratesModulusEndpoint
  have closedPacket :
      PicardContractionPacket banach contraction lipschitz concatenatedIterates modulus
          concatenatedEndpoint transport routes provenance name bundle pkg := by
    exact
      ⟨banachUnary, contractionUnary, lipschitzUnary, concatenatedIteratesUnary, modulusUnary,
        concatenatedEndpointUnary, transportUnary, routesUnary, provenanceUnary, nameUnary,
        banachContractionLipschitz, concatenatedIteratesModulusEndpoint,
        concatenatedEndpointTransportRoutes, routesProvenanceName, namePkg⟩
  exact
    ⟨closedPacket, sameEndpointNextIterates, concatenatedIteratesUnary,
      concatenatedEndpointUnary⟩

theorem PicardContractionPacket_banach_ode_boundary [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates endpoint consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
            UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
              UnaryHistory consumer ∧ Cont banach contraction lipschitz ∧
                Cont iterates modulus endpoint ∧ Cont iterates endpoint consumer ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle consumer pkg := by
  intro packet iteratesEndpointConsumer consumerPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointConsumer
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
      endpointUnary, consumerUnary, banachContractionLipschitz, iteratesModulusEndpoint,
      iteratesEndpointConsumer, namePkg, consumerPkg⟩

end BEDC.Derived.PicardContractionUp
