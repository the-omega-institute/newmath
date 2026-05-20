import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_contraction_row_exactness [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      step consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates contraction step ->
        Cont iterates endpoint consumer ->
          PkgSig bundle step pkg ->
            PkgSig bundle consumer pkg ->
              UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
                UnaryHistory iterates ∧ UnaryHistory step ∧ UnaryHistory consumer ∧
                  Cont banach contraction lipschitz ∧ Cont iterates contraction step ∧
                    Cont iterates endpoint consumer ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle step pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont UnaryHistory
  intro packet iteratesContractionStep iteratesEndpointConsumer stepPkg consumerPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, _modulusUnary,
    endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have stepUnary : UnaryHistory step :=
    unary_cont_closed iteratesUnary contractionUnary iteratesContractionStep
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointConsumer
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, stepUnary,
      consumerUnary, banachContractionLipschitz, iteratesContractionStep,
      iteratesEndpointConsumer, namePkg, stepPkg, consumerPkg⟩

end BEDC.Derived.PicardContractionUp
