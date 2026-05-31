import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_product_observation_seal_obligations [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name observationSeal finalSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes observationSeal ->
        Cont observationSeal ledger finalSeal ->
          PkgSig bundle finalSeal pkg ->
            UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory observationSeal ∧
              UnaryHistory finalSeal ∧ Cont observationA observationB product ∧
                Cont product ledger classifier ∧ Cont classifier routes observationSeal ∧
                  Cont observationSeal ledger finalSeal ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle finalSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierObservation observationFinal finalPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have observationSealUnary : UnaryHistory observationSeal :=
    unary_cont_closed classifierUnary routesUnary classifierObservation
  have finalSealUnary : UnaryHistory finalSeal :=
    unary_cont_closed observationSealUnary ledgerUnary observationFinal
  exact
    ⟨productUnary, classifierUnary, observationSealUnary, finalSealUnary, productRoute,
      classifierRoute, classifierObservation, observationFinal, namePkg, finalPkg⟩

end BEDC.Derived.CauchyProductUp
