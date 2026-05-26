import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_public_interface_export [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name finiteApproxRead observationBudgetRead
      limitSealRead finalRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes finiteApproxRead ->
        Cont finiteApproxRead ledger observationBudgetRead ->
          Cont observationBudgetRead routes limitSealRead ->
            Cont limitSealRead ledger finalRead ->
              Cont finalRead routes publicRead ->
                PkgSig bundle publicRead pkg ->
                  UnaryHistory product ∧ UnaryHistory classifier ∧
                    UnaryHistory finiteApproxRead ∧ UnaryHistory observationBudgetRead ∧
                      UnaryHistory limitSealRead ∧ UnaryHistory finalRead ∧
                        UnaryHistory publicRead ∧ Cont observationA observationB product ∧
                          Cont product ledger classifier ∧
                            Cont classifier routes finiteApproxRead ∧
                              Cont finiteApproxRead ledger observationBudgetRead ∧
                                Cont observationBudgetRead routes limitSealRead ∧
                                  Cont limitSealRead ledger finalRead ∧
                                    Cont finalRead routes publicRead ∧
                                      PkgSig bundle name pkg ∧
                                        PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont UnaryHistory ProbeBundle Pkg
  intro packet classifierFinite finiteObservation observationLimit limitFinal finalPublic
    publicPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have finiteApproxUnary : UnaryHistory finiteApproxRead :=
    unary_cont_closed classifierUnary routesUnary classifierFinite
  have observationBudgetUnary : UnaryHistory observationBudgetRead :=
    unary_cont_closed finiteApproxUnary ledgerUnary finiteObservation
  have limitSealUnary : UnaryHistory limitSealRead :=
    unary_cont_closed observationBudgetUnary routesUnary observationLimit
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed limitSealUnary ledgerUnary limitFinal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed finalReadUnary routesUnary finalPublic
  exact
    ⟨productUnary, classifierUnary, finiteApproxUnary, observationBudgetUnary,
      limitSealUnary, finalReadUnary, publicReadUnary, productRoute, classifierRoute,
      classifierFinite, finiteObservation, observationLimit, limitFinal, finalPublic,
      namePkg, publicPkg⟩

end BEDC.Derived.CauchyProductUp
