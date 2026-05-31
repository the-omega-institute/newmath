import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_budget_product_unit_route [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name unitSource unitWindow unitObservation unitProduct
      budgetClassifier budgetSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      UnaryHistory unitSource ->
        Cont unitSource windowB unitWindow ->
          Cont unitWindow observationB unitObservation ->
            Cont unitObservation ledger unitProduct ->
              Cont unitProduct routes budgetClassifier ->
                Cont budgetClassifier ledger budgetSeal ->
                  PkgSig bundle budgetSeal pkg ->
                    UnaryHistory unitWindow ∧ UnaryHistory unitObservation ∧
                      UnaryHistory unitProduct ∧ UnaryHistory budgetClassifier ∧
                        UnaryHistory budgetSeal ∧ Cont unitSource windowB unitWindow ∧
                          Cont unitWindow observationB unitObservation ∧
                            Cont unitObservation ledger unitProduct ∧
                              Cont unitProduct routes budgetClassifier ∧
                                Cont budgetClassifier ledger budgetSeal ∧
                                  PkgSig bundle name pkg ∧
                                    PkgSig bundle budgetSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet unitSourceUnary unitWindowRoute unitObservationRoute unitProductRoute
    budgetClassifierRoute budgetSealRoute budgetSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, _observationAUnary, observationBUnary, _routesUnary, ledgerUnary,
    _windowTransport, _productRoute, _classifierRoute, namePkg⟩ := packet
  have unitWindowUnary : UnaryHistory unitWindow :=
    unary_cont_closed unitSourceUnary windowBUnary unitWindowRoute
  have unitObservationUnary : UnaryHistory unitObservation :=
    unary_cont_closed unitWindowUnary observationBUnary unitObservationRoute
  have unitProductUnary : UnaryHistory unitProduct :=
    unary_cont_closed unitObservationUnary ledgerUnary unitProductRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed unitProductUnary _routesUnary budgetClassifierRoute
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSealRoute
  exact
    ⟨unitWindowUnary, unitObservationUnary, unitProductUnary, budgetClassifierUnary,
      budgetSealUnary, unitWindowRoute, unitObservationRoute, unitProductRoute,
      budgetClassifierRoute, budgetSealRoute, namePkg, budgetSealPkg⟩

end BEDC.Derived.CauchyProductUp
