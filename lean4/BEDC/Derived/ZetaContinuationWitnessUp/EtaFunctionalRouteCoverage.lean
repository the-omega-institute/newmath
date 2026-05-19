import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_eta_functional_route_coverage [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name etaRead
      functionalRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      UnaryHistory eta →
        UnaryHistory functional →
          UnaryHistory gamma →
            Cont eta functional etaRead →
              Cont functional gamma functionalRead →
                Cont etaRead functionalRead routeRead →
                  PkgSig bundle routeRead pkg →
                    UnaryHistory etaRead ∧ UnaryHistory functionalRead ∧
                      UnaryHistory routeRead ∧ Cont eta functional etaRead ∧
                        Cont functional gamma functionalRead ∧
                          Cont etaRead functionalRead routeRead ∧
                            PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                              PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet etaUnary functionalUnary gammaUnary etaFunctionalRead functionalGammaRead
    etaFunctionalRoute routePkg
  obtain ⟨_basicEtaAnalytic, _analyticFunctionalTransports, _poleZeroLedgerGamma,
    _transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have etaReadUnary : UnaryHistory etaRead :=
    unary_cont_closed etaUnary functionalUnary etaFunctionalRead
  have functionalReadUnary : UnaryHistory functionalRead :=
    unary_cont_closed functionalUnary gammaUnary functionalGammaRead
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed etaReadUnary functionalReadUnary etaFunctionalRoute
  exact
    ⟨etaReadUnary, functionalReadUnary, routeReadUnary, etaFunctionalRead,
      functionalGammaRead, etaFunctionalRoute, namePkg, provenancePkg, routePkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
