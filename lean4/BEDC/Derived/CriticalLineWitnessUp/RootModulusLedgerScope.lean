import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessRootModulusLedgerScope
    {Z S M R Q H C P N modulusRead comparisonRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R modulusRead ->
        Cont modulusRead Q comparisonRead ->
          UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory modulusRead ∧
            UnaryHistory comparisonRead ∧ Cont M R modulusRead ∧
              Cont modulusRead Q comparisonRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro packet modulusRoute comparisonRoute
  obtain ⟨_unaryZ, _unaryS, unaryM, unaryR, _unaryP, _sameH, carrierRouteQ, _routeC,
    _routeN⟩ := packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR carrierRouteQ
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed modulusUnary unaryQ comparisonRoute
  exact
    ⟨unaryM, unaryR, unaryQ, modulusUnary, comparisonUnary, modulusRoute,
      comparisonRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
