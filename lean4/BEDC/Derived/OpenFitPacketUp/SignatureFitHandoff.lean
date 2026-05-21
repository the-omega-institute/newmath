import BEDC.Derived.OpenFitPacketUp.NoFinalOracleBoundary

namespace BEDC.Derived.OpenFitPacketUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem OpenFitSignatureFitHandoff {H Pi S M F E L B N fitRead auditRead : BHist} :
    OpenFitPacketCarrier H Pi S M F E L B N ->
      Cont S M fitRead ->
        Cont fitRead L auditRead ->
          UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory F ∧ UnaryHistory E ∧
            UnaryHistory L ∧ UnaryHistory B ∧ UnaryHistory fitRead ∧
              UnaryHistory auditRead ∧ Cont S M F ∧ Cont F E L ∧ Cont L B N ∧
                Cont S M fitRead ∧ Cont fitRead L auditRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory OpenFitPacketCarrier
  intro carrier fitRoute auditRoute
  obtain ⟨_unaryH, _unaryPi, unaryS, unaryM, unaryF, unaryE, unaryL, unaryB, _unaryN,
    _routeS, routeF, routeL, routeN⟩ := carrier
  have fitReadUnary : UnaryHistory fitRead :=
    unary_cont_closed unaryS unaryM fitRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed fitReadUnary unaryL auditRoute
  exact
    ⟨unaryS, unaryM, unaryF, unaryE, unaryL, unaryB, fitReadUnary, auditReadUnary,
      routeF, routeL, routeN, fitRoute, auditRoute⟩

end BEDC.Derived.OpenFitPacketUp
