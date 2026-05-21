import BEDC.Derived.MeasureUp.RootPublicObligationBasis

namespace BEDC.Derived.MeasureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MeasureRootDownstreamUnblockPackage
    {event union value sum endpoint total integralRead probabilityRead : BHist} :
    MeasureRootPublicObligationBasis event union value sum endpoint ->
      Cont endpoint BHist.Empty total ->
        Cont endpoint total integralRead ->
          Cont total endpoint probabilityRead ->
            MeasureEventRowCoverage event union value sum endpoint ∧
              MeasureZeroBHistCarrier total ∧ UnaryHistory total ∧
                UnaryHistory integralRead ∧ UnaryHistory probabilityRead ∧
                  Cont endpoint total integralRead ∧
                    Cont total endpoint probabilityRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro basis endpointTotal integralRoute probabilityRoute
  have publicRows :
      MeasureEventRowCoverage event union value sum endpoint ∧ hsame endpoint BHist.Empty :=
    MeasureRootPublicObligationBasis_event_row_coverage basis
  have totalSameEndpoint : hsame total endpoint :=
    cont_right_unit_result endpointTotal
  have totalZero : MeasureZeroBHistCarrier total :=
    hsame_trans totalSameEndpoint publicRows.right
  have totalUnary : UnaryHistory total :=
    unary_transport unary_empty (hsame_symm totalZero)
  have endpointUnary : UnaryHistory endpoint :=
    unary_transport totalUnary totalSameEndpoint
  have integralUnary : UnaryHistory integralRead :=
    unary_cont_closed endpointUnary totalUnary integralRoute
  have probabilityUnary : UnaryHistory probabilityRead :=
    unary_cont_closed totalUnary endpointUnary probabilityRoute
  exact
    ⟨publicRows.left, totalZero, totalUnary, integralUnary, probabilityUnary, integralRoute,
      probabilityRoute⟩

end BEDC.Derived.MeasureUp
