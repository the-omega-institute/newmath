import BEDC.FKernel.Cont.Units
import BEDC.Derived.RealAnalyticUp

namespace BEDC.Derived.RealAnalyticUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexSeriesUp

theorem RealAnalyticCosEmpty_constant_one {one n result endpoint : BHist}
    {cosTerm : BHist -> BHist} :
    hsame one (BHist.e1 BHist.Empty) ->
      (forall {m : BHist}, UnaryHistory m -> hsame (cosTerm m) BHist.Empty) ->
        ComplexPartSum one cosTerm n result -> Cont result BHist.Empty endpoint ->
          hsame endpoint one ∧ UnaryHistory endpoint := by
  intro sameOne termEmpty partialSum endpointCont
  have partialRows :=
    RealAnalyticCosPart_empty_constant_one sameOne termEmpty partialSum
  have sameEndpointResult : hsame endpoint result :=
    cont_right_unit_result endpointCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_transport
      (ComplexPartSum_result_unary
        (unary_transport (unary_e1_closed unary_empty) (hsame_symm sameOne))
        (fun {m : BHist} unaryM =>
          unary_transport unary_empty (hsame_symm (termEmpty unaryM)))
        partialSum)
      (hsame_symm sameEndpointResult)
  exact And.intro (hsame_trans sameEndpointResult partialRows.right) endpointUnary

end BEDC.Derived.RealAnalyticUp
