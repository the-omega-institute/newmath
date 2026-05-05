import BEDC.Derived.ComplexSeriesUp

namespace BEDC.Derived.ComplexSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CauchyProduct_result_unary {zero : BHist} {a b : BHist -> BHist}
    {n result : BHist} (zeroUnary : UnaryHistory zero)
    (aUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (a m))
    (bUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (b m)) :
    CauchyProduct zero a b n result -> UnaryHistory result := by
  intro product
  cases product with
  | intro left productRest =>
      cases productRest with
      | intro right data =>
          exact unary_cont_closed
            (ComplexPartSum_result_unary zeroUnary aUnary data.left)
            (ComplexPartSum_result_unary zeroUnary bUnary data.right.left)
            data.right.right

end BEDC.Derived.ComplexSeriesUp
