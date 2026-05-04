import BEDC.Derived.ListUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def ListUnaryLength : ListCarrier BHist -> BHist
  | [] => BHist.Empty
  | _ :: xs => BHist.e1 (ListUnaryLength xs)

theorem ListUnaryLength_append_cont {xs ys : ListCarrier BHist} :
    Cont (ListUnaryLength ys) (ListUnaryLength xs) (ListUnaryLength (xs ++ ys)) := by
  induction xs with
  | nil =>
      exact cont_right_unit (ListUnaryLength ys)
  | cons _ xs ih =>
      exact cont_step_one ih

end BEDC.Derived.ListUp
