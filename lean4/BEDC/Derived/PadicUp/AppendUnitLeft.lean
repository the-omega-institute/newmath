import BEDC.Derived.PadicUp

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem PadicPrimeScale_append_unit_left_result_hsame {p q e r : BHist} :
    UnaryHistory q -> PadicPrimeScale p q e ->
      PadicPrimeScale p (append (BHist.e1 BHist.Empty) q) r -> hsame r (append p e) := by
  intro unaryQ scaleE scaleR
  have predecessor := PadicPrimeScale_append_unit_left_predecessor_unique unaryQ scaleR
  cases predecessor with
  | intro pred data =>
      have samePredE : hsame pred e := data.right.right e scaleE
      exact cont_respects_hsame (hsame_refl p) samePredE data.right.left (cont_intro rfl)

end BEDC.Derived.PadicUp
