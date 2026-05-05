import BEDC.Derived.PadicUp
import BEDC.Derived.PrimeUp.PrimeShape

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.PrimeUp

theorem PadicPrimeScale_append_unit_left_result_hsame {p q e r : BHist} :
    UnaryHistory q -> PadicPrimeScale p q e ->
      PadicPrimeScale p (append (BHist.e1 BHist.Empty) q) r -> hsame r (append p e) := by
  intro unaryQ scaleE scaleR
  have predecessor := PadicPrimeScale_append_unit_left_predecessor_unique unaryQ scaleR
  cases predecessor with
  | intro pred data =>
      have samePredE : hsame pred e := data.right.right e scaleE
      exact cont_respects_hsame (hsame_refl p) samePredE data.right.left (cont_intro rfl)

theorem PadicPrimeScale_append_unit_left_result_not_empty {p q e r : BHist} :
    UnaryHistory q -> PadicPrimeScale p q e ->
      PadicPrimeScale p (append (BHist.e1 BHist.Empty) q) r ->
        hsame r BHist.Empty -> False := by
  intro unaryQ scaleE scaleR resultEmpty
  have predecessor := PadicPrimeScale_append_unit_left_predecessor_unique unaryQ scaleR
  cases predecessor with
  | intro pred data =>
      have predEmpty : hsame pred BHist.Empty := by
        have continuationEmpty : Cont p pred BHist.Empty :=
          cont_result_hsame_transport data.right.left resultEmpty
        exact (cont_empty_result_inversion continuationEmpty).right
      have eEmpty : hsame e BHist.Empty :=
        hsame_trans (hsame_symm (data.right.right e scaleE)) predEmpty
      have qEmpty : hsame q BHist.Empty :=
        Iff.mp (PadicPrimeScale_empty_result_iff_empty_exponent scaleE) eEmpty
      have pEmpty : hsame p BHist.Empty := by
        have continuationEmpty : Cont p pred BHist.Empty :=
          cont_result_hsame_transport data.right.left resultEmpty
        exact (cont_empty_result_inversion continuationEmpty).left
      exact NatPrime_empty_absurd scaleR.left pEmpty

end BEDC.Derived.PadicUp
