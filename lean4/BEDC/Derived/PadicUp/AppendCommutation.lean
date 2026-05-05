import BEDC.Derived.PadicUp

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem PadicPrimeScale_append_factor_results_comm_hsame {p w q n e r s : BHist} :
    PadicPrimeScale p w n -> PadicPrimeScale p q e -> Cont n e r -> Cont e n s ->
      hsame r s := by
  intro left right leftContinuation rightContinuation
  have leftComponents := PadicPrimeScale_unary_components left
  have rightComponents := PadicPrimeScale_unary_components right
  exact hsame_trans leftContinuation
    (hsame_trans
      (unary_append_comm_hsame leftComponents.right.right rightComponents.right.right)
      (hsame_symm rightContinuation))

end BEDC.Derived.PadicUp
