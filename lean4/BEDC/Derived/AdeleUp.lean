import BEDC.Derived.RealUp
import BEDC.Derived.PadicUp

namespace BEDC.Derived.AdeleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RealUp
open BEDC.Derived.PadicUp

def AdeleHistoryCarrier (h : BHist) : Prop :=
  ∃ real : BHist, ∃ p : BHist, ∃ exponent : BHist, ∃ result : BHist,
    RealConstantHistoryCarrier real ∧ PadicPrimeScale p exponent result ∧
      hsame h (append real result)

theorem AdeleHistoryCarrier_not_empty {h : BHist} :
    AdeleHistoryCarrier h -> hsame h BHist.Empty -> False := by
  intro carrier emptyH
  cases carrier with
  | intro real rest =>
      cases rest with
      | intro _p rest =>
          cases rest with
          | intro _exponent rest =>
              cases rest with
              | intro result data =>
                  have appendEmpty : hsame (append real result) BHist.Empty :=
                    hsame_trans (hsame_symm data.right.right) emptyH
                  have emptyParts := append_eq_empty_iff.mp appendEmpty
                  cases data.left with
                  | intro witness realData =>
                      exact not_hsame_emp_e1
                        (hsame_trans (hsame_symm emptyParts.left) realData.left)

end BEDC.Derived.AdeleUp
