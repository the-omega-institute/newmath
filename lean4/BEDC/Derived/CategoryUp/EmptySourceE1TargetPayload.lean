import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_empty_source_e1_target_payload_iff {r k : BHist} :
    CategoryHomCarrier BHist.Empty (BHist.e1 r) (BHist.e1 k) <->
      UnaryHistory r /\ hsame k r := by
  constructor
  · intro homCarrier
    have data :=
      (CategoryHomCarrier_empty_source_iff (b := BHist.e1 r) (f := BHist.e1 k)).mp
        homCarrier
    exact And.intro (unary_e1_inversion data.left) (hsame_e1_iff.mp data.right)
  · intro data
    exact
      (CategoryHomCarrier_empty_source_iff (b := BHist.e1 r) (f := BHist.e1 k)).mpr
        (And.intro (unary_e1_closed data.left) (hsame_e1_congr data.right))

end BEDC.Derived.CategoryUp
