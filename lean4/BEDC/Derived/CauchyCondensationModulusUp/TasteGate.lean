import BEDC.FKernel.Hist

namespace BEDC.Derived.CauchyCondensationModulusUp

open BEDC.FKernel.Hist

inductive CauchyCondensationModulusUp : Type where
  | mk (K M B W Q D E H C P N : BHist) : CauchyCondensationModulusUp
  deriving DecidableEq

theorem CauchyCondensationModulusUp_carrier_nonempty :
    Nonempty CauchyCondensationModulusUp :=
  ⟨CauchyCondensationModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
    BHist.Empty⟩

end BEDC.Derived.CauchyCondensationModulusUp
