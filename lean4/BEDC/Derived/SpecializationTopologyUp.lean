import BEDC.FKernel.Hist

namespace BEDC.Derived.SpecializationTopologyUp

open BEDC.FKernel.Hist

inductive SpecializationTopologyUp : Type where
  | mk (T S R H C P N : BHist) : SpecializationTopologyUp
  deriving DecidableEq

theorem carrier_nonempty : Nonempty SpecializationTopologyUp :=
  Nonempty.intro
    (SpecializationTopologyUp.mk
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)

end BEDC.Derived.SpecializationTopologyUp
