import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LovaszLocalLemmaUp : Type where
  | mk (Omega Events Dependency RandomRows Avoidance Bounds Independence H C P N : BHist) :
      LovaszLocalLemmaUp

end BEDC.Derived
