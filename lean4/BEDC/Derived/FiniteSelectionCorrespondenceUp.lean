import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FiniteSelectionCorrespondenceUp : Type where
  | mk (M K S W R D H C P N : BHist) : FiniteSelectionCorrespondenceUp

end BEDC.Derived
