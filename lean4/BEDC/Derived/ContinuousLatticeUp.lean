import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive ContinuousLatticeUp : Type where
  | mk (D C W A S L H R P N : BHist) : ContinuousLatticeUp
  deriving DecidableEq

end BEDC.Derived
