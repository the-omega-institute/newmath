import BEDC.FKernel.Hist

namespace BEDC.Derived.MetaCICLocalConfluenceFrontierUp

open BEDC.FKernel.Hist

inductive MetaCICLocalConfluenceFrontierUp : Type where
  | mk (K J S O H T P N : BHist) : MetaCICLocalConfluenceFrontierUp

end BEDC.Derived.MetaCICLocalConfluenceFrontierUp
