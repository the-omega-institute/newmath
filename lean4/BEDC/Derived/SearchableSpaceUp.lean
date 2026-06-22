import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SearchableSpaceUp : Type where
  | mk
      (schedule predicate witness compactHandoff transport replay provenance name : BHist) :
      SearchableSpaceUp
  deriving DecidableEq

end BEDC.Derived
