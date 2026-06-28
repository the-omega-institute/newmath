import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DyadicDistanceUp : Type where
  | mk (left right scale signed abs ledger transport replay provenance name : BHist) :
      DyadicDistanceUp
  deriving DecidableEq, Repr

end BEDC.Derived
