import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive KolmogorovRieszFiniteTranslationUp : Type where
  | mk (F T D R Q B E H C P N : BHist) : KolmogorovRieszFiniteTranslationUp
  deriving DecidableEq

end BEDC.Derived
