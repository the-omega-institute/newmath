import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MetaCICNormalizationSubstitutionBoundaryUp : Type where
  | mk : (F C S D O H R P N : BHist) → MetaCICNormalizationSubstitutionBoundaryUp
  deriving DecidableEq

end BEDC.Derived
