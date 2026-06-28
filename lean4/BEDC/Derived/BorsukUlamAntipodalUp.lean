import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BorsukUlamAntipodalUp : Type where
  | mk (S A T L O H C P N : BHist) : BorsukUlamAntipodalUp
  deriving DecidableEq

def borsukUlamAntipodalRows : BorsukUlamAntipodalUp -> List BHist
  | BorsukUlamAntipodalUp.mk S A T L O H C P N => [S, A, T, L, O, H, C, P, N]

end BEDC.Derived
