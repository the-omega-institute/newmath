import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive PeetreKFunctionalUp : Type where
  | mk
      (source normedPair tolerance splitBudget valueReadback regularReadback streamWindow
        dyadicLedger realSeal transport replay provenance localName : BHist) :
      PeetreKFunctionalUp
  deriving DecidableEq

def peetreKFunctionalRows : PeetreKFunctionalUp -> List BHist
  | PeetreKFunctionalUp.mk S X T B V Q W D E H C P N => [S, X, T, B, V, Q, W, D, E, H, C, P, N]

end BEDC.Derived
