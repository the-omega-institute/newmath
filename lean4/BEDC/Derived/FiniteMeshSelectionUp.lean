import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FiniteMeshSelectionUp : Type where
  | mk (D W R I E H C P N : BHist) : FiniteMeshSelectionUp
  deriving DecidableEq

def finiteMeshSelectionRows : FiniteMeshSelectionUp -> List BHist
  | FiniteMeshSelectionUp.mk D W R I E H C P N => [D, W, R, I, E, H, C, P, N]

theorem FiniteMeshSelectionUp_inhabited : Nonempty FiniteMeshSelectionUp := by
  exact
    Nonempty.intro
      (FiniteMeshSelectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)

end BEDC.Derived
