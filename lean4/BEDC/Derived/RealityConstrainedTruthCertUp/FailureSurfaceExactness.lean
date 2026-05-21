import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RealityConstrainedTruthCertFailureSurfaceExactness
    (x : TasteGate.RealityConstrainedTruthCertUp) :
    exists S Sigma K T U D I L F N failureRead : BHist,
      x = TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N ∧
        TasteGate.realityConstrainedTruthCertFields x =
          [S, Sigma, K, T, U, D, I, L, F, N] ∧
          Cont F N failureRead ∧ hsame failureRead (append F N) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases x with
  | mk S Sigma K T U D I L F N =>
      exact
        ⟨S, Sigma, K, T, U, D, I, L, F, N, append F N, rfl, rfl, rfl,
          hsame_refl (append F N)⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
