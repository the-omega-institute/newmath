import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RealityConstrainedTruthCertLedgerExactness
    (x : TasteGate.RealityConstrainedTruthCertUp) :
    exists S Sigma K T U D I L F N : BHist,
      x = TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N /\
        TasteGate.realityConstrainedTruthCertFields x = [S, Sigma, K, T, U, D, I, L, F, N] /\
          Cont L F (append L F) /\
            hsame (append L F) (append L F) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  cases x with
  | mk S Sigma K T U D I L F N =>
      exact ⟨S, Sigma, K, T, U, D, I, L, F, N, rfl, rfl, rfl, hsame_refl (append L F)⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
