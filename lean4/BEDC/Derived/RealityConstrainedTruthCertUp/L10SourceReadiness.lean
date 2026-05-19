import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem RealityConstrainedTruthCertL10SourceReadiness
    (x : TasteGate.RealityConstrainedTruthCertUp) :
    exists S Sigma K T U D I L F N : BHist,
      x = TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N /\
        TasteGate.realityConstrainedTruthCertFields x = [S, Sigma, K, T, U, D, I, L, F, N] /\
          hsame (append K L) (append K L) /\ Cont L F (append L F) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S Sigma K T U D I L F N =>
      exact ⟨S, Sigma, K, T, U, D, I, L, F, N, rfl, rfl, hsame_refl (append K L), rfl⟩

theorem RealityConstrainedTruthCertL10SourceExposure
    (x : TasteGate.RealityConstrainedTruthCertUp) :
    exists S Sigma K T U D I L F N : BHist,
      x = TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N /\
        TasteGate.realityConstrainedTruthCertFields x = [S, Sigma, K, T, U, D, I, L, F, N] /\
          Cont S Sigma (append S Sigma) /\
            Cont T U (append T U) /\ Cont F N (append F N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  cases x with
  | mk S Sigma K T U D I L F N =>
      exact ⟨S, Sigma, K, T, U, D, I, L, F, N, rfl, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
