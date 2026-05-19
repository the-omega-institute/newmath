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

end BEDC.Derived.RealityConstrainedTruthCertUp
