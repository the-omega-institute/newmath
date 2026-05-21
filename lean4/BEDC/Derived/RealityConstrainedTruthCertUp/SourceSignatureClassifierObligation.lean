import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Hist

theorem RealityConstrainedTruthCertSourceSignatureClassifierObligation
    (x : TasteGate.RealityConstrainedTruthCertUp) :
    exists S Sigma K T U D I L F N : BHist,
      x = TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N /\
        TasteGate.realityConstrainedTruthCertFields x = [S, Sigma, K, T, U, D, I, L, F, N] /\
          hsame (BEDC.FKernel.Cont.append S Sigma) (BEDC.FKernel.Cont.append S Sigma) /\
            BEDC.FKernel.Cont.Cont S Sigma (BEDC.FKernel.Cont.append S Sigma) /\
              BEDC.FKernel.Cont.Cont (BEDC.FKernel.Cont.append S Sigma) K
                (BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append S Sigma) K) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  cases x with
  | mk S Sigma K T U D I L F N =>
      exact ⟨S, Sigma, K, T, U, D, I, L, F, N, rfl, rfl,
        BEDC.FKernel.Hist.hsame_refl (BEDC.FKernel.Cont.append S Sigma), rfl, rfl⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
