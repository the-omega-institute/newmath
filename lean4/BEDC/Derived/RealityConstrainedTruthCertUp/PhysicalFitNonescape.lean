import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RealityConstrainedTruthCertPhysicalFitNonescape
    (x : TasteGate.RealityConstrainedTruthCertUp) :
    exists S Sigma K T U D I L F N fitRoute methodologyRoute physicalRead : BHist,
      x = TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N /\
        TasteGate.realityConstrainedTruthCertFields x = [S, Sigma, K, T, U, D, I, L, F, N] /\
          Cont F L fitRoute /\
            Cont fitRoute K methodologyRoute /\
              Cont methodologyRoute N physicalRead /\
                hsame physicalRead (append (append (append F L) K) N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  cases x with
  | mk S Sigma K T U D I L F N =>
      exact
        ⟨S, Sigma, K, T, U, D, I, L, F, N, append F L, append (append F L) K,
          append (append (append F L) K) N, rfl, rfl, rfl, rfl, rfl,
          hsame_refl (append (append (append F L) K) N)⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
