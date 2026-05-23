import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RealityConstrainedTruthCertExportReadiness
    (x : TasteGate.RealityConstrainedTruthCertUp) :
    exists S Sigma K T U D I L F N sourceSig classifierRead towerRead
      descentInvariantRead ledgerFailure failureRead exportRead : BHist,
      x = TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N ∧
        TasteGate.realityConstrainedTruthCertFields x =
          [S, Sigma, K, T, U, D, I, L, F, N] ∧
          Cont S Sigma sourceSig ∧
            Cont sourceSig K classifierRead ∧
              Cont T U towerRead ∧
                Cont D I descentInvariantRead ∧
                  Cont L F ledgerFailure ∧
                    Cont F N failureRead ∧
                      Cont classifierRead ledgerFailure exportRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases x with
  | mk S Sigma K T U D I L F N =>
      exact
        ⟨S, Sigma, K, T, U, D, I, L, F, N, append S Sigma, append (append S Sigma) K,
          append T U, append D I, append L F, append F N, append (append (append S Sigma) K)
            (append L F), rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
