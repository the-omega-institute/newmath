import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RealityConstrainedTruthCert_l10_failure_ledger_lock
    (x : TasteGate.RealityConstrainedTruthCertUp) :
    exists S Sigma K T U D I L F N ledgerFailure namedLedger : BHist,
      x = TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N ∧
        TasteGate.realityConstrainedTruthCertFields x = [S, Sigma, K, T, U, D, I, L, F, N] ∧
          Cont L F ledgerFailure ∧ Cont ledgerFailure N namedLedger ∧
            hsame namedLedger (append (append L F) N) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases x with
  | mk S Sigma K T U D I L F N =>
      exact
        ⟨S, Sigma, K, T, U, D, I, L, F, N, append L F, append (append L F) N,
          rfl, rfl, rfl, rfl, hsame_refl (append (append L F) N)⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
