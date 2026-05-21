import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem RealityConstrainedTruthCertCarrierAdmission_eventflow_boundary
    (x : TasteGate.RealityConstrainedTruthCertUp) :
    ∃ S Sigma K T U D I L F N : BHist,
      x = TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N ∧
        TasteGate.realityConstrainedTruthCertFields x = [S, Sigma, K, T, U, D, I, L, F, N] ∧
          TasteGate.realityConstrainedTruthCertToEventFlow x =
            [[BMark.b0],
              TasteGate.realityConstrainedTruthCertEncodeBHist S,
              [BMark.b1, BMark.b0],
              TasteGate.realityConstrainedTruthCertEncodeBHist Sigma,
              [BMark.b1, BMark.b1, BMark.b0],
              TasteGate.realityConstrainedTruthCertEncodeBHist K,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              TasteGate.realityConstrainedTruthCertEncodeBHist T,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              TasteGate.realityConstrainedTruthCertEncodeBHist U,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              TasteGate.realityConstrainedTruthCertEncodeBHist D,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              TasteGate.realityConstrainedTruthCertEncodeBHist I,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b0],
              TasteGate.realityConstrainedTruthCertEncodeBHist L,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b0],
              TasteGate.realityConstrainedTruthCertEncodeBHist F,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b0],
              TasteGate.realityConstrainedTruthCertEncodeBHist N] ∧
            hsame (append S Sigma) (append S Sigma) := by
  -- BEDC touchpoint anchor: BHist BMark hsame
  cases x with
  | mk S Sigma K T U D I L F N =>
      exact ⟨S, Sigma, K, T, U, D, I, L, F, N, rfl, rfl, rfl,
        hsame_refl (append S Sigma)⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
