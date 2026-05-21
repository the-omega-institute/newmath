import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem RealityConstrainedTruthCertRootNontrivialReadiness :
    exists x y : TasteGate.RealityConstrainedTruthCertUp,
      x ≠ y /\ BHistCarrier.toEventFlow x ≠ BHistCarrier.toEventFlow y := by
  -- BEDC touchpoint anchor: BHist BMark
  let x :=
    TasteGate.RealityConstrainedTruthCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  let y :=
    TasteGate.RealityConstrainedTruthCertUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  have hxy : x ≠ y := by
    intro h
    have hsource : BHist.Empty = BHist.e0 BHist.Empty := by
      injection h with hsource _ _ _ _ _ _ _ _ _
    cases hsource
  have hflow : BHistCarrier.toEventFlow x ≠ BHistCarrier.toEventFlow y :=
    ChapterTasteGate.layer_separation x y hxy
  exact ⟨x, y, hxy, hflow⟩

theorem RealityConstrainedTruthCertRootTasteGateObligation
    (x : TasteGate.RealityConstrainedTruthCertUp) :
    BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x /\
      exists S Sigma K T U D I L F N : BHist,
        x = TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N /\
          BHistCarrier.toEventFlow x =
            TasteGate.realityConstrainedTruthCertToEventFlow
              (TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N) /\
            hsame (append S Sigma) (append S Sigma) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  constructor
  · exact ChapterTasteGate.round_trip x
  · cases x with
    | mk S Sigma K T U D I L F N =>
        exact
          ⟨S, Sigma, K, T, U, D, I, L, F, N, rfl, rfl,
            hsame_refl (append S Sigma)⟩

theorem RealityConstrainedTruthCertRootFieldFaithfulReadiness
    (x y : TasteGate.RealityConstrainedTruthCertUp) :
    TasteGate.realityConstrainedTruthCertFields x =
        TasteGate.realityConstrainedTruthCertFields y →
      x = y ∧ BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hfields
  have hxy : x = y := by
    cases x with
    | mk S1 Sigma1 K1 T1 U1 D1 I1 L1 F1 N1 =>
        cases y with
        | mk S2 Sigma2 K2 T2 U2 D2 I2 L2 F2 N2 =>
            cases hfields
            rfl
  constructor
  · exact hxy
  · cases hxy
    rfl

end BEDC.Derived.RealityConstrainedTruthCertUp
