import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.JordanDecompositionBoundedVariationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

inductive JordanDecompositionBoundedVariationUp : Type where
  | mk
      (boundedVariationSource finiteVariationLedger positiveLedger negativeLedger monotonicityWitness
        regSeqReadback dyadicTolerance realSeal transport replay provenance localName : BHist) :
      JordanDecompositionBoundedVariationUp
  deriving DecidableEq

theorem JordanDecompositionBoundedVariationNameCertObligations
    (J : JordanDecompositionBoundedVariationUp) :
    ∃ B L Ppos Pneg M R D E H C Q N sourceLedger signedLedger readbackSeal : BHist,
      J = JordanDecompositionBoundedVariationUp.mk B L Ppos Pneg M R D E H C Q N ∧
        Cont B L sourceLedger ∧
          Cont Ppos Pneg signedLedger ∧
            Cont R D readbackSeal ∧ hsame E E := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases J with
  | mk B L Ppos Pneg M R D E H C Q N =>
      exact
        ⟨B, L, Ppos, Pneg, M, R, D, E, H, C, Q, N, append B L, append Ppos Pneg,
          append R D, rfl, rfl, rfl, rfl, rfl⟩

theorem JordanDecompositionBoundedVariationConsumerRoute
    (J : JordanDecompositionBoundedVariationUp) :
    ∃ B L Ppos Pneg M R D E H C Q N sourceLedger signedLedger readbackSeal
        consumerRoute : BHist,
      J = JordanDecompositionBoundedVariationUp.mk B L Ppos Pneg M R D E H C Q N ∧
        Cont B L sourceLedger ∧
          Cont Ppos Pneg signedLedger ∧
            Cont R D readbackSeal ∧
              Cont sourceLedger readbackSeal consumerRoute ∧ hsame E E := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases J with
  | mk B L Ppos Pneg M R D E H C Q N =>
      exact
        ⟨B, L, Ppos, Pneg, M, R, D, E, H, C, Q, N, append B L, append Ppos Pneg,
          append R D, append (append B L) (append R D), rfl, rfl, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.JordanDecompositionBoundedVariationUp
