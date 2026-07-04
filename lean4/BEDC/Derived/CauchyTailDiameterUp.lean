import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

inductive CauchyTailDiameterUp : Type where
  | mk
      (source threshold leftIndex rightIndex tolerance bound window transport replay provenance
        localName : BHist) :
      CauchyTailDiameterUp
  deriving DecidableEq

namespace CauchyTailDiameterUp

def CauchyTailDiameterCarrier
    (source threshold leftIndex rightIndex tolerance bound window transport replay provenance
      localName : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory source ∧ UnaryHistory threshold ∧ UnaryHistory leftIndex ∧
    UnaryHistory rightIndex ∧ UnaryHistory tolerance ∧ UnaryHistory bound ∧
      UnaryHistory window ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName

theorem CauchyTailDiameterCarrier_tail_window_handoff
    {source threshold leftIndex rightIndex tolerance bound window transport replay provenance
      localName read : BHist} :
    CauchyTailDiameterCarrier source threshold leftIndex rightIndex tolerance bound window
        transport replay provenance localName ->
      Cont source threshold leftIndex ->
        Cont leftIndex rightIndex tolerance ->
          Cont tolerance bound window ->
            Cont window replay read ->
              UnaryHistory read ∧ Cont source threshold leftIndex ∧
                Cont leftIndex rightIndex tolerance ∧ Cont tolerance bound window ∧
                  Cont window replay read := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier sourceThreshold leftRight toleranceBound windowReplay
  obtain ⟨sourceUnary, thresholdUnary, _leftIndexUnary, rightIndexUnary, _toleranceUnary,
    boundUnary, _windowUnary, _transportUnary, replayUnary, _provenanceUnary,
    _localNameUnary⟩ := carrier
  have leftIndexUnary : UnaryHistory leftIndex :=
    unary_cont_closed sourceUnary thresholdUnary sourceThreshold
  have toleranceUnary : UnaryHistory tolerance :=
    unary_cont_closed leftIndexUnary rightIndexUnary leftRight
  have windowUnary : UnaryHistory window :=
    unary_cont_closed toleranceUnary boundUnary toleranceBound
  have readUnary : UnaryHistory read :=
    unary_cont_closed windowUnary replayUnary windowReplay
  exact
    ⟨readUnary, sourceThreshold, leftRight, toleranceBound, windowReplay⟩

end CauchyTailDiameterUp

end BEDC.Derived
