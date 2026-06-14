import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentialSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SequentialSpaceCarrier
    (source topology sequence convergence window transport replay provenance localName : BHist) :
    Prop :=
  UnaryHistory source ∧ UnaryHistory topology ∧ UnaryHistory sequence ∧
    UnaryHistory convergence ∧ UnaryHistory window ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont source sequence window ∧ Cont window convergence replay ∧
          hsame transport replay

theorem SequentialSpaceCarrier_namecert_obligations
    {source topology sequence convergence window transport replay provenance localName : BHist} :
    SequentialSpaceCarrier source topology sequence convergence window transport replay provenance
        localName ->
      UnaryHistory source ∧ UnaryHistory topology ∧ UnaryHistory sequence ∧
        UnaryHistory convergence ∧ UnaryHistory window ∧ UnaryHistory replay ∧
          hsame transport replay ∧ Cont source sequence window ∧
            Cont window convergence replay := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet
  obtain
    ⟨sourceUnary, topologyUnary, sequenceUnary, convergenceUnary, windowUnary,
      _transportUnary, replayUnary, _provenanceUnary, _localNameUnary, sourceSequence,
      convergenceReplay, transportReplay⟩ := packet
  exact
    ⟨sourceUnary, topologyUnary, sequenceUnary, convergenceUnary, windowUnary, replayUnary,
      transportReplay, sourceSequence, convergenceReplay⟩

end BEDC.Derived.SequentialSpaceUp
