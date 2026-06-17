import BEDC.Derived.BishopLocatedCompletionEmbeddingUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopLocatedCompletionEmbeddingUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def BishopLocatedCompletionEmbeddingCarrier (M L D E R H C P _N : BHist) : Prop :=
  UnaryHistory M ∧ UnaryHistory L ∧ UnaryHistory D ∧ UnaryHistory E ∧
    UnaryHistory R ∧ Cont M L D ∧ Cont D E R ∧ Cont H C P

theorem BishopLocatedCompletionEmbeddingCarrier_row_exposure
    {M L D E R H C P N : BHist} :
    BishopLocatedCompletionEmbeddingCarrier M L D E R H C P N →
      UnaryHistory M ∧ UnaryHistory R ∧ Cont M L D ∧ Cont D E R ∧ Cont H C P := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier
  obtain
    ⟨metricUnary, _locatedUnary, _denseUnary, _embeddingUnary, readbackUnary,
      metricLocatedDense, denseEmbeddingReadback, transportReplay⟩ := carrier
  exact
    ⟨metricUnary, readbackUnary, metricLocatedDense, denseEmbeddingReadback, transportReplay⟩

end BEDC.Derived.BishopLocatedCompletionEmbeddingUp
