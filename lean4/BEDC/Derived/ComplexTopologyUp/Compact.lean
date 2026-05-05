import BEDC.Derived.ComplexTopologyUp

namespace BEDC.Derived.ComplexTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ComplexTopologyCompact (K : BHist -> Prop) : Prop :=
  ∃ bound : BHist,
    UnaryHistory bound ∧
      (∀ {z : BHist}, K z ->
        ∃ gap : BHist, ComplexTopologyClosedDiskGap BHist.Empty bound z gap) ∧
        (∀ precision : BHist, UnaryHistory precision ->
          ∃ net : List BHist, ComplexTopologyDyadicNet K precision net)

theorem ComplexTopologyCompact_net_witness {K : BHist -> Prop} {precision : BHist} :
    ComplexTopologyCompact K -> UnaryHistory precision ->
      ∃ net : List BHist, ComplexTopologyDyadicNet K precision net := by
  intro compact precisionCarrier
  cases compact with
  | intro _bound compactData =>
      exact compactData.right.right precision precisionCarrier

end BEDC.Derived.ComplexTopologyUp
