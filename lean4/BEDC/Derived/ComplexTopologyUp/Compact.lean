import BEDC.Derived.ComplexTopologyUp

namespace BEDC.Derived.ComplexTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ComplexTopologyCompactNetFunction (K : BHist -> Prop) (bound : BHist)
    (net : BHist -> List BHist) : Prop :=
  UnaryHistory bound ∧
    forall {precision : BHist}, UnaryHistory precision ->
      ComplexTopologyDyadicNet K precision (net precision)

theorem ComplexTopologyCompact_precision_radius_not_empty
    {K : BHist -> Prop} {bound precision z : BHist} {net : BHist -> List BHist} :
    ComplexTopologyCompactNetFunction K bound net -> UnaryHistory precision -> K z ->
      exists center gap : BHist,
        List.Mem center (net precision) ∧
          ComplexTopologyOpenDiskGap center precision z gap ∧
            (hsame precision BHist.Empty -> False) := by
  intro compact precisionUnary member
  have precisionNet : ComplexTopologyDyadicNet K precision (net precision) :=
    compact.right precisionUnary
  cases precisionNet.right z member with
  | intro center witness =>
      cases witness with
      | intro gap witnessData =>
          exact Exists.intro center
            (Exists.intro gap
              (And.intro witnessData.left
                (And.intro witnessData.right
                  (ComplexTopologyOpenDiskGap_radius_not_empty witnessData.right))))

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
