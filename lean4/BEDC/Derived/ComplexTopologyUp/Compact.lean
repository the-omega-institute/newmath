import BEDC.Derived.ComplexTopologyUp

namespace BEDC.Derived.ComplexTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ComplexTopologyCompact (K : BHist -> Prop) (bound : BHist)
    (net : BHist -> List BHist) : Prop :=
  UnaryHistory bound ∧
    forall {precision : BHist}, UnaryHistory precision ->
      ComplexTopologyDyadicNet K precision (net precision)

theorem ComplexTopologyCompact_precision_radius_not_empty
    {K : BHist -> Prop} {bound precision z : BHist} {net : BHist -> List BHist} :
    ComplexTopologyCompact K bound net -> UnaryHistory precision -> K z ->
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

end BEDC.Derived.ComplexTopologyUp
