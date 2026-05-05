import BEDC.Derived.ComplexTopologyUp

namespace BEDC.Derived.ComplexTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def ComplexTopologyCertifiedSubradius (inner outer tail : BHist) : Prop :=
  UnaryHistory inner ∧ UnaryHistory outer ∧ UnaryHistory tail ∧ Cont inner tail outer

theorem ComplexTopologyCertifiedSubradius_comp {r0 r1 r2 e0 e1 e01 : BHist} :
    ComplexTopologyCertifiedSubradius r0 r1 e0 ->
      ComplexTopologyCertifiedSubradius r1 r2 e1 ->
        Cont e0 e1 e01 ->
          ComplexTopologyCertifiedSubradius r0 r2 e01 ∧ Cont r0 e01 r2 := by
  intro left right tailRel
  have e01Carrier : UnaryHistory e01 :=
    unary_cont_closed left.right.right.left right.right.right.left tailRel
  have radiusRel : Cont r0 e01 r2 := by
    apply cont_intro
    exact
      right.right.right.right.trans
        ((congrArg (fun h => append h e1) left.right.right.right).trans
          ((append_assoc r0 e0 e1).trans
            (congrArg (append r0) tailRel.symm)))
  exact
    And.intro
      (And.intro left.left
        (And.intro right.right.left
          (And.intro e01Carrier radiusRel)))
      radiusRel

theorem ComplexTopologyCertifiedSubradius_openDiskGap_extension_gap_readback
    {center inner outer point gap tail displayedGap : BHist} :
    ComplexTopologyOpenDiskGap center inner point gap ->
      ComplexTopologyCertifiedSubradius inner outer tail ->
        ComplexTopologyOpenDiskGap center outer point displayedGap ->
          hsame displayedGap (append gap tail) := by
  intro disk subradius displayed
  have gapStep : Cont gap tail (append gap tail) := by
    exact cont_intro rfl
  have extended :=
    ComplexTopologyOpenDiskGap_radius_extension_closed disk subradius.right.right.left
      subradius.right.right.right gapStep
  exact ComplexTopologyOpenDiskGap_gap_deterministic displayed extended.right

end BEDC.Derived.ComplexTopologyUp
