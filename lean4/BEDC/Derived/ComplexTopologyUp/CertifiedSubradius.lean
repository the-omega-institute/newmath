import BEDC.Derived.ComplexTopologyUp

namespace BEDC.Derived.ComplexTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def ComplexTopologyCertifiedSubradius (inner outer tail : BHist) : Prop :=
  UnaryHistory inner ∧ UnaryHistory outer ∧ UnaryHistory tail ∧ Cont inner tail outer

theorem ComplexTopologyOpenDiskGap_certified_subradius_extension
    {center rSmall rLarge point gap tail gapLarge : BHist} :
    ComplexTopologyOpenDiskGap center rSmall point gap ->
      ComplexTopologyCertifiedSubradius rSmall rLarge tail -> Cont gap tail gapLarge ->
        ComplexTopologyOpenDiskGap center rLarge point gapLarge ∧ Cont point gapLarge rLarge := by
  intro disk subradius gapTail
  exact ComplexTopologyOpenDiskGap_radius_extension_closed disk subradius.right.right.left
    subradius.right.right.right gapTail

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

end BEDC.Derived.ComplexTopologyUp
