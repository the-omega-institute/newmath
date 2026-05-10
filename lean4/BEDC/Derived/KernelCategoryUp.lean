import BEDC.Derived.CategoryUp

namespace BEDC.Derived.KernelCategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

structure SourceRows where
  objSource : BHist
  objTarget : BHist
  morphismWitness : BHist
  carrier : CategoryHomCarrier objSource objTarget morphismWitness

def Pattern (s : SourceRows) : Prop :=
  CategoryHomCarrier s.objSource s.objTarget s.morphismWitness

def Classifier (s t : SourceRows) : Prop :=
  hsame s.objSource t.objSource ∧
    hsame s.objTarget t.objTarget ∧
      hsame s.morphismWitness t.morphismWitness

def identityRow (object : BHist) (carrier : UnaryHistory object) : SourceRows where
  objSource := object
  objTarget := object
  morphismWitness := BHist.Empty
  carrier := CategoryHomCarrier_empty_identity carrier

def composeRows (left right : SourceRows) (middle : hsame left.objTarget right.objSource)
    {composite : BHist} (comp : Cont left.morphismWitness right.morphismWitness composite) :
    SourceRows := by
  have rightAtMiddle : CategoryHomCarrier left.objTarget right.objTarget right.morphismWitness :=
    CategoryHomCarrier_hsame_transport (hsame_symm middle) (hsame_refl right.objTarget)
      (hsame_refl right.morphismWitness) right.carrier
  exact
    { objSource := left.objSource
      objTarget := right.objTarget
      morphismWitness := composite
      carrier := CategoryHomCarrier_comp_closed left.carrier rightAtMiddle comp }

theorem stability {left right : SourceRows}
    (middle : hsame left.objTarget right.objSource) {composite : BHist}
    (comp : Cont left.morphismWitness right.morphismWitness composite) :
    Pattern (identityRow left.objSource left.carrier.left) ∧
      Pattern (identityRow right.objTarget right.carrier.right.left) ∧
        Pattern (composeRows left right middle comp) ∧
          Classifier (composeRows left right middle comp)
            (composeRows left right middle comp) := by
  constructor
  · exact (identityRow left.objSource left.carrier.left).carrier
  · constructor
    · exact (identityRow right.objTarget right.carrier.right.left).carrier
    · constructor
      · exact (composeRows left right middle comp).carrier
      · constructor
        · exact hsame_refl (composeRows left right middle comp).objSource
        · constructor
          · exact hsame_refl (composeRows left right middle comp).objTarget
          · exact hsame_refl (composeRows left right middle comp).morphismWitness

structure Ledger where
  left : SourceRows
  right : SourceRows
  middle : hsame left.objTarget right.objSource
  composite : BHist
  composition : Cont left.morphismWitness right.morphismWitness composite

end BEDC.Derived.KernelCategoryUp
