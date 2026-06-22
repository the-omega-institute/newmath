import BEDC.Derived.LayeredRelationGateUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.LayeredRelationGateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem LayeredRelationGateCarrier_classifier_obligation
    {A B L P N F G H C Pi verdictRead : BHist} :
    Cont P N verdictRead →
      UnaryHistory P →
        UnaryHistory N →
          List.Mem (layeredRelationGateEncodeBHist P)
              (layeredRelationGateToEventFlow
                (LayeredRelationGateUp.mk A B L P N F G H C Pi)) ∧
            List.Mem (layeredRelationGateEncodeBHist N)
              (layeredRelationGateToEventFlow
                (LayeredRelationGateUp.mk A B L P N F G H C Pi)) ∧
              UnaryHistory verdictRead := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory
  intro verdictRoute preservedUnary notPreservedUnary
  have preservedDisplayed :
      List.Mem (layeredRelationGateEncodeBHist P)
        (layeredRelationGateToEventFlow
          (LayeredRelationGateUp.mk A B L P N F G H C Pi)) := by
    simp only [layeredRelationGateToEventFlow]
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    exact List.Mem.head _
  have notPreservedDisplayed :
      List.Mem (layeredRelationGateEncodeBHist N)
        (layeredRelationGateToEventFlow
          (LayeredRelationGateUp.mk A B L P N F G H C Pi)) := by
    simp only [layeredRelationGateToEventFlow]
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    exact List.Mem.head _
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed preservedUnary notPreservedUnary verdictRoute
  exact ⟨preservedDisplayed, notPreservedDisplayed, verdictUnary⟩

end BEDC.Derived.LayeredRelationGateUp
