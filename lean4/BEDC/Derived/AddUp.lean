import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Unary

namespace BEDC.Derived.AddUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem AddUnaryContinuation_hsame_transport {h h' k k' r r' : BHist} :
    UnaryHistory h -> UnaryHistory k -> Cont h k r -> hsame h h' -> hsame k k' ->
      hsame r r' -> UnaryHistory h' ∧ UnaryHistory k' ∧ UnaryHistory r' ∧ Cont h' k' r' := by
  intro unaryH unaryK continuation sameH sameK sameR
  have unaryH' : UnaryHistory h' := unary_transport unaryH sameH
  have unaryK' : UnaryHistory k' := unary_transport unaryK sameK
  have continuation' : Cont h' k' r' :=
    cont_hsame_transport sameH sameK sameR continuation
  have unaryR' : UnaryHistory r' := unary_cont_closed unaryH' unaryK' continuation'
  exact ⟨unaryH', unaryK', unaryR', continuation'⟩

inductive AddUpThreePointCarrier : BHist → Prop where
  | empty : AddUpThreePointCarrier BHist.Empty
  | point0 : AddUpThreePointCarrier (BHist.e0 BHist.Empty)
  | point1 : AddUpThreePointCarrier (BHist.e1 BHist.Empty)

def AddUpThreePointMul : BHist → BHist → BHist
  | BHist.Empty, y => y
  | BHist.e0 _, _ => BHist.e0 BHist.Empty
  | BHist.e1 _, _ => BHist.e1 BHist.Empty

theorem AddUpThreePoint_unital_graph_not_swapped_commutative :
    let e : BHist := BHist.Empty
    let p : BHist := BHist.e0 BHist.Empty
    let q : BHist := BHist.e1 BHist.Empty
    AddUpThreePointCarrier e ∧ AddUpThreePointCarrier p ∧ AddUpThreePointCarrier q ∧
      (forall x : BHist, AddUpThreePointCarrier x ->
        hsame (AddUpThreePointMul e x) x ∧ hsame (AddUpThreePointMul x e) x) ∧
      hsame (AddUpThreePointMul p q) p ∧ hsame (AddUpThreePointMul q p) q ∧
        (hsame p q -> False) := by
  constructor
  · exact AddUpThreePointCarrier.empty
  · constructor
    · exact AddUpThreePointCarrier.point0
    · constructor
      · exact AddUpThreePointCarrier.point1
      · constructor
        · intro x carrier
          cases carrier with
          | empty => exact And.intro rfl rfl
          | point0 => exact And.intro rfl rfl
          | point1 => exact And.intro rfl rfl
        · constructor
          · rfl
          · constructor
            · rfl
            · intro same
              exact not_hsame_e0_e1 same

end BEDC.Derived.AddUp
