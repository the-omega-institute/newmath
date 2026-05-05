import BEDC.Derived.FunctorUp

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_comp_family_public_readback {a b c f g fg displayed : BHist} :
    (forall {p : BHist}, UnaryHistory p -> CategoryHomCarrier (append p a) (append p b) f) ->
      (forall {p : BHist}, UnaryHistory p -> CategoryHomCarrier (append p b) (append p c) g) ->
        Cont f g fg ->
          (forall {p : BHist}, UnaryHistory p ->
            CategoryHomCarrier (append p a) (append p c) displayed) ->
            hsame fg displayed := by
  intro leftFamily rightFamily comp displayedFamily
  have leftEmpty :
      CategoryHomCarrier (append BHist.Empty a) (append BHist.Empty b) f :=
    leftFamily (p := BHist.Empty) unary_empty
  have rightEmpty :
      CategoryHomCarrier (append BHist.Empty b) (append BHist.Empty c) g :=
    rightFamily (p := BHist.Empty) unary_empty
  have displayedEmpty :
      CategoryHomCarrier (append BHist.Empty a) (append BHist.Empty c) displayed :=
    displayedFamily (p := BHist.Empty) unary_empty
  have compositeEmpty :
      CategoryHomCarrier (append BHist.Empty a) (append BHist.Empty c) fg :=
    CategoryHomCarrier_comp_closed leftEmpty rightEmpty comp
  exact CategoryHomCarrier_morphism_deterministic compositeEmpty displayedEmpty

inductive RawFunctorSourceHom : BHist -> BHist -> BHist -> Prop
  | id_zero : RawFunctorSourceHom BHist.Empty BHist.Empty BHist.Empty
  | id_one :
      RawFunctorSourceHom (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)
        (BHist.e1 BHist.Empty)
  | arrow :
      RawFunctorSourceHom BHist.Empty (BHist.e1 BHist.Empty)
        (BHist.e1 (BHist.e1 BHist.Empty))

inductive RawFunctorTargetHom : BHist -> BHist -> BHist -> Prop
  | id_zero : RawFunctorTargetHom BHist.Empty BHist.Empty BHist.Empty
  | id_one :
      RawFunctorTargetHom (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)
        (BHist.e1 BHist.Empty)
  | reverse_arrow :
      RawFunctorTargetHom (BHist.e1 BHist.Empty) BHist.Empty
        (BHist.e1 (BHist.e1 BHist.Empty))

def RawFunctorObjectMap : BHist -> BHist
  | BHist.Empty => BHist.Empty
  | BHist.e0 h => BHist.e0 h
  | BHist.e1 h => BHist.e1 h

def RawFunctorMorphismMap : BHist -> BHist
  | BHist.Empty => BHist.Empty
  | BHist.e0 h => BHist.e0 h
  | BHist.e1 h => BHist.e1 h

def RawFunctorIdentityPreserving (objectMap morphismMap : BHist -> BHist) : Prop :=
  hsame (objectMap BHist.Empty) BHist.Empty ∧
    hsame (objectMap (BHist.e1 BHist.Empty)) (BHist.e1 BHist.Empty) ∧
      hsame (morphismMap BHist.Empty) BHist.Empty ∧
        hsame (morphismMap (BHist.e1 BHist.Empty)) (BHist.e1 BHist.Empty)

def RawFunctorCompositionPreserving (morphismMap : BHist -> BHist) : Prop :=
  hsame (morphismMap BHist.Empty) BHist.Empty ∧
    hsame (morphismMap (BHist.e1 BHist.Empty)) (BHist.e1 BHist.Empty) ∧
      hsame (morphismMap (BHist.e1 (BHist.e1 BHist.Empty)))
        (BHist.e1 (BHist.e1 BHist.Empty))

theorem RawFunctorHomCarrier_landing_obstruction :
    RawFunctorSourceHom BHist.Empty (BHist.e1 BHist.Empty)
      (BHist.e1 (BHist.e1 BHist.Empty)) /\
      RawFunctorIdentityPreserving RawFunctorObjectMap RawFunctorMorphismMap /\
        RawFunctorCompositionPreserving RawFunctorMorphismMap /\
          (RawFunctorTargetHom (RawFunctorObjectMap BHist.Empty)
            (RawFunctorObjectMap (BHist.e1 BHist.Empty))
            (RawFunctorMorphismMap (BHist.e1 (BHist.e1 BHist.Empty))) -> False) := by
  constructor
  · exact RawFunctorSourceHom.arrow
  · constructor
    · constructor
      · exact hsame_refl BHist.Empty
      · constructor
        · exact hsame_refl (BHist.e1 BHist.Empty)
        · constructor
          · exact hsame_refl BHist.Empty
          · exact hsame_refl (BHist.e1 BHist.Empty)
    · constructor
      · constructor
        · exact hsame_refl BHist.Empty
        · constructor
          · exact hsame_refl (BHist.e1 BHist.Empty)
          · exact hsame_refl (BHist.e1 (BHist.e1 BHist.Empty))
      · intro landing
        cases landing

theorem RawFunctorTargetHom_reverse_arrow_endpoint_readback {s t : BHist} :
    RawFunctorTargetHom s t (BHist.e1 (BHist.e1 BHist.Empty)) ->
      hsame s (BHist.e1 BHist.Empty) ∧ hsame t BHist.Empty := by
  intro targetHom
  cases targetHom
  exact And.intro (hsame_refl (BHist.e1 BHist.Empty)) (hsame_refl BHist.Empty)

theorem RawFunctorSourceHom_empty_morphism_endpoint_readback {s t : BHist} :
    RawFunctorSourceHom s t BHist.Empty -> hsame s BHist.Empty ∧ hsame t BHist.Empty := by
  intro sourceHom
  cases sourceHom
  exact And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)

end BEDC.Derived.FunctorUp
