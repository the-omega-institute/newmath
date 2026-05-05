import BEDC.FKernel.Cont
import BEDC.Derived.FieldUp
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.FieldUp
open BEDC.Derived.VecSpaceUp

def FieldExtSingletonEmbedding (h : BHist) : BHist :=
  append BHist.Empty h

def FieldExtSingletonLedgerPolicy (h : BHist) : Prop :=
  FieldSingletonCarrier h ∧ VecSpaceSingletonCarrier h ∧
    FieldSingletonClassifier (FieldExtSingletonEmbedding h) (append BHist.Empty h)

theorem FieldExtSingletonLedgerPolicy_carrier_coincidence {h : BHist} :
    FieldExtSingletonLedgerPolicy h ->
      FieldSingletonCarrier h ∧ VecSpaceSingletonCarrier h ∧
        FieldSingletonClassifier (FieldExtSingletonEmbedding h) (append BHist.Empty h) := by
  intro policy
  cases policy with
  | intro fieldCarrier rest =>
      cases rest with
      | intro vecCarrier embeddedClassifier =>
          exact And.intro fieldCarrier (And.intro vecCarrier embeddedClassifier)

theorem FieldExtSingletonVectorSpace_smul_mul_compatible {r m : BHist} :
    FieldSingletonCarrier r -> VecSpaceSingletonCarrier m ->
      VecSpaceSingletonCarrier (VecSpaceSingletonSmul (FieldExtSingletonEmbedding r) m) ∧
        FieldSingletonCarrier (FieldSingletonMul (FieldExtSingletonEmbedding r) m) ∧
          hsame (VecSpaceSingletonSmul (FieldExtSingletonEmbedding r) m)
            (FieldSingletonMul (FieldExtSingletonEmbedding r) m) := by
  intro _carrierR _carrierM
  have smulCarrier :
      VecSpaceSingletonCarrier (VecSpaceSingletonSmul (FieldExtSingletonEmbedding r) m) :=
    hsame_refl BHist.Empty
  have mulCarrier :
      FieldSingletonCarrier (FieldSingletonMul (FieldExtSingletonEmbedding r) m) :=
    hsame_refl BHist.Empty
  exact And.intro smulCarrier
    (And.intro mulCarrier (hsame_refl BHist.Empty))

theorem FieldExtSingletonEmbedding_laws :
    FieldSingletonCarrier BHist.Empty ∧
      (forall {h : BHist}, FieldSingletonCarrier h ->
        FieldSingletonCarrier (FieldExtSingletonEmbedding h)) ∧
      (forall {h k : BHist}, FieldSingletonClassifier h k <->
        FieldSingletonClassifier (FieldExtSingletonEmbedding h)
          (FieldExtSingletonEmbedding k)) ∧
      FieldSingletonClassifier (FieldExtSingletonEmbedding FieldSingletonZero)
        FieldSingletonZero ∧
      FieldSingletonClassifier (FieldExtSingletonEmbedding FieldSingletonOne)
        FieldSingletonOne := by
  have emptyCarrier : FieldSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  constructor
  · exact emptyCarrier
  · constructor
    · intro h carrierH
      unfold FieldExtSingletonEmbedding
      exact hsame_trans (append_empty_left h) carrierH
    · constructor
      · intro h k
        constructor
        · intro classified
          have embeddedH : FieldSingletonCarrier (FieldExtSingletonEmbedding h) := by
            unfold FieldExtSingletonEmbedding
            exact hsame_trans (append_empty_left h) classified.left
          have embeddedK : FieldSingletonCarrier (FieldExtSingletonEmbedding k) := by
            unfold FieldExtSingletonEmbedding
            exact hsame_trans (append_empty_left k) classified.right.left
          have embeddedSame :
              hsame (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k) := by
            unfold FieldExtSingletonEmbedding
            exact hsame_trans (append_empty_left h)
              (hsame_trans classified.right.right (hsame_symm (append_empty_left k)))
          exact And.intro embeddedH (And.intro embeddedK embeddedSame)
        · intro classified
          have carrierH : FieldSingletonCarrier h := by
            unfold FieldExtSingletonEmbedding at classified
            exact hsame_trans (hsame_symm (append_empty_left h)) classified.left
          have carrierK : FieldSingletonCarrier k := by
            unfold FieldExtSingletonEmbedding at classified
            exact hsame_trans (hsame_symm (append_empty_left k)) classified.right.left
          have sameHK : hsame h k := by
            unfold FieldExtSingletonEmbedding at classified
            exact hsame_trans (hsame_symm (append_empty_left h))
              (hsame_trans classified.right.right (append_empty_left k))
          exact And.intro carrierH (And.intro carrierK sameHK)
      · constructor
        · unfold FieldExtSingletonEmbedding FieldSingletonZero FieldSingletonClassifier
          exact And.intro emptyCarrier
            (And.intro emptyCarrier (hsame_refl BHist.Empty))
        · unfold FieldExtSingletonEmbedding FieldSingletonOne FieldSingletonClassifier
          exact And.intro emptyCarrier
            (And.intro emptyCarrier (hsame_refl BHist.Empty))

end BEDC.Derived.FieldExtUp
