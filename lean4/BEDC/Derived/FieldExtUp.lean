import BEDC.FKernel.Cont
import BEDC.Derived.FieldUp
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Cont
open BEDC.Derived.FieldUp
open BEDC.Derived.VecSpaceUp

def FieldExtSingletonCarrier (h : BHist) : Prop :=
  FieldSingletonCarrier h ∧ VecSpaceSingletonCarrier h

def FieldExtSingletonClassifier (h k : BHist) : Prop :=
  FieldSingletonClassifier h k ∧ VecSpaceSingletonClassifier h k

theorem FieldExtSingleton_embedding_obligations :
    SemanticNameCert FieldExtSingletonCarrier FieldExtSingletonCarrier
        FieldExtSingletonCarrier FieldExtSingletonClassifier ∧
      (forall {h k : BHist}, FieldExtSingletonClassifier h k ->
        FieldSingletonClassifier h k ∧ VecSpaceSingletonClassifier h k) ∧
      (forall {h k : BHist}, FieldSingletonClassifier h k -> VecSpaceSingletonClassifier h k ->
        FieldExtSingletonClassifier h k) := by
  have emptyCarrier : FieldExtSingletonCarrier BHist.Empty :=
    And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
  have semantic :
      SemanticNameCert FieldExtSingletonCarrier FieldExtSingletonCarrier
        FieldExtSingletonCarrier FieldExtSingletonClassifier := {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
      equiv_refl := by
        intro h carrier
        exact And.intro
          (And.intro carrier.left (And.intro carrier.left (hsame_refl h)))
          (And.intro carrier.right (And.intro carrier.right (hsame_refl h)))
      equiv_symm := by
        intro h k same
        exact And.intro
          (And.intro same.left.right.left
            (And.intro same.left.left (hsame_symm same.left.right.right)))
          (And.intro same.right.right.left
            (And.intro same.right.left (hsame_symm same.right.right.right)))
      equiv_trans := by
        intro h k r sameHK sameKR
        exact And.intro
          (And.intro sameHK.left.left
            (And.intro sameKR.left.right.left
              (hsame_trans sameHK.left.right.right sameKR.left.right.right)))
          (And.intro sameHK.right.left
            (And.intro sameKR.right.right.left
              (hsame_trans sameHK.right.right.right sameKR.right.right.right)))
      carrier_respects_equiv := by
        intro _h _k same _carrier
        exact And.intro same.left.right.left same.right.right.left
    }
    pattern_sound := by
      intro _h carrier
      exact carrier
    ledger_sound := by
      intro _h carrier
      exact carrier
  }
  exact And.intro semantic
    (And.intro
      (by
        intro h k classified
        exact classified)
      (by
        intro h k fieldClassified vecClassified
        exact And.intro fieldClassified vecClassified))

def FieldExtSingletonEmbedding (h : BHist) : BHist :=
  append BHist.Empty h

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

theorem FieldExtSingletonCarrier_coincidence {h : BHist} :
    FieldSingletonCarrier h ->
      FieldSingletonCarrier h ∧ VecSpaceSingletonCarrier h ∧
        FieldSingletonClassifier h BHist.Empty ∧
          VecSpaceSingletonClassifier h BHist.Empty := by
  intro carrier
  have emptyFieldCarrier : FieldSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyVecCarrier : VecSpaceSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have vecCarrier : VecSpaceSingletonCarrier h := carrier
  have fieldRow : FieldSingletonClassifier h BHist.Empty :=
    And.intro carrier (And.intro emptyFieldCarrier carrier)
  have vecRow : VecSpaceSingletonClassifier h BHist.Empty :=
    And.intro vecCarrier (And.intro emptyVecCarrier carrier)
  exact And.intro carrier (And.intro vecCarrier (And.intro fieldRow vecRow))

theorem FieldExtSingletonOperation_readback_exactness {r m : BHist} :
    FieldSingletonCarrier r -> VecSpaceSingletonCarrier m ->
      FieldSingletonClassifier FieldSingletonZero BHist.Empty ∧
        FieldSingletonClassifier FieldSingletonOne BHist.Empty ∧
          FieldSingletonClassifier (FieldSingletonAdd r m) BHist.Empty ∧
            FieldSingletonClassifier (FieldSingletonNeg r) BHist.Empty ∧
              FieldSingletonClassifier (FieldSingletonMul r m) BHist.Empty ∧
                VecSpaceSingletonClassifier (VecSpaceSingletonSmul r m) BHist.Empty ∧
                  FieldSingletonClassifier (FieldSingletonMul r m)
                    (VecSpaceSingletonSmul r m) := by
  intro _carrierR _carrierM
  have emptyFieldCarrier : FieldSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyVecCarrier : VecSpaceSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have fieldEmptyRow : FieldSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyFieldCarrier
      (And.intro emptyFieldCarrier (hsame_refl BHist.Empty))
  have vecEmptyRow : VecSpaceSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyVecCarrier
      (And.intro emptyVecCarrier (hsame_refl BHist.Empty))
  exact And.intro fieldEmptyRow
    (And.intro fieldEmptyRow
      (And.intro fieldEmptyRow
        (And.intro fieldEmptyRow
          (And.intro fieldEmptyRow
            (And.intro vecEmptyRow fieldEmptyRow)))))

end BEDC.Derived.FieldExtUp
