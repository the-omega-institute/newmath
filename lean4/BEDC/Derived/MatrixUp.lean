import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

def MatrixSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def MatrixSingletonClassifier (h k : BHist) : Prop :=
  MatrixSingletonCarrier h ∧ MatrixSingletonCarrier k ∧ hsame h k

def MatrixSingletonZero : BHist :=
  BHist.Empty

def MatrixSingletonOne : BHist :=
  BHist.Empty

def MatrixSingletonAdd (M N : BHist) : BHist :=
  append M N

def MatrixSingletonMul (M N : BHist) : BHist :=
  append M N

theorem MatrixSingletonClassifier_append_split_empty_iff {M N h : BHist} :
    MatrixSingletonClassifier (append M N) h ↔
      hsame M BHist.Empty ∧ hsame N BHist.Empty ∧ MatrixSingletonCarrier h := by
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    exact And.intro emptyParts.left (And.intro emptyParts.right classified.right.left)
  · intro split
    have appendEmpty : hsame (append M N) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro split.left split.right.left)
    exact And.intro appendEmpty
      (And.intro split.right.right (hsame_trans appendEmpty (hsame_symm split.right.right)))

theorem MatrixSingletonClassifier_append_visible_right_absurd {h p q : BHist} :
    (MatrixSingletonClassifier h (append p (BHist.e0 q)) -> False) ∧
      (MatrixSingletonClassifier h (append p (BHist.e1 q)) -> False) := by
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.right.left
    cases emptyParts.right
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.right.left
    cases emptyParts.right

theorem MatrixSingletonClassifier_append_pair_carrier_iff {M N P Q : BHist} :
    MatrixSingletonClassifier (append M N) (append P Q) ↔
      MatrixSingletonCarrier M ∧ MatrixSingletonCarrier N ∧
        MatrixSingletonCarrier P ∧ MatrixSingletonCarrier Q := by
  constructor
  · intro classified
    have leftParts := append_eq_empty_iff.mp classified.left
    have rightParts := append_eq_empty_iff.mp classified.right.left
    exact And.intro leftParts.left
      (And.intro leftParts.right (And.intro rightParts.left rightParts.right))
  · intro carriers
    have leftEmpty : hsame (append M N) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro carriers.left carriers.right.left)
    have rightEmpty : hsame (append P Q) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro carriers.right.right.left carriers.right.right.right)
    exact And.intro leftEmpty
      (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty)))

theorem MatrixSingletonClassifier_append_right_cancel_iff {P Q R : BHist} :
    MatrixSingletonClassifier (append P R) (append Q R) <->
      MatrixSingletonClassifier P Q ∧ MatrixSingletonCarrier R := by
  constructor
  · intro classified
    have leftParts := append_eq_empty_iff.mp classified.left
    have rightParts := append_eq_empty_iff.mp classified.right.left
    have baseClassified : MatrixSingletonClassifier P Q :=
      And.intro leftParts.left
        (And.intro rightParts.left (hsame_trans leftParts.left (hsame_symm rightParts.left)))
    exact And.intro baseClassified leftParts.right
  · intro data
    have carrierP : MatrixSingletonCarrier P := data.left.left
    have carrierQ : MatrixSingletonCarrier Q := data.left.right.left
    have carrierR : MatrixSingletonCarrier R := data.right
    cases carrierP
    cases carrierQ
    cases carrierR
    exact And.intro (hsame_refl BHist.Empty)
      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))

theorem MatrixSingletonEmptyHistory_laws :
    SemanticNameCert MatrixSingletonCarrier MatrixSingletonCarrier MatrixSingletonCarrier
        MatrixSingletonClassifier ∧
      MatrixSingletonCarrier MatrixSingletonZero ∧
      MatrixSingletonCarrier MatrixSingletonOne ∧
      (forall {M N : BHist}, MatrixSingletonCarrier M -> MatrixSingletonCarrier N ->
        MatrixSingletonCarrier (MatrixSingletonAdd M N) ∧
          MatrixSingletonCarrier (MatrixSingletonMul M N)) ∧
      (forall {M : BHist}, MatrixSingletonCarrier M ->
        MatrixSingletonClassifier (MatrixSingletonAdd MatrixSingletonZero M) M ∧
          MatrixSingletonClassifier (MatrixSingletonAdd M MatrixSingletonZero) M) ∧
      (forall {M : BHist}, MatrixSingletonCarrier M ->
        MatrixSingletonClassifier (MatrixSingletonMul MatrixSingletonOne M) M ∧
          MatrixSingletonClassifier (MatrixSingletonMul M MatrixSingletonOne) M) ∧
      (forall {M N P : BHist}, MatrixSingletonCarrier M -> MatrixSingletonCarrier N ->
        MatrixSingletonCarrier P ->
          MatrixSingletonClassifier (MatrixSingletonAdd (MatrixSingletonAdd M N) P)
            (MatrixSingletonAdd M (MatrixSingletonAdd N P)) ∧
          MatrixSingletonClassifier (MatrixSingletonMul (MatrixSingletonMul M N) P)
            (MatrixSingletonMul M (MatrixSingletonMul N P))) ∧
      (forall {M M' N N' : BHist}, MatrixSingletonClassifier M M' ->
        MatrixSingletonClassifier N N' ->
          MatrixSingletonClassifier (MatrixSingletonAdd M N) (MatrixSingletonAdd M' N') ∧
          MatrixSingletonClassifier (MatrixSingletonMul M N) (MatrixSingletonMul M' N')) := by
  have emptyCarrier : MatrixSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : MatrixSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  have appendCarrier :
      forall {M N : BHist}, MatrixSingletonCarrier M -> MatrixSingletonCarrier N ->
        MatrixSingletonCarrier (append M N) := by
    intro M N carrierM carrierN
    cases carrierM
    cases carrierN
    exact hsame_refl BHist.Empty
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
        equiv_refl := by
          intro h carrier
          exact And.intro carrier (And.intro carrier (hsame_refl h))
        equiv_symm := by
          intro h k same
          exact And.intro same.right.left
            (And.intro same.left (hsame_symm same.right.right))
        equiv_trans := by
          intro h k r sameHK sameKR
          exact And.intro sameHK.left
            (And.intro sameKR.right.left (hsame_trans sameHK.right.right sameKR.right.right))
        carrier_respects_equiv := by
          intro h k same _carrier
          exact same.right.left
      }
      pattern_sound := by
        intro _h carrier
        exact carrier
      ledger_sound := by
        intro _h carrier
        exact carrier
    }
  · constructor
    · exact emptyCarrier
    · constructor
      · exact emptyCarrier
      · constructor
        · intro M N carrierM carrierN
          exact And.intro (appendCarrier carrierM carrierN) (appendCarrier carrierM carrierN)
        · constructor
          · intro M carrierM
            cases carrierM
            exact And.intro emptyClassified emptyClassified
          · constructor
            · intro M carrierM
              cases carrierM
              exact And.intro emptyClassified emptyClassified
            · constructor
              · intro M N P carrierM carrierN carrierP
                cases carrierM
                cases carrierN
                cases carrierP
                exact And.intro emptyClassified emptyClassified
              · intro M M' N N' sameMM' sameNN'
                cases sameMM'.left
                cases sameMM'.right.left
                cases sameNN'.left
                cases sameNN'.right.left
                exact And.intro emptyClassified emptyClassified

theorem MatrixSingletonEmptyHistory_endpoint_exactness {M N : BHist} :
    MatrixSingletonCarrier M -> MatrixSingletonCarrier N ->
      MatrixSingletonClassifier M BHist.Empty ∧
        MatrixSingletonClassifier MatrixSingletonZero BHist.Empty ∧
          MatrixSingletonClassifier MatrixSingletonOne BHist.Empty ∧
            MatrixSingletonClassifier (MatrixSingletonAdd M N) BHist.Empty ∧
              MatrixSingletonClassifier (MatrixSingletonMul M N) BHist.Empty := by
  intro carrierM carrierN
  have emptyCarrier : MatrixSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : MatrixSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  have appendCarrier : MatrixSingletonCarrier (append M N) := by
    cases carrierM
    cases carrierN
    exact hsame_refl BHist.Empty
  have appendClassified : MatrixSingletonClassifier (append M N) BHist.Empty :=
    And.intro appendCarrier (And.intro emptyCarrier appendCarrier)
  constructor
  · exact And.intro carrierM (And.intro emptyCarrier carrierM)
  · constructor
    · exact emptyClassified
    · constructor
      · exact emptyClassified
      · exact And.intro appendClassified appendClassified

theorem MatrixSingletonEmptyHistory_endpoint_collapse {M N : BHist} :
    MatrixSingletonCarrier M -> MatrixSingletonCarrier N ->
      MatrixSingletonClassifier (MatrixSingletonAdd M N) BHist.Empty ∧
        MatrixSingletonClassifier (MatrixSingletonMul M N) BHist.Empty ∧
          MatrixSingletonClassifier (MatrixSingletonAdd M N) (MatrixSingletonMul M N) := by
  intro carrierM carrierN
  have endpointExact := MatrixSingletonEmptyHistory_endpoint_exactness carrierM carrierN
  have addClassified : MatrixSingletonClassifier (MatrixSingletonAdd M N) BHist.Empty :=
    endpointExact.right.right.right.left
  have mulClassified : MatrixSingletonClassifier (MatrixSingletonMul M N) BHist.Empty :=
    endpointExact.right.right.right.right
  have addMulClassified :
      MatrixSingletonClassifier (MatrixSingletonAdd M N) (MatrixSingletonMul M N) :=
    And.intro addClassified.left
      (And.intro mulClassified.left (hsame_refl (MatrixSingletonAdd M N)))
  exact And.intro addClassified (And.intro mulClassified addMulClassified)

theorem MatrixSingletonAddMul_classifier_iff {M N : BHist} :
    MatrixSingletonClassifier (MatrixSingletonAdd M N) (MatrixSingletonMul M N) <->
      hsame M BHist.Empty ∧ hsame N BHist.Empty := by
  constructor
  · intro classified
    exact append_eq_empty_iff.mp classified.left
  · intro emptyParts
    have appendEmpty : MatrixSingletonCarrier (append M N) :=
      append_eq_empty_iff.mpr emptyParts
    exact And.intro appendEmpty
      (And.intro appendEmpty (hsame_refl (MatrixSingletonAdd M N)))

theorem MatrixSingletonClassifier_continuation_comm_closed {M N left right : BHist} :
    MatrixSingletonCarrier M -> MatrixSingletonCarrier N -> Cont M N left -> Cont N M right ->
      MatrixSingletonCarrier left ∧ MatrixSingletonCarrier right ∧
        MatrixSingletonClassifier left right := by
  intro carrierM carrierN leftCont rightCont
  cases carrierM
  cases carrierN
  cases leftCont
  cases rightCont
  have emptyCarrier : MatrixSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  exact And.intro emptyCarrier
    (And.intro emptyCarrier
      (And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))))

end BEDC.Derived.MatrixUp
