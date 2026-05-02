import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolynomialUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def PolynomialSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def PolynomialSingletonClassifier (h k : BHist) : Prop :=
  PolynomialSingletonCarrier h ∧ PolynomialSingletonCarrier k ∧ hsame h k

def PolynomialSingletonZero : BHist :=
  BHist.Empty

def PolynomialSingletonOne : BHist :=
  BHist.Empty

def PolynomialSingletonNormalize (_P : BHist) : BHist :=
  BHist.Empty

def PolynomialSingletonAdd (P Q : BHist) : BHist :=
  append P Q

def PolynomialSingletonMul (P Q : BHist) : BHist :=
  append P Q

theorem singleton_empty_history_polynomial_laws :
    SemanticNameCert PolynomialSingletonCarrier PolynomialSingletonCarrier
      PolynomialSingletonCarrier PolynomialSingletonClassifier ∧
      PolynomialSingletonCarrier PolynomialSingletonZero ∧
      PolynomialSingletonCarrier PolynomialSingletonOne ∧
      (forall {P : BHist}, PolynomialSingletonCarrier P ->
        PolynomialSingletonClassifier
          (PolynomialSingletonNormalize (PolynomialSingletonNormalize P))
          (PolynomialSingletonNormalize P)) ∧
      (forall {P Q : BHist}, PolynomialSingletonCarrier P -> PolynomialSingletonCarrier Q ->
        PolynomialSingletonCarrier (PolynomialSingletonAdd P Q) ∧
          PolynomialSingletonCarrier (PolynomialSingletonMul P Q)) ∧
      (forall {P : BHist}, PolynomialSingletonCarrier P ->
        PolynomialSingletonClassifier (PolynomialSingletonAdd PolynomialSingletonZero P) P ∧
          PolynomialSingletonClassifier (PolynomialSingletonAdd P PolynomialSingletonZero) P ∧
          PolynomialSingletonClassifier (PolynomialSingletonMul PolynomialSingletonOne P) P ∧
          PolynomialSingletonClassifier (PolynomialSingletonMul P PolynomialSingletonOne) P) ∧
      (forall {P Q R : BHist}, PolynomialSingletonCarrier P ->
        PolynomialSingletonCarrier Q -> PolynomialSingletonCarrier R ->
          PolynomialSingletonClassifier (PolynomialSingletonAdd (PolynomialSingletonAdd P Q) R)
            (PolynomialSingletonAdd P (PolynomialSingletonAdd Q R)) ∧
            PolynomialSingletonClassifier (PolynomialSingletonMul (PolynomialSingletonMul P Q) R)
              (PolynomialSingletonMul P (PolynomialSingletonMul Q R))) := by
  have emptyCarrier : PolynomialSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : PolynomialSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  have semantic :
      SemanticNameCert PolynomialSingletonCarrier PolynomialSingletonCarrier
        PolynomialSingletonCarrier PolynomialSingletonClassifier := {
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
          (And.intro sameKR.right.left
            (hsame_trans sameHK.right.right sameKR.right.right))
      carrier_respects_equiv := by
        intro h k same _carrier
        exact same.right.left
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }
  have appendCarrier :
      forall {P Q : BHist}, PolynomialSingletonCarrier P -> PolynomialSingletonCarrier Q ->
        PolynomialSingletonCarrier (append P Q) := by
    intro P Q carrierP carrierQ
    cases carrierP
    exact hsame_trans (append_empty_left Q) carrierQ
  constructor
  · exact semantic
  · constructor
    · exact emptyCarrier
    · constructor
      · exact emptyCarrier
      · constructor
        · intro P _carrierP
          exact emptyClassified
        · constructor
          · intro P Q carrierP carrierQ
            constructor
            · exact appendCarrier carrierP carrierQ
            · exact appendCarrier carrierP carrierQ
          · constructor
            · intro P carrierP
              constructor
              · exact And.intro
                  (hsame_trans (append_empty_left P) carrierP)
                  (And.intro carrierP (append_empty_left P))
              · constructor
                · exact And.intro
                    (hsame_trans (append_empty_right P) carrierP)
                    (And.intro carrierP (append_empty_right P))
                · constructor
                  · exact And.intro
                      (hsame_trans (append_empty_left P) carrierP)
                      (And.intro carrierP (append_empty_left P))
                  · exact And.intro
                      (hsame_trans (append_empty_right P) carrierP)
                      (And.intro carrierP (append_empty_right P))
            · intro P Q R carrierP carrierQ carrierR
              have assocAdd :
                  hsame (PolynomialSingletonAdd (PolynomialSingletonAdd P Q) R)
                    (PolynomialSingletonAdd P (PolynomialSingletonAdd Q R)) :=
                append_assoc P Q R
              have assocMul :
                  hsame (PolynomialSingletonMul (PolynomialSingletonMul P Q) R)
                    (PolynomialSingletonMul P (PolynomialSingletonMul Q R)) :=
                append_assoc P Q R
              have rightCarrier :
                  PolynomialSingletonCarrier (PolynomialSingletonAdd P (PolynomialSingletonAdd Q R)) := by
                exact appendCarrier carrierP (appendCarrier carrierQ carrierR)
              constructor
              · exact And.intro (hsame_trans assocAdd rightCarrier)
                  (And.intro rightCarrier assocAdd)
              · exact And.intro (hsame_trans assocMul rightCarrier)
                  (And.intro rightCarrier assocMul)

end BEDC.Derived.PolynomialUp
