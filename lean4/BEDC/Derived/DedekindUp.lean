import BEDC.Derived.CommRingUp

namespace BEDC.Derived.DedekindUp

open BEDC.Derived.CommRingUp
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DedekindSingleton_shared_source_obligation :
    SemanticNameCert CommRingSingletonCarrier CommRingSingletonCarrier
      CommRingSingletonCarrier CommRingSingletonClassifier ∧
      ((forall {x : BHist},
        CommRingSingletonCarrier x ∧ CommRingSingletonClassifier x BHist.Empty ->
          CommRingSingletonCarrier x) ∧
        (CommRingSingletonCarrier BHist.Empty ∧
          CommRingSingletonClassifier BHist.Empty BHist.Empty) ∧
        (forall {x y : BHist},
          CommRingSingletonCarrier x ∧ CommRingSingletonClassifier x BHist.Empty ->
            CommRingSingletonCarrier y ∧ CommRingSingletonClassifier y BHist.Empty ->
              CommRingSingletonCarrier (CommRingSingletonAdd x y) ∧
                CommRingSingletonClassifier (CommRingSingletonAdd x y) BHist.Empty) ∧
        (forall {x : BHist},
          CommRingSingletonCarrier x ∧ CommRingSingletonClassifier x BHist.Empty ->
            CommRingSingletonCarrier (CommRingSingletonNeg x) ∧
              CommRingSingletonClassifier (CommRingSingletonNeg x) BHist.Empty) ∧
        (forall {x y : BHist},
          CommRingSingletonCarrier x ∧ CommRingSingletonClassifier x BHist.Empty ->
            CommRingSingletonCarrier y ∧ CommRingSingletonClassifier y BHist.Empty ->
              CommRingSingletonCarrier (CommRingSingletonMul x y) ∧
                CommRingSingletonClassifier (CommRingSingletonMul x y) BHist.Empty)) := by
  have emptyCarrier : CommRingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : CommRingSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
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
            (And.intro sameKR.right.left
              (hsame_trans sameHK.right.right sameKR.right.right))
        carrier_respects_equiv := by
          intro h k same _carrier
          exact same.right.left
      }
      pattern_sound := by
        intro h carrier
        exact carrier
      ledger_sound := by
        intro h carrier
        exact carrier
    }
  · constructor
    · intro x sourceRow
      exact sourceRow.left
    · constructor
      · exact And.intro emptyCarrier emptyClassified
      · constructor
        · intro x y _sourceX _sourceY
          exact And.intro emptyCarrier emptyClassified
        · constructor
          · intro x _sourceX
            exact And.intro emptyCarrier emptyClassified
          · intro x y _sourceX _sourceY
            exact And.intro emptyCarrier emptyClassified

theorem DedekindSingleton_domain_law_obligation :
    (forall {x : BHist}, CommRingSingletonCarrier x ->
      CommRingSingletonClassifier x BHist.Empty) ∧
      (forall {x y : BHist}, CommRingSingletonCarrier x -> CommRingSingletonCarrier y ->
        CommRingSingletonClassifier (CommRingSingletonAdd x y) BHist.Empty ∧
          CommRingSingletonClassifier (CommRingSingletonNeg x) BHist.Empty ∧
          CommRingSingletonClassifier (CommRingSingletonMul x y) BHist.Empty) ∧
      (forall {p i : BHist}, CommRingSingletonCarrier p -> CommRingSingletonCarrier i ->
        CommRingSingletonClassifier (CommRingSingletonMul p i) BHist.Empty ∧
          CommRingSingletonClassifier (CommRingSingletonMul i p) BHist.Empty) := by
  have emptyCarrier : CommRingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : CommRingSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  constructor
  · intro x carrierX
    exact And.intro carrierX (And.intro emptyCarrier carrierX)
  · constructor
    · intro x y _carrierX _carrierY
      exact And.intro emptyClassified (And.intro emptyClassified emptyClassified)
    · intro p i _carrierP _carrierI
      exact And.intro emptyClassified emptyClassified

end BEDC.Derived.DedekindUp
