import BEDC.Derived.CommRingUp
import BEDC.Derived.IdealUp

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

theorem DedekindSingleton_source_obligation :
    (exists h : BHist, CommRingSingletonCarrier h ∧
      CommRingSingletonClassifier h BHist.Empty) ∧
      (forall {h k : BHist}, CommRingSingletonClassifier h k ->
        CommRingSingletonCarrier h ∧ CommRingSingletonCarrier k ∧ hsame h k) ∧
      (forall {h : BHist}, CommRingSingletonCarrier h ->
        CommRingSingletonClassifier h BHist.Empty) ∧
      (forall {h k r : BHist}, CommRingSingletonClassifier h k ->
        CommRingSingletonClassifier k r -> CommRingSingletonClassifier h r) := by
  have emptyCarrier : CommRingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : CommRingSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  constructor
  · exact Exists.intro BHist.Empty (And.intro emptyCarrier emptyClassified)
  · constructor
    · intro h k classified
      exact classified
    · constructor
      · intro h carrier
        exact And.intro carrier (And.intro emptyCarrier carrier)
      · intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))

theorem DedekindSingleton_classifier_ledger_obligation :
    SemanticNameCert CommRingSingletonCarrier CommRingSingletonCarrier
      CommRingSingletonCarrier CommRingSingletonClassifier ∧
      (exists h : BHist, CommRingSingletonCarrier h) ∧
      (forall {h k : BHist}, CommRingSingletonClassifier h k -> hsame h k) ∧
      (forall {h : BHist}, CommRingSingletonCarrier h -> hsame h BHist.Empty) := by
  have commRingCert :
      SemanticNameCert CommRingSingletonCarrier CommRingSingletonCarrier
        CommRingSingletonCarrier CommRingSingletonClassifier :=
    singleton_empty_history_commring_laws.left
  have emptyCarrier : CommRingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  constructor
  · exact commRingCert
  · constructor
    · exact Exists.intro BHist.Empty emptyCarrier
    · constructor
      · intro h k classified
        exact classified.right.right
      · intro h carrier
        exact carrier

theorem DedekindSingleton_certificate_stability_rows :
    (forall {h k : BHist}, CommRingSingletonCarrier h -> CommRingSingletonClassifier h k ->
      CommRingSingletonCarrier k ∧ CommRingSingletonClassifier k BHist.Empty ∧ hsame h k) ∧
    (forall {x y : BHist}, CommRingSingletonCarrier x -> CommRingSingletonCarrier y ->
      CommRingSingletonClassifier (CommRingSingletonAdd x y) BHist.Empty ∧
        CommRingSingletonClassifier (CommRingSingletonNeg x) BHist.Empty ∧
        CommRingSingletonClassifier (CommRingSingletonMul x y) BHist.Empty) := by
  have commRingRows := singleton_empty_history_commring_laws
  have emptyCarrier : CommRingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  constructor
  · intro h k _carrierH classifiedHK
    have carrierK : CommRingSingletonCarrier k := classifiedHK.right.left
    have classifiedKEmpty : CommRingSingletonClassifier k BHist.Empty :=
      And.intro carrierK (And.intro emptyCarrier carrierK)
    exact And.intro carrierK (And.intro classifiedKEmpty classifiedHK.right.right)
  · intro x y carrierX carrierY
    exact And.intro (commRingRows.right.left carrierX carrierY)
      (And.intro (commRingRows.right.right.left carrierX)
        (commRingRows.right.right.right.left carrierX carrierY))

theorem DedekindSingleton_scoped_certificate_packet :
    (SemanticNameCert CommRingSingletonCarrier CommRingSingletonCarrier CommRingSingletonCarrier
      CommRingSingletonClassifier) ∧
      (∃ h : BHist, CommRingSingletonCarrier h ∧
        CommRingSingletonClassifier h BHist.Empty) ∧
      (∀ {h k : BHist}, CommRingSingletonClassifier h k ->
        hsame h BHist.Empty ∧ hsame k BHist.Empty ∧ hsame h k) ∧
      (∀ {h : BHist}, CommRingSingletonCarrier h ->
        hsame (CommRingSingletonMul h BHist.Empty) BHist.Empty ∧
          hsame (CommRingSingletonMul BHist.Empty h) BHist.Empty) ∧
      (∀ {h k : BHist}, CommRingSingletonClassifier h k ->
        CommRingSingletonClassifier (CommRingSingletonAdd h k) BHist.Empty) := by
  have singletonLaws := singleton_empty_history_commring_laws
  have sourceRows := DedekindSingleton_source_obligation
  constructor
  · exact singletonLaws.left
  · constructor
    · exact sourceRows.left
    · constructor
      · intro h k classified
        exact And.intro classified.left
          (And.intro classified.right.left classified.right.right)
      · constructor
        · intro h _carrier
          exact And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
        · intro h k classified
          exact singletonLaws.right.left classified.left classified.right.left

theorem DedekindSingleton_exact_ledger_public_surface :
    SemanticNameCert CommRingSingletonCarrier CommRingSingletonCarrier CommRingSingletonCarrier
      CommRingSingletonClassifier ∧
      (exists h : BHist, CommRingSingletonCarrier h ∧
        CommRingSingletonClassifier h BHist.Empty) ∧
      ((forall {x : BHist},
        CommRingSingletonCarrier x ∧ CommRingSingletonCarrier x ->
          CommRingSingletonCarrier x) ∧
        (CommRingSingletonCarrier BHist.Empty ∧ CommRingSingletonCarrier BHist.Empty) ∧
        (forall {x y : BHist},
          CommRingSingletonCarrier x ∧ CommRingSingletonCarrier x ->
            CommRingSingletonCarrier y ∧ CommRingSingletonCarrier y ->
              CommRingSingletonCarrier (CommRingSingletonAdd x y) ∧
                CommRingSingletonCarrier (CommRingSingletonAdd x y)) ∧
        (forall {x : BHist},
          CommRingSingletonCarrier x ∧ CommRingSingletonCarrier x ->
            CommRingSingletonCarrier (CommRingSingletonNeg x) ∧
              CommRingSingletonCarrier (CommRingSingletonNeg x)) ∧
        (forall {x y : BHist},
          CommRingSingletonCarrier x ∧ CommRingSingletonCarrier x ->
            CommRingSingletonCarrier y ∧ CommRingSingletonCarrier y ->
              CommRingSingletonCarrier (CommRingSingletonMul x y) ∧
                CommRingSingletonCarrier (CommRingSingletonMul x y)) ∧
        (forall {x y : BHist},
          CommRingSingletonCarrier x ∧ CommRingSingletonCarrier x ->
            CommRingSingletonClassifier x y ->
              CommRingSingletonCarrier y ∧ CommRingSingletonCarrier y) ∧
        (forall {r x : BHist},
          CommRingSingletonCarrier r ->
            CommRingSingletonCarrier x ∧ CommRingSingletonCarrier x ->
              (CommRingSingletonCarrier (CommRingSingletonMul r x) ∧
                  CommRingSingletonCarrier (CommRingSingletonMul r x)) ∧
                (CommRingSingletonCarrier (CommRingSingletonMul x r) ∧
                  CommRingSingletonCarrier (CommRingSingletonMul x r)))) ∧
      (forall {h k : BHist}, CommRingSingletonClassifier h k -> hsame h k) ∧
      (forall {h : BHist}, CommRingSingletonCarrier h -> hsame h BHist.Empty) := by
  have ledgerRows := DedekindSingleton_classifier_ledger_obligation
  have emptyCarrier : CommRingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : CommRingSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  have meetRows :
      (forall {x : BHist},
        CommRingSingletonCarrier x ∧ CommRingSingletonCarrier x ->
          CommRingSingletonCarrier x) ∧
        (CommRingSingletonCarrier BHist.Empty ∧ CommRingSingletonCarrier BHist.Empty) ∧
        (forall {x y : BHist},
          CommRingSingletonCarrier x ∧ CommRingSingletonCarrier x ->
            CommRingSingletonCarrier y ∧ CommRingSingletonCarrier y ->
              CommRingSingletonCarrier (CommRingSingletonAdd x y) ∧
                CommRingSingletonCarrier (CommRingSingletonAdd x y)) ∧
        (forall {x : BHist},
          CommRingSingletonCarrier x ∧ CommRingSingletonCarrier x ->
            CommRingSingletonCarrier (CommRingSingletonNeg x) ∧
              CommRingSingletonCarrier (CommRingSingletonNeg x)) ∧
        (forall {x y : BHist},
          CommRingSingletonCarrier x ∧ CommRingSingletonCarrier x ->
            CommRingSingletonCarrier y ∧ CommRingSingletonCarrier y ->
              CommRingSingletonCarrier (CommRingSingletonMul x y) ∧
                CommRingSingletonCarrier (CommRingSingletonMul x y)) ∧
        (forall {x y : BHist},
          CommRingSingletonCarrier x ∧ CommRingSingletonCarrier x ->
            CommRingSingletonClassifier x y ->
              CommRingSingletonCarrier y ∧ CommRingSingletonCarrier y) ∧
        (forall {r x : BHist},
          CommRingSingletonCarrier r ->
            CommRingSingletonCarrier x ∧ CommRingSingletonCarrier x ->
              (CommRingSingletonCarrier (CommRingSingletonMul r x) ∧
                  CommRingSingletonCarrier (CommRingSingletonMul r x)) ∧
                (CommRingSingletonCarrier (CommRingSingletonMul x r) ∧
                  CommRingSingletonCarrier (CommRingSingletonMul x r))) :=
    BEDC.Derived.IdealUp.IdealIntersection_closure_rows
      (Carrier := CommRingSingletonCarrier)
      (I := CommRingSingletonCarrier)
      (J := CommRingSingletonCarrier)
      (Classifier := CommRingSingletonClassifier)
      (zero := BHist.Empty)
      (add := CommRingSingletonAdd)
      (mul := CommRingSingletonMul)
      (neg := CommRingSingletonNeg)
      ledgerRows.left.core
      emptyCarrier
      (by
        intro x y _carrierX _carrierY
        exact emptyCarrier)
      (by
        intro x _carrierX
        exact emptyCarrier)
      (by
        intro x y _carrierX _carrierY
        exact emptyCarrier)
      (by
        intro x carrierX
        exact carrierX)
      emptyCarrier
      (by
        intro x y _carrierX _carrierY
        exact emptyCarrier)
      (by
        intro x _carrierX
        exact emptyCarrier)
      (by
        intro x y _carrierX _carrierY
        exact emptyCarrier)
      (by
        intro x y _carrierX classified
        exact classified.right.left)
      (by
        intro r x _carrierR _carrierX
        exact And.intro emptyCarrier emptyCarrier)
      (by
        intro x carrierX
        exact carrierX)
      emptyCarrier
      (by
        intro x y _carrierX _carrierY
        exact emptyCarrier)
      (by
        intro x _carrierX
        exact emptyCarrier)
      (by
        intro x y _carrierX _carrierY
        exact emptyCarrier)
      (by
        intro x y _carrierX classified
        exact classified.right.left)
      (by
        intro r x _carrierR _carrierX
        exact And.intro emptyCarrier emptyCarrier)
  exact And.intro ledgerRows.left
    (And.intro (Exists.intro BHist.Empty (And.intro emptyCarrier emptyClassified))
      (And.intro meetRows (And.intro ledgerRows.right.right.left ledgerRows.right.right.right)))

end BEDC.Derived.DedekindUp
