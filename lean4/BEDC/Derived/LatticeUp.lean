import BEDC.Derived.PreorderUp

namespace BEDC.Derived.LatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.PreorderUp

def LatticeSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def LatticeSingletonClassifier (h k : BHist) : Prop :=
  LatticeSingletonCarrier h ∧ LatticeSingletonCarrier k ∧ hsame h k

def LatticeSingletonLE (h k : BHist) : Prop :=
  LatticeSingletonCarrier h ∧ LatticeSingletonCarrier k ∧ PreorderPrefixLE h k

def LatticeSingletonMeet (_h _k : BHist) : BHist :=
  BHist.Empty

def LatticeSingletonJoin (_h _k : BHist) : BHist :=
  BHist.Empty

theorem LatticeSingletonPrefix_laws :
    SemanticNameCert LatticeSingletonCarrier LatticeSingletonCarrier LatticeSingletonCarrier
        LatticeSingletonClassifier ∧
      (forall {h k : BHist}, LatticeSingletonCarrier h -> LatticeSingletonCarrier k ->
        LatticeSingletonCarrier (LatticeSingletonMeet h k) ∧
          LatticeSingletonCarrier (LatticeSingletonJoin h k)) ∧
      (forall {h k : BHist}, LatticeSingletonCarrier h -> LatticeSingletonCarrier k ->
        LatticeSingletonLE (LatticeSingletonMeet h k) h ∧
          LatticeSingletonLE (LatticeSingletonMeet h k) k ∧
          LatticeSingletonLE h (LatticeSingletonJoin h k) ∧
          LatticeSingletonLE k (LatticeSingletonJoin h k)) ∧
      (forall {h k z : BHist}, LatticeSingletonCarrier h -> LatticeSingletonCarrier k ->
        LatticeSingletonCarrier z -> LatticeSingletonLE z h -> LatticeSingletonLE z k ->
          LatticeSingletonLE z (LatticeSingletonMeet h k)) ∧
      (forall {h k z : BHist}, LatticeSingletonCarrier h -> LatticeSingletonCarrier k ->
        LatticeSingletonCarrier z -> LatticeSingletonLE h z -> LatticeSingletonLE k z ->
          LatticeSingletonLE (LatticeSingletonJoin h k) z) ∧
      (forall {h h' k k' : BHist}, LatticeSingletonClassifier h h' ->
        LatticeSingletonClassifier k k' ->
          LatticeSingletonClassifier (LatticeSingletonMeet h k) (LatticeSingletonMeet h' k') ∧
          LatticeSingletonClassifier (LatticeSingletonJoin h k) (LatticeSingletonJoin h' k')) := by
  have emptyCarrier : LatticeSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : LatticeSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  have leEmptyLeft :
      forall {h : BHist}, LatticeSingletonCarrier h -> LatticeSingletonLE BHist.Empty h := by
    intro h carrierH
    exact And.intro emptyCarrier
      (And.intro carrierH (PreorderPrefixLE_of_hsame (hsame_symm carrierH)))
  have leEmptyRight :
      forall {h : BHist}, LatticeSingletonCarrier h -> LatticeSingletonLE h BHist.Empty := by
    intro h carrierH
    exact And.intro carrierH (And.intro emptyCarrier (PreorderPrefixLE_of_hsame carrierH))
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
    · intro h k _carrierH _carrierK
      exact And.intro emptyCarrier emptyCarrier
    · constructor
      · intro h k carrierH carrierK
        exact And.intro (leEmptyLeft carrierH)
          (And.intro (leEmptyLeft carrierK)
            (And.intro (leEmptyRight carrierH) (leEmptyRight carrierK)))
      · constructor
        · intro h k z _carrierH _carrierK carrierZ _leZH _leZK
          exact leEmptyRight carrierZ
        · constructor
          · intro h k z _carrierH _carrierK carrierZ _leHZ _leKZ
            exact leEmptyLeft carrierZ
          · intro h h' k k' _sameHH' _sameKK'
            exact And.intro emptyClassified emptyClassified

theorem LatticeSingletonLE_empty_endpoints_iff {h k : BHist} :
    LatticeSingletonLE h k ↔ hsame h BHist.Empty ∧ hsame k BHist.Empty := by
  constructor
  · intro leData
    exact ⟨leData.left, leData.right.left⟩
  · intro endpoints
    cases endpoints with
    | intro hEmpty kEmpty =>
        exact
          ⟨hEmpty, kEmpty, PreorderPrefixLE_of_hsame (hsame_trans hEmpty (hsame_symm kEmpty))⟩

theorem LatticeSingletonCarrier_order_collapse {h k : BHist} :
    LatticeSingletonCarrier h -> LatticeSingletonCarrier k ->
      LatticeSingletonLE h k ∧ LatticeSingletonLE k h ∧ LatticeSingletonClassifier h k ∧
        hsame h BHist.Empty ∧ hsame k BHist.Empty := by
  intro hCarrier kCarrier
  have sameHK : hsame h k := hsame_trans hCarrier (hsame_symm kCarrier)
  have sameKH : hsame k h := hsame_symm sameHK
  constructor
  · exact And.intro hCarrier (And.intro kCarrier (PreorderPrefixLE_of_hsame sameHK))
  · constructor
    · exact And.intro kCarrier (And.intro hCarrier (PreorderPrefixLE_of_hsame sameKH))
    · constructor
      · exact And.intro hCarrier (And.intro kCarrier sameHK)
      · exact And.intro hCarrier kCarrier

theorem LatticeSingletonLE_antisymm_classifier {h k : BHist} :
    LatticeSingletonLE h k -> LatticeSingletonLE k h ->
      LatticeSingletonClassifier h k ∧ hsame h BHist.Empty ∧ hsame k BHist.Empty := by
  intro forward backward
  have endpoints : hsame h BHist.Empty ∧ hsame k BHist.Empty :=
    LatticeSingletonLE_empty_endpoints_iff.mp forward
  have sameHK : hsame h k :=
    PreorderPrefixLE_antisymm_hsame forward.right.right backward.right.right
  exact ⟨⟨endpoints.left, endpoints.right, sameHK⟩, endpoints.left, endpoints.right⟩

theorem LatticeSingletonMeetJoin_absorption_classifier {h k : BHist} :
    LatticeSingletonCarrier h -> LatticeSingletonCarrier k ->
      LatticeSingletonClassifier (LatticeSingletonMeet h (LatticeSingletonJoin h k)) h ∧
        LatticeSingletonClassifier (LatticeSingletonJoin h (LatticeSingletonMeet h k)) h ∧
          hsame (LatticeSingletonMeet h (LatticeSingletonJoin h k)) BHist.Empty ∧
            hsame (LatticeSingletonJoin h (LatticeSingletonMeet h k)) BHist.Empty := by
  intro hCarrier _kCarrier
  have meetCarrier :
      LatticeSingletonCarrier (LatticeSingletonMeet h (LatticeSingletonJoin h k)) :=
    hsame_refl BHist.Empty
  have joinCarrier :
      LatticeSingletonCarrier (LatticeSingletonJoin h (LatticeSingletonMeet h k)) :=
    hsame_refl BHist.Empty
  have meetSameH : hsame (LatticeSingletonMeet h (LatticeSingletonJoin h k)) h :=
    hsame_symm hCarrier
  have joinSameH : hsame (LatticeSingletonJoin h (LatticeSingletonMeet h k)) h :=
    hsame_symm hCarrier
  exact
    ⟨⟨meetCarrier, hCarrier, meetSameH⟩,
      ⟨⟨joinCarrier, hCarrier, joinSameH⟩, meetCarrier, joinCarrier⟩⟩

theorem LatticeSingletonMeetJoin_absorption_empty_classified {h k : BHist} :
    LatticeSingletonCarrier h -> LatticeSingletonCarrier k ->
      hsame (LatticeSingletonMeet h (LatticeSingletonJoin h k)) BHist.Empty ∧
      hsame (LatticeSingletonJoin h (LatticeSingletonMeet h k)) BHist.Empty ∧
      LatticeSingletonClassifier (LatticeSingletonMeet h (LatticeSingletonJoin h k)) h ∧
      LatticeSingletonClassifier (LatticeSingletonJoin h (LatticeSingletonMeet h k)) h := by
  intro carrierH _carrierK
  have emptyCarrier : LatticeSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyToH : hsame BHist.Empty h := hsame_symm carrierH
  constructor
  · exact emptyCarrier
  · constructor
    · exact emptyCarrier
    · constructor
      · exact And.intro emptyCarrier (And.intro carrierH emptyToH)
      · exact And.intro emptyCarrier (And.intro carrierH emptyToH)

end BEDC.Derived.LatticeUp
