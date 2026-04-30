import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History
import BEDC.FKernel.Hist

namespace BEDC.Derived.PreorderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def PreorderCarrier (h : BHist) : Prop :=
  UnaryHistory h

def PreorderPrefixLE (h k : BHist) : Prop :=
  ∃ tail : BHist, UnaryHistory tail ∧ Cont h tail k

theorem PreorderPrefixLE_of_hsame {h k : BHist} :
    hsame h k -> PreorderPrefixLE h k := by
  intro same
  cases same
  exact ⟨BHist.Empty, unary_empty, cont_right_unit h⟩

theorem PreorderPrefixLE_empty_left_iff_unary {h : BHist} :
    PreorderPrefixLE BHist.Empty h ↔ PreorderCarrier h := by
  constructor
  · intro prefixWitness
    cases prefixWitness with
    | intro tail data =>
        cases data with
        | intro tailUnary cont =>
            exact unary_transport tailUnary (hsame_symm (cont_left_unit_result cont))
  · intro carrier
    exact Exists.intro h (And.intro carrier (cont_left_unit h))

theorem PreorderPrefixLE_empty_target_iff {h : BHist} :
    PreorderPrefixLE h BHist.Empty ↔ hsame h BHist.Empty := by
  constructor
  · intro prefixWitness
    cases prefixWitness with
    | intro tail data =>
        cases data with
        | intro _tailUnary cont =>
            have emptyParts := cont_empty_result_inversion cont
            cases emptyParts.left
            exact hsame_refl BHist.Empty
  · intro same
    cases same
    exact ⟨BHist.Empty, unary_empty, cont_right_unit BHist.Empty⟩

theorem PreorderPrefixLE_target_carrier {h k : BHist} :
    PreorderCarrier h -> PreorderPrefixLE h k -> PreorderCarrier k := by
  intro carrier prefixWitness
  cases prefixWitness with
  | intro tail data =>
      cases data with
      | intro tailUnary cont =>
          exact unary_cont_closed carrier tailUnary cont

theorem PreorderPrefixLE_result_carrier {h k : BHist} :
    PreorderCarrier h -> PreorderPrefixLE h k -> PreorderCarrier k := by
  intro hCarrier prefixLE
  cases prefixLE with
  | intro tail tailData =>
      cases tailData with
      | intro tailCarrier cont =>
          exact unary_cont_closed hCarrier tailCarrier cont

def PreorderClassifierSpec (h k : BHist) : Prop :=
  hsame h k

def PreorderCarrierClassifierSpec (Carrier : BHist → Prop) (h k : BHist) : Prop :=
  Carrier h ∧ Carrier k ∧ hsame h k

theorem PreorderPrefixLE_right_extension {h k tail result : BEDC.FKernel.Hist.BHist} :
    PreorderPrefixLE h k -> BEDC.FKernel.Unary.UnaryHistory tail ->
      BEDC.FKernel.Cont.Cont k tail result -> PreorderPrefixLE h result := by
  intro prefixLE tailUnary tailCont
  cases prefixLE with
  | intro leftTail leftData =>
      cases leftData with
      | intro leftUnary leftCont =>
          cases leftCont
          exact ⟨append leftTail tail, unary_append_closed leftUnary tailUnary,
            tailCont.trans (append_assoc h leftTail tail)⟩

theorem PreorderPrefixLE_trans {h k r : BHist} :
    PreorderPrefixLE h k -> PreorderPrefixLE k r -> PreorderPrefixLE h r := by
  intro hk kr
  cases hk with
  | intro leftTail leftData =>
      cases leftData with
      | intro leftUnary leftCont =>
          cases kr with
          | intro rightTail rightData =>
              cases rightData with
              | intro rightUnary rightCont =>
                  cases leftCont
                  exact ⟨append leftTail rightTail, unary_append_closed leftUnary rightUnary,
                    rightCont.trans (append_assoc h leftTail rightTail)⟩

theorem PreorderPrefixLE_preserves_carrier {h k : BEDC.FKernel.Hist.BHist} :
    PreorderCarrier h → PreorderPrefixLE h k → PreorderCarrier k := by
  intro hCarrier prefixWitness
  cases prefixWitness with
  | intro tail tailData =>
      cases tailData with
      | intro tailCarrier hCont =>
          exact unary_cont_closed hCarrier tailCarrier hCont

theorem PreorderPrefixLE_antisymm_hsame {h k : BHist} :
    PreorderPrefixLE h k -> PreorderPrefixLE k h -> hsame h k := by
  intro hk kh
  cases hk with
  | intro forwardTail forwardData =>
      cases forwardData with
      | intro _ forwardCont =>
          cases kh with
          | intro backwardTail backwardData =>
              cases backwardData with
              | intro _ backwardCont =>
                  cases forwardCont
                  have loop :
                      append h BHist.Empty = append h (append forwardTail backwardTail) :=
                    (cont_right_unit h).symm.trans
                      (backwardCont.trans (append_assoc h forwardTail backwardTail))
                  have emptyTail : hsame BHist.Empty (append forwardTail backwardTail) :=
                    append_left_cancel (h := h) loop
                  have forwardTailEmpty : forwardTail = BHist.Empty :=
                    (append_eq_empty_iff.mp emptyTail.symm).left
                  cases forwardTailEmpty
                  exact rfl

theorem PreorderPrefixLE_antisymm_classifier {h k : BHist} :
    PreorderPrefixLE h k -> PreorderPrefixLE k h -> PreorderClassifierSpec h k := by
  intro hk kh
  cases hk with
  | intro forwardTail forwardData =>
      cases forwardData with
      | intro _ forwardCont =>
          cases kh with
          | intro backwardTail backwardData =>
              cases backwardData with
              | intro _ backwardCont =>
                  cases forwardCont
                  have loop :
                      append h BHist.Empty = append h (append forwardTail backwardTail) :=
                    (cont_right_unit h).symm.trans
                      (backwardCont.trans (append_assoc h forwardTail backwardTail))
                  have emptyTail : hsame BHist.Empty (append forwardTail backwardTail) :=
                    append_left_cancel (h := h) loop
                  have forwardTailEmpty : forwardTail = BHist.Empty :=
                    (append_eq_empty_iff.mp emptyTail.symm).left
                  cases forwardTailEmpty
                  exact rfl

theorem PreorderPrefixLE_left_extension {x h k tail : BEDC.FKernel.Hist.BHist} :
    BEDC.FKernel.Unary.UnaryHistory tail -> BEDC.FKernel.Cont.Cont x tail h ->
      PreorderPrefixLE h k -> PreorderPrefixLE x k := by
  intro tailUnary tailCont prefixLE
  cases prefixLE with
  | intro rightTail rightData =>
      cases rightData with
      | intro rightUnary rightCont =>
          cases tailCont
          exact ⟨append tail rightTail, unary_append_closed tailUnary rightUnary,
            rightCont.trans (append_assoc x tail rightTail)⟩

theorem preorder_name_certificate (Carrier : BHist → Prop) (Le : BHist → BHist → Prop)
    (carrier_witness : ∃ h : BHist, Carrier h)
    (carrier_transport : ∀ {h k : BHist}, hsame h k → Carrier h → Carrier k)
    (le_refl : ∀ {h : BHist}, Carrier h → Le h h)
    (le_trans : ∀ {h k r : BHist}, Le h k → Le k r → Le h r) :
    NameCert Carrier (PreorderCarrierClassifierSpec Carrier) ∧
      (∀ {h : BHist}, Carrier h → Le h h) ∧
        (∀ {h k r : BHist}, Le h k → Le k r → Le h r) := by
  constructor
  · constructor
    · exact carrier_witness
    · intro h carrier
      exact ⟨carrier, carrier, hsame_refl h⟩
    · intro h k same
      exact ⟨same.right.left, same.left, hsame_symm same.right.right⟩
    · intro h k r hk kr
      exact ⟨hk.left, kr.right.left, hsame_trans hk.right.right kr.right.right⟩
    · intro h k same carrier
      exact carrier_transport same.right.right carrier
  · constructor
    · intro h carrier
      exact le_refl carrier
    · intro h k r hk kr
      exact le_trans hk kr

theorem preorder_carrier_semantic_name_certificate :
    SemanticNameCert PreorderCarrier PreorderCarrier PreorderCarrier
      (PreorderCarrierClassifierSpec PreorderCarrier) := by
  constructor
  · constructor
    · exact ⟨BHist.Empty, unary_empty⟩
    · intro h carrier
      exact ⟨carrier, carrier, hsame_refl h⟩
    · intro h k same
      exact ⟨same.right.left, same.left, hsame_symm same.right.right⟩
    · intro h k r hk kr
      exact ⟨hk.left, kr.right.left, hsame_trans hk.right.right kr.right.right⟩
    · intro h k same _
      exact same.right.left
  · intro h source
    exact source
  · intro h source
    exact source

theorem preorder_prefix_stability_certificate_fields :
    (∀ h : BHist, PreorderCarrier h → PreorderPrefixLE h h) ∧
      (∀ {h k r : BHist}, PreorderPrefixLE h k → PreorderPrefixLE k r →
        PreorderPrefixLE h r) ∧
        (∀ {h h2 k k2 : BHist}, PreorderClassifierSpec h h2 →
          PreorderClassifierSpec k k2 → PreorderPrefixLE h k →
            PreorderPrefixLE h2 k2) := by
  constructor
  · intro h _carrier
    exact ⟨BHist.Empty, unary_empty, cont_right_unit h⟩
  · constructor
    · intro h k r hk kr
      cases hk with
      | intro leftTail leftData =>
          cases leftData with
          | intro leftUnary leftCont =>
              cases kr with
              | intro rightTail rightData =>
                  cases rightData with
                  | intro rightUnary rightCont =>
                      cases leftCont
                      exact ⟨append leftTail rightTail,
                        unary_append_closed leftUnary rightUnary,
                        rightCont.trans (append_assoc h leftTail rightTail)⟩
    · intro h h2 k k2 sameH sameK hk
      cases sameH
      cases sameK
      exact hk

theorem preorder_stability_certificate_fields (leC : BHist → BHist → Prop)
    (leRefl : ∀ h : BHist, leC h h)
    (leTrans : ∀ {a b c : BHist}, leC a b → leC b c → leC a c)
    (leCongr : ∀ {a a' b b' : BHist}, hsame a a' → hsame b b' → leC a b → leC a' b') :
    (∀ h : BHist, hsame h h) ∧
      (∀ {a b c : BHist}, hsame a b → hsame b c → hsame a c) ∧
      (∀ h : BHist, leC h h) ∧
      (∀ {a b c : BHist}, leC a b → leC b c → leC a c) ∧
      (∀ {a a' b b' : BHist}, hsame a a' → hsame b b' → leC a b → leC a' b') := by
  constructor
  · exact BEDC.FKernel.Hist.hsame_refl
  · constructor
    · exact BEDC.FKernel.Hist.hsame_trans
    · constructor
      · intro h
        exact leRefl h
      · constructor
        · intro a b c hab hbc
          exact leTrans hab hbc
        · intro a a' b b' haa' hbb' hle
          exact leCongr haa' hbb' hle

end BEDC.Derived.PreorderUp
