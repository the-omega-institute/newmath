import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.PreorderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def PreorderCarrier (h : BHist) : Prop :=
  UnaryHistory h

def PreorderPrefixLE (h k : BHist) : Prop :=
  ∃ tail : BHist, UnaryHistory tail ∧ Cont h tail k

def PreorderClassifierSpec (h k : BHist) : Prop :=
  hsame h k

def PreorderCarrierClassifierSpec (Carrier : BHist → Prop) (h k : BHist) : Prop :=
  Carrier h ∧ Carrier k ∧ hsame h k

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

end BEDC.Derived.PreorderUp
