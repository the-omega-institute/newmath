import BEDC.FKernel.NameCert

namespace BEDC.Derived.PreorderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def PreorderClassifierSpec (Carrier : BHist → Prop) (h k : BHist) : Prop :=
  Carrier h ∧ Carrier k ∧ hsame h k

theorem preorder_name_certificate (Carrier : BHist → Prop) (Le : BHist → BHist → Prop)
    (carrier_witness : ∃ h : BHist, Carrier h)
    (carrier_transport : ∀ {h k : BHist}, hsame h k → Carrier h → Carrier k)
    (le_refl : ∀ {h : BHist}, Carrier h → Le h h)
    (le_trans : ∀ {h k r : BHist}, Le h k → Le k r → Le h r) :
    NameCert Carrier (PreorderClassifierSpec Carrier) ∧
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

end BEDC.Derived.PreorderUp
