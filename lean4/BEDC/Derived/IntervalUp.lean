import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.IntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def IntervalCarrier (lower upper : BHist → Prop) (h : BHist) : Prop :=
  UnaryHistory h ∧ lower h ∧ upper h

def IntervalClassifierSpec (lower upper : BHist → Prop) (h k : BHist) : Prop :=
  IntervalCarrier lower upper h ∧ IntervalCarrier lower upper k ∧ hsame h k

theorem interval_name_certificate (lower upper : BHist → Prop)
    (lower_empty : lower BHist.Empty) (upper_empty : upper BHist.Empty)
    (lower_transport : ∀ {h k : BHist}, hsame h k → lower h → lower k)
    (upper_transport : ∀ {h k : BHist}, hsame h k → upper h → upper k) :
    NameCert (IntervalCarrier lower upper) (IntervalClassifierSpec lower upper) ∧
      (∀ {h k : BHist}, hsame h k → IntervalCarrier lower upper h →
        IntervalCarrier lower upper k) := by
  constructor
  · constructor
    · exact ⟨BHist.Empty, unary_empty, lower_empty, upper_empty⟩
    · intro h carrier
      exact ⟨carrier, carrier, hsame_refl h⟩
    · intro h k same
      exact ⟨same.right.left, same.left, hsame_symm same.right.right⟩
    · intro h k r hk kr
      exact ⟨hk.left, kr.right.left, hsame_trans hk.right.right kr.right.right⟩
    · intro h k same carrier
      exact ⟨unary_transport carrier.left same.right.right,
        lower_transport same.right.right carrier.right.left,
        upper_transport same.right.right carrier.right.right⟩
  · intro h k same carrier
    exact ⟨unary_transport carrier.left same,
      lower_transport same carrier.right.left,
      upper_transport same carrier.right.right⟩

end BEDC.Derived.IntervalUp
