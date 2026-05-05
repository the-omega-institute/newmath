import BEDC.FKernel.Hist
import BEDC.FKernel.Bundle

namespace BEDC.Derived.FinsetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Bundle

def FinsetEnumerationBundle (A : BHist -> Prop) : ProbeBundle BHist -> Prop
  | ProbeBundle.Bnil => hsame BHist.Empty BHist.Empty
  | ProbeBundle.Bcons x xs => A x ∧ FinsetEnumerationBundle A xs

theorem FinsetEnumerationBundle_member_source_carried {A : BHist -> Prop} {x : BHist}
    {xs : ProbeBundle BHist} :
    FinsetEnumerationBundle A xs -> InBundle x xs -> A x := by
  intro spine member
  induction xs with
  | Bnil =>
      cases member
  | Bcons y ys ih =>
      cases spine with
      | intro sourceY spineYS =>
          cases member with
          | inl same =>
              cases same
              exact sourceY
          | inr tailMember =>
              exact ih spineYS tailMember

end BEDC.Derived.FinsetUp
