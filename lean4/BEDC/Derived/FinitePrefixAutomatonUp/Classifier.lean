import BEDC.Derived.FinitePrefixAutomatonUp.TasteGate

namespace BEDC.Derived.FinitePrefixAutomatonUp

open BEDC.FKernel.Hist

def FinitePrefixAutomatonClassifier
    (Q q0 A T W R E H C P N Q' q0' A' T' W' R' E' H' C' P' N' : BHist) : Prop :=
  hsame Q Q' ∧ hsame q0 q0' ∧ hsame A A' ∧ hsame T T' ∧ hsame W W' ∧
    hsame R R' ∧ hsame E E' ∧ hsame H H' ∧ hsame C C' ∧ hsame P P' ∧
      hsame N N'

end BEDC.Derived.FinitePrefixAutomatonUp
