import BEDC.Derived.RealTailAgreementSealUp.TerminalRoute

namespace BEDC.Derived.RealTailAgreementSealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RealTailAgreementSealCarrier_window_agreement_determinacy
    {R S W D A H C P N leftRead rightRead leftDyadic rightDyadic agreement terminal
      altAgreement : BHist} :
    RealTailAgreementSealCarrier R S W D A H C P N ->
      RealTailAgreementSealTerminalRoute R S W D A P leftRead rightRead leftDyadic
        rightDyadic agreement terminal ->
        Cont leftDyadic A altAgreement ->
          hsame agreement altAgreement ∧ hsame agreement (append leftDyadic A) ∧
            hsame altAgreement (append leftDyadic A) ∧ Cont W D leftDyadic ∧
              Cont leftDyadic A altAgreement := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro _carrier route altAgreementRoute
  have summary :=
    RealTailAgreementSealTerminalRoute_exhaustion
      (R := R) (S := S) (W := W) (D := D) (A := A) (P := P)
      (leftRead := leftRead) (rightRead := rightRead) (leftDyadic := leftDyadic)
      (rightDyadic := rightDyadic) (agreement := agreement) (terminal := terminal) route
  have leftDyadicRoute : Cont W D leftDyadic :=
    summary.right.right.right.right.left
  have agreementRoute : Cont leftDyadic A agreement :=
    summary.right.right.right.right.right.right.left
  have sameAgreementAlt : hsame agreement altAgreement :=
    cont_deterministic agreementRoute altAgreementRoute
  have agreementSameAppend : hsame agreement (append leftDyadic A) :=
    summary.right.right.right.right.right.right.right.right
  have altSameAppend : hsame altAgreement (append leftDyadic A) :=
    hsame_trans (hsame_symm sameAgreementAlt) agreementSameAppend
  exact
    ⟨sameAgreementAlt, agreementSameAppend, altSameAppend, leftDyadicRoute,
      altAgreementRoute⟩

end BEDC.Derived.RealTailAgreementSealUp
