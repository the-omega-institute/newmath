import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Unary
import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ComplexDiffUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

def CplxNonZero (h : BHist) : Prop :=
  hsame h BHist.Empty -> False

def CplxDiffQuot (f z h q : BHist) : Prop :=
  UnaryHistory f ∧ UnaryHistory z ∧ CplxNonZero h ∧ UnaryHistory q ∧ Cont f h q

theorem CplxDiffQuot_hsame_transport {f f' z z' h h' q q' : BHist} :
    hsame f f' -> hsame z z' -> hsame h h' -> hsame q q' ->
      CplxDiffQuot f z h q ->
        CplxDiffQuot f' z' h' q' ∧ UnaryHistory z' ∧ CplxNonZero h' ∧
          Cont f' h' q' := by
  intro sameF sameZ sameH sameQ quotient
  cases quotient with
  | intro functionCarrier rest =>
      cases rest with
      | intro pointCarrier rest =>
          cases rest with
          | intro stepNonzero rest =>
              cases rest with
              | intro quotientCarrier ledger =>
                  have functionCarrier' : UnaryHistory f' :=
                    unary_transport functionCarrier sameF
                  have pointCarrier' : UnaryHistory z' :=
                    unary_transport pointCarrier sameZ
                  have quotientCarrier' : UnaryHistory q' :=
                    unary_transport quotientCarrier sameQ
                  have stepNonzero' : CplxNonZero h' := by
                    intro stepEmpty
                    exact stepNonzero (hsame_trans sameH stepEmpty)
                  have ledger' : Cont f' h' q' :=
                    cont_hsame_transport sameF sameH sameQ ledger
                  exact And.intro
                    (And.intro functionCarrier'
                      (And.intro pointCarrier'
                        (And.intro stepNonzero'
                          (And.intro quotientCarrier' ledger'))))
                    (And.intro pointCarrier'
                      (And.intro stepNonzero' ledger'))

def CplxDiffQuotAppendClassifier (f : BHist -> BHist) (z h q : BHist) : Prop :=
  ComplexHistoryCarrier z ∧ CplxNonZero h ∧ ComplexHistoryCarrier q ∧
    ComplexHistoryClassifier q (f (append z h))

theorem CplxDiffQuot_append_classifier_transport {f : BHist -> BHist} {z z' h h' q : BHist} :
    CplxDiffQuotAppendClassifier f z h q -> hsame z z' -> hsame h h' -> CplxNonZero h' ->
      ComplexHistoryClassifier q (f (append z' h')) ∧
        CplxDiffQuotAppendClassifier f z' h' q := by
  intro quotient sameZ sameH targetNonzero
  cases sameZ
  cases sameH
  cases quotient with
  | intro zCarrier quotientRest =>
      cases quotientRest with
      | intro _ quotientRest =>
          cases quotientRest with
          | intro qCarrier qClass =>
              exact And.intro qClass
                (And.intro zCarrier (And.intro targetNonzero (And.intro qCarrier qClass)))

theorem CplxDiffQuot_result_not_empty {f z h q : BHist} :
    CplxDiffQuot f z h q -> hsame q BHist.Empty -> False := by
  intro quotient resultEmpty
  cases quotient with
  | intro _functionCarrier rest =>
      cases rest with
      | intro _pointCarrier rest =>
          cases rest with
          | intro stepNonzero rest =>
              cases rest with
              | intro _quotientCarrier ledger =>
                  have emptyLedger : Cont f h BHist.Empty :=
                    cont_result_hsame_transport ledger resultEmpty
                  have emptyParts := cont_empty_result_inversion emptyLedger
                  exact stepNonzero emptyParts.right

theorem CplxDiffQuotAppendClassifier_append_target_not_empty {f : BHist -> BHist}
    {z h q : BHist} :
    CplxDiffQuotAppendClassifier f z h q -> hsame (append z h) BHist.Empty -> False := by
  intro quotient appendEmpty
  cases quotient with
  | intro _zCarrier rest =>
      cases rest with
      | intro stepNonzero _rest =>
          exact stepNonzero (append_eq_empty_iff.mp appendEmpty).right

theorem CplxDiffQuot_quotient_cont_deterministic {f z h q q' : BHist} :
    CplxDiffQuot f z h q -> CplxDiffQuot f z h q' ->
      Cont f h q ∧ Cont f h q' ∧ hsame q q' := by
  intro left right
  cases left with
  | intro _functionCarrier leftRest =>
      cases leftRest with
      | intro _pointCarrier leftRest =>
          cases leftRest with
          | intro _stepNonzero leftRest =>
              cases leftRest with
              | intro _quotientCarrier leftLedger =>
                  cases right with
                  | intro _functionCarrier' rightRest =>
                      cases rightRest with
                      | intro _pointCarrier' rightRest =>
                          cases rightRest with
                          | intro _stepNonzero' rightRest =>
                              cases rightRest with
                              | intro _quotientCarrier' rightLedger =>
                                  exact And.intro leftLedger
                                    (And.intro rightLedger
                                      (cont_deterministic leftLedger rightLedger))

theorem CplxDiffQuot_empty_function_result_nonzero {z h q : BHist} :
    CplxDiffQuot BHist.Empty z h q -> CplxNonZero q := by
  intro quotient
  cases quotient with
  | intro _functionCarrier rest =>
      cases rest with
      | intro _pointCarrier rest =>
          cases rest with
          | intro stepNonzero rest =>
              cases rest with
              | intro _quotientCarrier ledger =>
                  intro quotientEmpty
                  have sameQH : hsame q h := cont_left_unit_result ledger
                  exact stepNonzero (hsame_trans (hsame_symm sameQH) quotientEmpty)

theorem CplxDiffQuot_same_result_step_deterministic {f z h h' q : BHist} :
    CplxDiffQuot f z h q -> CplxDiffQuot f z h' q ->
      hsame h h' ∧ Cont f h q ∧ Cont f h' q := by
  intro left right
  cases left with
  | intro _functionCarrier leftRest =>
      cases leftRest with
      | intro _pointCarrier leftRest =>
          cases leftRest with
          | intro _stepNonzero leftRest =>
              cases leftRest with
              | intro _quotientCarrier leftLedger =>
                  cases right with
                  | intro _functionCarrier' rightRest =>
                      cases rightRest with
                      | intro _pointCarrier' rightRest =>
                          cases rightRest with
                          | intro _stepNonzero' rightRest =>
                              cases rightRest with
                              | intro _quotientCarrier' rightLedger =>
                                  exact And.intro (cont_left_cancel leftLedger rightLedger)
                                    (And.intro leftLedger rightLedger)

theorem CplxDiffQuot_step_unary {f z h q : BHist} :
    CplxDiffQuot f z h q -> UnaryHistory h ∧ UnaryHistory q ∧ Cont f h q := by
  intro quotient
  cases quotient with
  | intro _functionCarrier rest =>
      cases rest with
      | intro _pointCarrier rest =>
          cases rest with
          | intro _stepNonzero rest =>
              cases rest with
              | intro quotientCarrier ledger =>
                  exact And.intro (unary_cont_right_factor ledger quotientCarrier)
                    (And.intro quotientCarrier ledger)

theorem CplxDiffQuot_cont_result_hsame {f z h q q' : BHist} :
    CplxDiffQuot f z h q -> Cont f h q' -> hsame q q' := by
  intro quotient continuation
  cases quotient with
  | intro _functionCarrier quotientRest =>
      cases quotientRest with
      | intro _pointCarrier quotientRest =>
          cases quotientRest with
          | intro _stepNonzero quotientRest =>
              cases quotientRest with
              | intro _quotientCarrier ledger =>
                  exact cont_deterministic ledger continuation

theorem CplxDiffQuot_point_hsame_cont_deterministic {f z z' h q q' : BHist} :
    hsame z z' -> CplxDiffQuot f z h q -> CplxDiffQuot f z' h q' ->
      Cont f h q ∧ Cont f h q' ∧ hsame q q' := by
  intro samePoint left right
  have rightAtSource : CplxDiffQuot f z h q' :=
    (CplxDiffQuot_hsame_transport (hsame_refl f) (hsame_symm samePoint)
      (hsame_refl h) (hsame_refl q') right).left
  exact CplxDiffQuot_quotient_cont_deterministic left rightAtSource

end BEDC.Derived.ComplexDiffUp
