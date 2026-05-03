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

end BEDC.Derived.ComplexDiffUp
