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

theorem CplxNonZero_empty_or_nonzero {h : BHist} :
    hsame h BHist.Empty ∨ CplxNonZero h := by
  cases h with
  | Empty => exact Or.inl (hsame_refl BHist.Empty)
  | e0 p => exact Or.inr not_hsame_e0_empty
  | e1 p => exact Or.inr not_hsame_e1_empty

theorem CplxDiffQuot_visible_step_construct {f z p q out0 out1 : BHist} :
    UnaryHistory f -> UnaryHistory z -> UnaryHistory out0 -> UnaryHistory out1 ->
      Cont f (BHist.e0 p) out0 -> Cont f (BHist.e1 q) out1 ->
        CplxDiffQuot f z (BHist.e0 p) out0 ∧ CplxDiffQuot f z (BHist.e1 q) out1 := by
  intro functionCarrier pointCarrier out0Carrier out1Carrier cont0 cont1
  constructor
  · exact And.intro functionCarrier
      (And.intro pointCarrier
        (And.intro not_hsame_e0_empty (And.intro out0Carrier cont0)))
  · exact And.intro functionCarrier
      (And.intro pointCarrier
        (And.intro not_hsame_e1_empty (And.intro out1Carrier cont1)))

def CplxDiffAt (f z fp : BHist) : Prop :=
  UnaryHistory f ∧ UnaryHistory z ∧ ComplexHistoryCarrier fp ∧
    (∃ h : BHist, ∃ q : BHist, CplxDiffQuot f z h q) ∧
      (∀ {h q : BHist}, CplxDiffQuot f z h q -> hsame q fp)

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

protected theorem CplxDiffQuot_result_nonempty_from_step {f z h q : BHist} :
    CplxDiffQuot f z h q -> hsame q BHist.Empty -> False := by
  intro quotient qEmpty
  cases quotient with
  | intro _functionCarrier rest =>
      cases rest with
      | intro _pointCarrier rest =>
          cases rest with
          | intro stepNonzero rest =>
              cases rest with
              | intro _quotientCarrier ledger =>
                  have appendEmpty : hsame (append f h) BHist.Empty :=
                    hsame_trans (hsame_symm ledger) qEmpty
                  exact stepNonzero (append_eq_empty_iff.mp appendEmpty).right

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

theorem CplxDiffQuot_result_nonempty {f z h q : BHist} :
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

theorem CplxDiffQuot_result_visible_context_readback {p r f z h q core : BHist} :
    CplxDiffQuot f z h q ->
      hsame (append (append p q) r) (append (append p core) r) ->
        hsame q core ∧ (hsame core BHist.Empty -> False) := by
  intro quotient sameVisible
  have sameNested : hsame (append p (append q r)) (append p (append core r)) :=
    hsame_trans (hsame_symm (append_assoc p q r))
      (hsame_trans sameVisible (append_assoc p core r))
  have sameCore : hsame q core :=
    (append_hsame_common_context_cancel_iff (hsame_refl p) (hsame_refl r)).mp sameNested
  exact And.intro sameCore
    (fun coreEmpty =>
      CplxDiffQuot_result_nonempty quotient (hsame_trans sameCore coreEmpty))

theorem CplxDiffAt_derivative_unique {f z fp gp : BHist} :
    CplxDiffAt f z fp -> CplxDiffAt f z gp ->
      hsame fp gp ∧ ∃ h : BHist, ∃ q : BHist, CplxDiffQuot f z h q ∧ Cont f h q := by
  intro fpDiff gpDiff
  cases fpDiff with
  | intro _fpFunctionCarrier fpRest =>
      cases fpRest with
      | intro _fpPointCarrier fpRest =>
          cases fpRest with
          | intro _fpDerivativeCarrier fpRest =>
              cases fpRest with
              | intro fpWitness fpClassifier =>
                  cases fpWitness with
                  | intro h fpWitness =>
                      cases fpWitness with
                      | intro q quotient =>
                          cases gpDiff with
                          | intro _gpFunctionCarrier gpRest =>
                              cases gpRest with
                              | intro _gpPointCarrier gpRest =>
                                  cases gpRest with
                                  | intro _gpDerivativeCarrier gpRest =>
                                      cases gpRest with
                                      | intro _gpWitness gpClassifier =>
                                          have qSameFp : hsame q fp := fpClassifier quotient
                                          have qSameGp : hsame q gp := gpClassifier quotient
                                          have quotientCont : Cont f h q := by
                                            cases quotient with
                                            | intro _functionCarrier quotientRest =>
                                                cases quotientRest with
                                                | intro _pointCarrier quotientRest =>
                                                    cases quotientRest with
                                                    | intro _stepNonzero quotientRest =>
                                                        cases quotientRest with
                                                        | intro _quotientCarrier ledger =>
                                                            exact ledger
                                          exact And.intro
                                            (hsame_trans (hsame_symm qSameFp) qSameGp)
                                            (Exists.intro h
                                              (Exists.intro q (And.intro quotient quotientCont)))

end BEDC.Derived.ComplexDiffUp
