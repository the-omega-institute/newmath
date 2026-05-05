import BEDC.Derived.ComplexDiffUp

namespace BEDC.Derived.ComplexDifferentiabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp
open BEDC.Derived.ComplexDiffUp

def CplxRealProj (f u v : BHist) : Prop :=
  UnaryHistory u ∧ UnaryHistory v ∧ Cont u v f

def PartialReal (u z p : BHist) : Prop :=
  UnaryHistory u ∧ UnaryHistory z ∧ CplxDiffAt u z p

def PartialImag (u z q : BHist) : Prop :=
  UnaryHistory u ∧ UnaryHistory z ∧ CplxDiffAt u z q

def CplxDiffClassifierSpec (f z fp g w gp : BHist) : Prop :=
  CplxDiffAt f z fp ∧ CplxDiffAt g w gp ∧ hsame f g ∧ hsame z w ∧ hsame fp gp

def CplxDiffSourceSpec (f z fp : BHist) : Prop :=
  CplxDiffAt f z fp ∧
    ∃ h : BHist, ∃ q : BHist, CplxDiffQuot f z h q ∧ Cont f h q ∧ hsame q fp

def CplxDiffPatternSpec (f z pattern : BHist) : Prop :=
  ∃ h : BHist, ∃ q : BHist, CplxDiffQuot f z h q ∧ Cont h q pattern

theorem CplxDiffPatternSpec_witness_readback {f z pattern : BHist} :
    CplxDiffPatternSpec f z pattern ->
      ∃ h : BHist, ∃ q : BHist,
        CplxDiffQuot f z h q ∧ Cont h q pattern ∧ UnaryHistory h ∧ UnaryHistory q := by
  intro patternSpec
  cases patternSpec with
  | intro h patternRest =>
      cases patternRest with
      | intro q witness =>
          have quotientReadback := CplxDiffQuot_step_unary witness.left
          exact Exists.intro h
            (Exists.intro q
              (And.intro witness.left
                (And.intro witness.right
                  (And.intro quotientReadback.left quotientReadback.right.left))))

theorem CplxDiffAt_witness_step_nonzero {f z fp : BHist} :
    CplxDiffAt f z fp ->
      exists h : BHist, exists q : BHist,
        CplxNonZero h ∧ CplxDiffQuot f z h q ∧ Cont f h q ∧ hsame q fp := by
  intro diff
  cases diff with
  | intro _functionCarrier diffRest =>
      cases diffRest with
      | intro _pointCarrier diffRest =>
          cases diffRest with
          | intro _derivativeCarrier diffRest =>
              cases diffRest with
              | intro witness classifier =>
                  cases witness with
                  | intro h witnessRest =>
                      cases witnessRest with
                      | intro q quotient =>
                          cases quotient with
                          | intro functionCarrier quotientRest =>
                              cases quotientRest with
                              | intro pointCarrier quotientRest =>
                                  cases quotientRest with
                                  | intro stepNonzero quotientRest =>
                                      cases quotientRest with
                                      | intro quotientCarrier ledger =>
                                          have rebuilt : CplxDiffQuot f z h q :=
                                            And.intro functionCarrier
                                              (And.intro pointCarrier
                                                (And.intro stepNonzero
                                                  (And.intro quotientCarrier ledger)))
                                          exact Exists.intro h
                                            (Exists.intro q
                                              (And.intro stepNonzero
                                                  (And.intro rebuilt
                                                    (And.intro ledger (classifier rebuilt)))))

theorem CplxDiffSourceSpec_of_diff {f z fp : BHist} :
    CplxDiffAt f z fp -> CplxDiffSourceSpec f z fp := by
  intro diff
  cases CplxDiffAt_witness_step_nonzero diff with
  | intro h witness =>
      cases witness with
      | intro q data =>
          exact And.intro diff
            (Exists.intro h
              (Exists.intro q
                (And.intro data.right.left
                  (And.intro data.right.right.left data.right.right.right))))

theorem CplxDiffAt_witness_nonzero_unary_step {f z fp : BHist} :
    CplxDiffAt f z fp -> ∃ h : BHist, ∃ q : BHist,
      CplxNonZero h ∧ UnaryHistory h ∧ UnaryHistory q ∧ CplxDiffQuot f z h q ∧
        Cont f h q ∧ hsame q fp := by
  intro diff
  cases CplxDiffAt_witness_step_nonzero diff with
  | intro h witness =>
      cases witness with
      | intro q data =>
          cases data with
          | intro stepNonzero rest =>
              cases rest with
              | intro quotient rest =>
                  cases rest with
                  | intro ledger quotientClass =>
                      have unaryReadback := CplxDiffQuot_step_unary quotient
                      exact Exists.intro h
                        (Exists.intro q
                          (And.intro stepNonzero
                            (And.intro unaryReadback.left
                              (And.intro unaryReadback.right.left
                                (And.intro quotient
                                  (And.intro ledger quotientClass))))))

theorem CplxDiffAt_witness_nonzero_result {f z fp : BHist} :
    CplxDiffAt f z fp ->
      exists h : BHist, exists q : BHist,
        CplxDiffQuot f z h q ∧ Cont f h q ∧ CplxNonZero h ∧ CplxNonZero q ∧
          hsame q fp := by
  intro diff
  cases CplxDiffAt_witness_step_nonzero diff with
  | intro h witness =>
      cases witness with
      | intro q data =>
          cases data with
          | intro stepNonzero rest =>
              cases rest with
              | intro quotient rest =>
                  cases rest with
                  | intro ledger quotientClass =>
                      exact Exists.intro h
                        (Exists.intro q
                          (And.intro quotient
                            (And.intro ledger
                              (And.intro stepNonzero
                                (And.intro (CplxDiffQuot_result_nonempty quotient)
                                  quotientClass)))))

theorem CplxDiffAt_sum_append_derivative_carrier {f g z fp gp : BHist} :
    CplxDiffAt f z fp -> CplxDiffAt g z gp ->
      ComplexHistoryCarrier (append fp gp) ∧
        ∃ hf : BHist, ∃ qf : BHist, ∃ hg : BHist, ∃ qg : BHist,
          CplxDiffQuot f z hf qf ∧ CplxDiffQuot g z hg qg ∧
            Cont fp gp (append fp gp) := by
  intro diffF diffG
  cases diffF.right.right.right.left with
  | intro hf diffFWitness =>
      cases diffFWitness with
      | intro qf quotientF =>
          cases diffG.right.right.right.left with
          | intro hg diffGWitness =>
              cases diffGWitness with
              | intro qg quotientG =>
                  have appendCarrier : ComplexHistoryCarrier (append fp gp) :=
                    ComplexHistoryCarrier_append_unary_closed diffF.right.right.left
                      (ComplexHistoryCarrier_unary diffG.right.right.left)
                  exact And.intro appendCarrier
                    (Exists.intro hf
                      (Exists.intro qf
                        (Exists.intro hg
                          (Exists.intro qg
                            (And.intro quotientF
                              (And.intro quotientG (cont_intro rfl)))))))

theorem CplxDiffAt_scalar_append_derivative_carrier {f z fp c : BHist} :
    CplxDiffAt f z fp -> ComplexHistoryCarrier c ->
      ComplexHistoryCarrier (append c fp) ∧
        exists h : BHist, exists q : BHist,
          CplxDiffQuot f z h q ∧ Cont c q (append c q) ∧
            ComplexHistoryCarrier (append c q) := by
  intro diff carrierC
  cases diff.right.right.right.left with
  | intro h witness =>
      cases witness with
      | intro q quotient =>
          have derivativeAppendCarrier : ComplexHistoryCarrier (append c fp) :=
            ComplexHistoryCarrier_append_unary_closed carrierC
              (ComplexHistoryCarrier_unary diff.right.right.left)
          have quotientReadback := CplxDiffQuot_step_unary quotient
          have quotientAppendCarrier : ComplexHistoryCarrier (append c q) :=
            ComplexHistoryCarrier_append_unary_closed carrierC quotientReadback.right.left
          exact And.intro derivativeAppendCarrier
            (Exists.intro h
              (Exists.intro q
                (And.intro quotient
                  (And.intro (cont_intro rfl) quotientAppendCarrier))))

theorem CplxDiffAt_visible_step_branches_absurd {f z fp p q out0 out1 : BHist} :
    CplxDiffAt f z fp -> CplxDiffQuot f z (BHist.e0 p) out0 ->
      CplxDiffQuot f z (BHist.e1 q) out1 -> False := by
  intro diff leftQuot rightQuot
  cases diff with
  | intro _functionCarrier diffRest =>
      cases diffRest with
      | intro _pointCarrier diffRest =>
          cases diffRest with
          | intro _derivativeCarrier diffRest =>
              cases diffRest with
              | intro _witness classifier =>
                  have sameLeft : hsame out0 fp := classifier leftQuot
                  have sameRight : hsame out1 fp := classifier rightQuot
                  have sameRightLeft : hsame out1 out0 :=
                    hsame_trans sameRight (hsame_symm sameLeft)
                  have rightAtLeft : CplxDiffQuot f z (BHist.e1 q) out0 :=
                    (CplxDiffQuot_hsame_transport (hsame_refl f) (hsame_refl z)
                      (hsame_refl (BHist.e1 q)) sameRightLeft rightQuot).left
                  exact CplxDiffQuot_visible_step_same_result_absurd leftQuot rightAtLeft

theorem CplxDiffAt_derivative_visible_context_readback {p r f z fp core : BHist} :
    CplxDiffAt f z fp ->
      hsame (append (append p fp) r) (append (append p core) r) ->
        hsame fp core ∧ ComplexHistoryCarrier core := by
  intro diff sameVisible
  have sameNested : hsame (append p (append fp r)) (append p (append core r)) :=
    hsame_trans (hsame_symm (append_assoc p fp r))
      (hsame_trans sameVisible (append_assoc p core r))
  have sameCore : hsame fp core :=
    (append_hsame_common_context_cancel_iff (hsame_refl p) (hsame_refl r)).mp sameNested
  exact And.intro sameCore
    (BEDC.Derived.ProdUp.ProdHistoryCarrier_hsame_transport sameCore diff.right.right.left)

theorem CplxDiffAt_derivative_visible_context_nonempty_readback {p r f z fp core : BHist} :
    CplxDiffAt f z fp ->
      hsame (append (append p fp) r) (append (append p core) r) ->
        hsame fp core ∧ ComplexHistoryCarrier core ∧ (hsame core BHist.Empty -> False) := by
  intro diff sameVisible
  have readback := CplxDiffAt_derivative_visible_context_readback diff sameVisible
  cases CplxDiffAt_witness_nonzero_result diff with
  | intro h witness =>
      cases witness with
      | intro q data =>
          cases data with
          | intro _quotient rest =>
              cases rest with
              | intro _ledger rest =>
                  cases rest with
                  | intro _stepNonzero rest =>
                      cases rest with
                      | intro quotientNonzero sameQFp =>
                          exact And.intro readback.left
                            (And.intro readback.right
                              (fun coreEmpty =>
                                quotientNonzero
                                  (hsame_trans sameQFp
                                    (hsame_trans readback.left coreEmpty))))

theorem CplxDiffAt_quotient_result_visible_context_derivative_readback
    {p r f z fp h q core : BHist} :
    CplxDiffAt f z fp -> CplxDiffQuot f z h q ->
      hsame (append (append p q) r) (append (append p core) r) ->
        hsame fp core ∧ ComplexHistoryCarrier core ∧ (hsame core BHist.Empty -> False) := by
  intro diff quotient sameVisible
  have quotientReadback := CplxDiffQuot_result_visible_context_readback quotient sameVisible
  have sameQFp : hsame q fp := diff.right.right.right.right quotient
  have sameFpCore : hsame fp core :=
    hsame_trans (hsame_symm sameQFp) quotientReadback.left
  have coreCarrier : ComplexHistoryCarrier core :=
    BEDC.Derived.ProdUp.ProdHistoryCarrier_hsame_transport sameFpCore diff.right.right.left
  exact And.intro sameFpCore (And.intro coreCarrier quotientReadback.right)

theorem CplxDiffAt_empty_function_derivative_nonzero {z fp : BHist} :
    CplxDiffAt BHist.Empty z fp -> CplxNonZero fp := by
  intro diff quotientEmpty
  cases CplxDiffAt_witness_step_nonzero diff with
  | intro h witness =>
      cases witness with
      | intro q data =>
          cases data with
          | intro _stepNonzero rest =>
              cases rest with
              | intro quotient rest =>
                  cases rest with
                  | intro _ledger sameQFp =>
                      exact CplxDiffQuot_empty_function_result_nonzero quotient
                        (hsame_trans sameQFp quotientEmpty)

theorem CplxDiffAt_full_hsame_transport_witness {f f' z z' fp gp : BHist} :
    CplxDiffAt f z fp -> hsame f f' -> hsame z z' -> hsame fp gp ->
      CplxDiffAt f' z' gp ∧
        ∃ h : BHist, ∃ q : BHist,
          CplxDiffQuot f' z' h q ∧ Cont f' h q ∧ hsame q gp := by
  intro diff sameF sameZ sameFpGp
  cases diff with
  | intro functionCarrier diffRest =>
      cases diffRest with
      | intro pointCarrier diffRest =>
          cases diffRest with
          | intro derivativeCarrier diffRest =>
              cases diffRest with
              | intro witness classifier =>
                  cases witness with
                  | intro h witnessRest =>
                      cases witnessRest with
                      | intro q quotient =>
                          have functionCarrier' : UnaryHistory f' :=
                            unary_transport functionCarrier sameF
                          have pointCarrier' : UnaryHistory z' :=
                            unary_transport pointCarrier sameZ
                          have derivativeCarrier' : ComplexHistoryCarrier gp :=
                            BEDC.Derived.ProdUp.ProdHistoryCarrier_hsame_transport sameFpGp
                              derivativeCarrier
                          have sameQGp : hsame q gp :=
                            hsame_trans (classifier quotient) sameFpGp
                          have transported :=
                            CplxDiffQuot_hsame_transport sameF sameZ (hsame_refl h) sameQGp
                              quotient
                          have quotient' : CplxDiffQuot f' z' h gp := transported.left
                          have continuation' : Cont f' h gp := transported.right.right.right
                          have diff' : CplxDiffAt f' z' gp := by
                            exact And.intro functionCarrier'
                              (And.intro pointCarrier'
                                (And.intro derivativeCarrier'
                                  (And.intro
                                    (Exists.intro h (Exists.intro gp quotient'))
                                    (by
                                      intro h' q' quotientAtTarget
                                      have quotientAtSource : CplxDiffQuot f z h' q' :=
                                        (CplxDiffQuot_hsame_transport (hsame_symm sameF)
                                          (hsame_symm sameZ) (hsame_refl h') (hsame_refl q')
                                          quotientAtTarget).left
                                      exact hsame_trans
                                        (classifier quotientAtSource) sameFpGp))))
                          exact And.intro diff'
                            (Exists.intro h
                            (Exists.intro gp
                              (And.intro quotient'
                              (And.intro continuation' (hsame_refl gp)))))

theorem CplxDiffAt_prepend_complex_scalar_closed {c f z fp : BHist} :
    ComplexHistoryCarrier c -> CplxDiffAt f z fp ->
      CplxDiffAt (append c f) z (append c fp) ∧ ComplexHistoryCarrier (append c fp) := by
  intro cCarrier diff
  cases diff with
  | intro functionCarrier diffRest =>
      cases diffRest with
      | intro pointCarrier diffRest =>
          cases diffRest with
          | intro derivativeCarrier diffRest =>
              cases diffRest with
              | intro witness classifier =>
                  cases witness with
                  | intro h witnessRest =>
                      cases witnessRest with
                      | intro q quotient =>
                          have cUnary : UnaryHistory c :=
                            ComplexHistoryCarrier_unary cCarrier
                          have targetFunctionCarrier : UnaryHistory (append c f) :=
                            unary_append_closed cUnary functionCarrier
                          have targetDerivativeCarrier :
                              ComplexHistoryCarrier (append c fp) :=
                            ComplexHistoryCarrier_append_unary_closed cCarrier
                              (ComplexHistoryCarrier_unary derivativeCarrier)
                          have qUnary : UnaryHistory q := (CplxDiffQuot_step_unary quotient).right.left
                          have targetQuotient :
                              CplxDiffQuot (append c f) z h (append c q) := by
                            cases quotient with
                            | intro _functionCarrier quotientRest =>
                                cases quotientRest with
                                | intro _pointCarrier quotientRest =>
                                    cases quotientRest with
                                    | intro stepNonzero quotientRest =>
                                        cases quotientRest with
                                        | intro _quotientCarrier ledger =>
                                            exact And.intro targetFunctionCarrier
                                              (And.intro pointCarrier
                                                (And.intro stepNonzero
                                                  (And.intro
                                                    (unary_append_closed cUnary qUnary)
                                                    (by
                                                      cases ledger
                                                      exact (append_assoc c f h).symm))))
                          have targetDiff :
                              CplxDiffAt (append c f) z (append c fp) := by
                            exact And.intro targetFunctionCarrier
                              (And.intro pointCarrier
                                (And.intro targetDerivativeCarrier
                                  (And.intro
                                    (Exists.intro h (Exists.intro (append c q) targetQuotient))
                                    (by
                                      intro h' q' targetQuotient'
                                      have hUnary : UnaryHistory h' :=
                                        (CplxDiffQuot_step_unary targetQuotient').left
                                      have sourceResultUnary : UnaryHistory (append f h') :=
                                        unary_append_closed functionCarrier hUnary
                                      have sourceQuotient : CplxDiffQuot f z h' (append f h') :=
                                        And.intro functionCarrier
                                          (And.intro pointCarrier
                                            (And.intro targetQuotient'.right.right.left
                                              (And.intro sourceResultUnary rfl)))
                                      have sameSourceResult : hsame (append f h') fp :=
                                        classifier sourceQuotient
                                      have sameTargetResult :
                                          hsame q' (append c (append f h')) :=
                                        hsame_trans targetQuotient'.right.right.right.right
                                          (append_assoc c f h')
                                      cases sameSourceResult
                                      exact sameTargetResult))))
                          exact And.intro targetDiff targetDerivativeCarrier

theorem CplxDiffClassifierSpec_hsame_transport_witness {f g z w fp gp : BHist} :
    CplxDiffAt f z fp -> hsame f g -> hsame z w -> hsame fp gp ->
      CplxDiffClassifierSpec f z fp g w gp ∧
        ∃ h : BHist, ∃ q : BHist,
          CplxDiffQuot g w h q ∧ Cont g h q ∧ hsame q gp := by
  intro diff sameF sameZ sameFpGp
  have transported := CplxDiffAt_full_hsame_transport_witness diff sameF sameZ sameFpGp
  exact And.intro
    (And.intro diff
      (And.intro transported.left
        (And.intro sameF (And.intro sameZ sameFpGp))))
    transported.right

theorem PartialDerivative_hsame_input_unique {u z z' p q : BHist} :
    ((PartialReal u z p -> PartialReal u z' q -> hsame z z' ->
        hsame p q ∧ PartialReal u z q ∧ PartialReal u z' p ∧
          ∃ h : BHist, ∃ r : BHist, CplxDiffQuot u z h r ∧ Cont u h r) ∧
      (PartialImag u z p -> PartialImag u z' q -> hsame z z' ->
        hsame p q ∧ PartialImag u z q ∧ PartialImag u z' p ∧
          ∃ h : BHist, ∃ r : BHist, CplxDiffQuot u z h r ∧ Cont u h r)) := by
  constructor
  · intro partialSource partialTarget sameInput
    have targetAtSource : CplxDiffAt u z q :=
      (CplxDiffAt_hsame_transport_witness partialTarget.right.right
        (hsame_symm sameInput) (hsame_refl q)).left
    have unique := CplxDiffAt_derivative_unique partialSource.right.right targetAtSource
    have sourceAtTarget : CplxDiffAt u z' p :=
      (CplxDiffAt_hsame_transport_witness partialSource.right.right sameInput
        (hsame_refl p)).left
    exact And.intro unique.left
      (And.intro
        (And.intro partialSource.left
          (And.intro (unary_transport partialTarget.right.left (hsame_symm sameInput))
            targetAtSource))
        (And.intro
          (And.intro partialTarget.left
            (And.intro (unary_transport partialSource.right.left sameInput) sourceAtTarget))
          unique.right))
  · intro partialSource partialTarget sameInput
    have targetAtSource : CplxDiffAt u z q :=
      (CplxDiffAt_hsame_transport_witness partialTarget.right.right
        (hsame_symm sameInput) (hsame_refl q)).left
    have unique := CplxDiffAt_derivative_unique partialSource.right.right targetAtSource
    have sourceAtTarget : CplxDiffAt u z' p :=
      (CplxDiffAt_hsame_transport_witness partialSource.right.right sameInput
        (hsame_refl p)).left
    exact And.intro unique.left
      (And.intro
        (And.intro partialSource.left
          (And.intro (unary_transport partialTarget.right.left (hsame_symm sameInput))
            targetAtSource))
        (And.intro
          (And.intro partialTarget.left
            (And.intro (unary_transport partialSource.right.left sameInput) sourceAtTarget))
          unique.right))

theorem complex_diff_semantic_name_certificate {f z fp : BHist} :
    CplxDiffAt f z fp ->
      SemanticNameCert (CplxDiffAt f z) (CplxDiffAt f z) (CplxDiffAt f z) hsame := by
  intro diff
  exact {
    core := {
      carrier_inhabited := Exists.intro fp diff
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k same carrier
        exact (CplxDiffAt_hsame_transport_witness carrier (hsame_refl z) same).left
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }

def CplxDiffLedgerPolicy (f z fp : BHist) : Prop :=
  CplxDiffAt f z fp ∧
    (∃ h : BHist, ∃ q : BHist,
      CplxDiffQuot f z h q ∧ Cont f h q ∧ CplxNonZero h ∧ CplxNonZero q ∧
        hsame q fp) ∧
      SemanticNameCert (CplxDiffAt f z) (CplxDiffAt f z) (CplxDiffAt f z) hsame

theorem CplxDiffLedgerPolicy_of_diff {f z fp : BHist} :
    CplxDiffAt f z fp -> CplxDiffLedgerPolicy f z fp := by
  intro diff
  exact And.intro diff
    (And.intro (CplxDiffAt_witness_nonzero_result diff)
      (complex_diff_semantic_name_certificate diff))

theorem complex_diff_name_certificate {f z fp : BHist} (diff : CplxDiffAt f z fp) :
    NameCert (CplxDiffAt f z) ComplexHistoryClassifier := by
  exact {
    carrier_inhabited := Exists.intro fp diff
    equiv_refl := by
      intro h carrier
      exact And.intro carrier.right.right.left
        (And.intro carrier.right.right.left (hsame_refl h))
    equiv_symm := by
      intro h k classified
      exact ComplexHistoryClassifier_symm classified
    equiv_trans := by
      intro h k r classifiedHK classifiedKR
      exact ComplexHistoryClassifier_trans classifiedHK classifiedKR
    carrier_respects_equiv := by
      intro h k classified carrier
      exact (CplxDiffAt_hsame_transport_witness carrier (hsame_refl z) classified.right.right).left
  }

theorem CplxDiff_stability_certificate_fields :
    (forall {f z z' fp gp : BHist}, CplxDiffAt f z fp -> hsame z z' ->
      hsame fp gp -> CplxDiffAt f z' gp ∧
        exists h : BHist, exists q : BHist,
          CplxDiffQuot f z' h q ∧ Cont f h q ∧ hsame q gp) ∧
    (forall {f z fp gp : BHist}, CplxDiffAt f z fp -> CplxDiffAt f z gp ->
      hsame fp gp ∧
        exists h : BHist, exists q : BHist, CplxDiffQuot f z h q ∧ Cont f h q) ∧
    (forall {f f' z z' h h' q q' : BHist}, hsame f f' -> hsame z z' ->
      hsame h h' -> hsame q q' -> CplxDiffQuot f z h q ->
        CplxDiffQuot f' z' h' q' ∧ UnaryHistory z' ∧ CplxNonZero h' ∧
          Cont f' h' q') := by
  constructor
  · intro f z z' fp gp diff sameZ sameFpGp
    exact CplxDiffAt_hsame_transport_witness diff sameZ sameFpGp
  · constructor
    · intro f z fp gp leftDiff rightDiff
      exact CplxDiffAt_derivative_unique leftDiff rightDiff
    · intro f f' z z' h h' q q' sameF sameZ sameH sameQ quotient
      exact CplxDiffQuot_hsame_transport sameF sameZ sameH sameQ quotient

end BEDC.Derived.ComplexDifferentiabilityUp
