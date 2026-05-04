import BEDC.Derived.ComplexDiffUp

namespace BEDC.Derived.ComplexDifferentiabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp
open BEDC.Derived.ComplexDiffUp

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

end BEDC.Derived.ComplexDifferentiabilityUp
