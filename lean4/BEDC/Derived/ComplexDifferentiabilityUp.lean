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
