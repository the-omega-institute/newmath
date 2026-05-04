import BEDC.Derived.ProdUp
import BEDC.Derived.RatUp

namespace BEDC.Derived.ComplexUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def ComplexHistoryCarrier (h : BHist) : Prop :=
  BEDC.Derived.ProdUp.ProdHistoryCarrier BEDC.Derived.RatUp.RatHistoryCarrier
    BEDC.Derived.RatUp.RatHistoryCarrier h

def ComplexHistoryClassifier (h k : BHist) : Prop :=
  BEDC.Derived.ProdUp.ProdHistoryClassifier BEDC.Derived.RatUp.RatHistoryCarrier
    BEDC.Derived.RatUp.RatHistoryCarrier h k

def ComplexHistoryLedgerPolicy (raw visible : BHist) : Prop :=
  ComplexHistoryCarrier raw ∧ hsame raw visible

theorem ComplexHistoryLedgerPolicy_visible_carrier {raw visible : BHist} :
    ComplexHistoryLedgerPolicy raw visible -> ComplexHistoryCarrier visible := by
  intro ledger
  cases ledger with
  | intro rawCarrier sameRawVisible =>
      cases rawCarrier with
      | intro leftHist rest =>
          cases rest with
          | intro rightHist data =>
              cases data with
              | intro leftCarrier rightData =>
                  cases rightData with
                  | intro rightCarrier cont =>
                      exact Exists.intro leftHist
                        (Exists.intro rightHist
                          (And.intro leftCarrier
                            (And.intro rightCarrier
                              (cont_result_hsame_transport cont sameRawVisible))))

theorem ComplexHistoryLedgerPolicy_raw_visible_classifier {raw visible : BHist} :
    ComplexHistoryLedgerPolicy raw visible -> ComplexHistoryClassifier raw visible := by
  intro ledger
  cases ledger with
  | intro rawCarrier sameRawVisible =>
      exact And.intro rawCarrier
        (And.intro
          (ComplexHistoryLedgerPolicy_visible_carrier
            (And.intro rawCarrier sameRawVisible))
          sameRawVisible)

theorem ComplexHistoryCarrier_positive_components {h : BHist} :
    ComplexHistoryCarrier h →
      ∃ real imag : BHist,
        RatUp.RatHistoryCarrier real ∧ RatUp.RatHistoryCarrier imag ∧ Cont real imag h ∧
          RatUp.PositiveUnaryDenominator real ∧ RatUp.PositiveUnaryDenominator imag := by
  intro carrier
  cases carrier with
  | intro real rest =>
      cases rest with
      | intro imag data =>
          cases data with
          | intro realCarrier rest =>
              cases rest with
              | intro imagCarrier cont =>
                  exact Exists.intro real
                    (Exists.intro imag
                      (And.intro realCarrier
                        (And.intro imagCarrier
                          (And.intro cont
                            (And.intro
                              (RatUp.RatHistoryCarrier_iff_positive_denominator.mp
                                realCarrier)
                              (RatUp.RatHistoryCarrier_iff_positive_denominator.mp
                                imagCarrier))))))

theorem ComplexHistoryClassifier_e0_endpoint_absurd {tail h : BHist} :
    (ComplexHistoryClassifier (BHist.e0 tail) h -> False) /\
      (ComplexHistoryClassifier h (BHist.e0 tail) -> False) := by
  have carrierE0Absurd : ComplexHistoryCarrier (BHist.e0 tail) -> False := by
    intro carrier
    have components := ComplexHistoryCarrier_positive_components carrier
    cases components with
    | intro real rest =>
        cases rest with
        | intro imag data =>
            cases data with
            | intro _realCarrier data =>
                cases data with
                | intro _imagCarrier data =>
                    cases data with
                    | intro cont data =>
                        cases data with
                        | intro _positiveReal positiveImag =>
                            have resultCases := cont_e0_result_inversion cont
                            cases resultCases with
                            | inl emptyCase =>
                                cases emptyCase with
                                | intro imagEmpty _sameReal =>
                                    cases imagEmpty
                                    exact RatUp.PositiveUnaryDenominator_not_empty
                                      positiveImag (hsame_refl BHist.Empty)
                            | inr visibleCase =>
                                cases visibleCase with
                                | intro imagTail fields =>
                                    cases fields with
                                    | intro imagVisible _tailCont =>
                                        cases imagVisible
                                        exact RatUp.PositiveUnaryDenominator_e0_absurd
                                          positiveImag
  constructor
  · intro classified
    exact carrierE0Absurd classified.left
  · intro classified
    exact carrierE0Absurd classified.right.left

theorem ComplexHistoryLedgerPolicy_e0_visible_absurd {raw tail : BHist} :
    ComplexHistoryLedgerPolicy raw (BHist.e0 tail) -> False := by
  intro ledger
  have carrierE0 : ComplexHistoryCarrier (BHist.e0 tail) :=
    ComplexHistoryLedgerPolicy_visible_carrier ledger
  have components := ComplexHistoryCarrier_positive_components carrierE0
  cases components with
  | intro real rest =>
      cases rest with
      | intro imag data =>
          cases data with
          | intro _realCarrier data =>
              cases data with
              | intro _imagCarrier data =>
                  cases data with
                  | intro cont data =>
                      cases data with
                      | intro _positiveReal positiveImag =>
                          have resultCases := cont_e0_result_inversion cont
                          cases resultCases with
                          | inl emptyCase =>
                              cases emptyCase with
                              | intro imagEmpty _sameReal =>
                                  cases imagEmpty
                                  exact RatUp.PositiveUnaryDenominator_not_empty
                                    positiveImag (hsame_refl BHist.Empty)
                          | inr visibleCase =>
                              cases visibleCase with
                              | intro imagTail fields =>
                                  cases fields with
                                  | intro imagVisible _tailCont =>
                                      cases imagVisible
                                      exact RatUp.PositiveUnaryDenominator_e0_absurd
                                        positiveImag

theorem ComplexHistoryCarrier_not_empty {h : BHist} :
    ComplexHistoryCarrier h -> hsame h BHist.Empty -> False := by
  intro carrier sameEmpty
  cases carrier with
  | intro real rest =>
      cases rest with
      | intro imag data =>
          cases data with
          | intro realCarrier data =>
              cases data with
              | intro _imagCarrier cont =>
                  have emptyParts :=
                    cont_empty_result_inversion (cont_result_hsame_transport cont sameEmpty)
                  exact RatUp.RatHistoryCarrier_not_empty realCarrier emptyParts.left

theorem ComplexHistoryClassifier_trans {h k r : BHist} :
    ComplexHistoryClassifier h k -> ComplexHistoryClassifier k r ->
      ComplexHistoryClassifier h r := by
  intro classifiedHK classifiedKR
  cases classifiedHK with
  | intro carrierH restHK =>
      cases restHK with
      | intro _ sameHK =>
          cases classifiedKR with
          | intro _ restKR =>
              cases restKR with
              | intro carrierR sameKR =>
                  exact And.intro carrierH (And.intro carrierR (hsame_trans sameHK sameKR))

theorem ComplexHistoryClassifier_symm {h k : BHist} :
    ComplexHistoryClassifier h k -> ComplexHistoryClassifier k h := by
  intro classified
  cases classified with
  | intro carrierH rest =>
      cases rest with
      | intro carrierK sameHK =>
          exact And.intro carrierK (And.intro carrierH (hsame_symm sameHK))

theorem ComplexHistoryClassifier_positive_components {h k : BHist} :
    ComplexHistoryClassifier h k ->
      ∃ hr hi kr ki : BHist,
        RatUp.RatHistoryCarrier hr ∧ RatUp.RatHistoryCarrier hi ∧
          RatUp.RatHistoryCarrier kr ∧ RatUp.RatHistoryCarrier ki ∧ Cont hr hi h ∧
            Cont kr ki k ∧ hsame h k ∧ RatUp.PositiveUnaryDenominator hr ∧
              RatUp.PositiveUnaryDenominator hi ∧ RatUp.PositiveUnaryDenominator kr ∧
                RatUp.PositiveUnaryDenominator ki := by
  intro classified
  cases classified with
  | intro carrierH rest =>
      cases rest with
      | intro carrierK sameHK =>
          have leftComponents := ComplexHistoryCarrier_positive_components carrierH
          have rightComponents := ComplexHistoryCarrier_positive_components carrierK
          cases leftComponents with
          | intro hr leftRest =>
              cases leftRest with
              | intro hi leftData =>
                  cases leftData with
                  | intro hrCarrier leftData =>
                      cases leftData with
                      | intro hiCarrier leftData =>
                          cases leftData with
                          | intro contH leftPositive =>
                              cases leftPositive with
                              | intro positiveHr positiveHi =>
                                  cases rightComponents with
                                  | intro kr rightRest =>
                                      cases rightRest with
                                      | intro ki rightData =>
                                          cases rightData with
                                          | intro krCarrier rightData =>
                                              cases rightData with
                                              | intro kiCarrier rightData =>
                                                  cases rightData with
                                                  | intro contK rightPositive =>
                                                      cases rightPositive with
                                                      | intro positiveKr positiveKi =>
                                                          exact ⟨hr, hi, kr, ki,
                                                            hrCarrier, hiCarrier, krCarrier,
                                                            kiCarrier, contH, contK, sameHK,
                                                            positiveHr, positiveHi, positiveKr,
                                                            positiveKi⟩

theorem ComplexHistoryCarrier_prepend_unary_closed {p h : BHist} :
    UnaryHistory p -> ComplexHistoryCarrier h -> ComplexHistoryCarrier (append p h) := by
  intro pUnary carrier
  cases carrier with
  | intro real rest =>
      cases rest with
      | intro imag data =>
          cases data with
          | intro realCarrier rest =>
              cases rest with
              | intro imagCarrier cont =>
                  exact Exists.intro (append p real)
                    (Exists.intro imag
                      (And.intro
                        (RatUp.RatHistoryCarrier_prepend_unary_denominator_closed pUnary
                          realCarrier)
                        (And.intro imagCarrier
                          (cont_intro
                            ((congrArg (append p) cont).trans
                              (append_assoc p real imag).symm)))))

theorem ComplexHistoryCarrier_append_unary_closed {h q : BHist} :
    ComplexHistoryCarrier h -> UnaryHistory q -> ComplexHistoryCarrier (append h q) := by
  intro carrier qUnary
  cases carrier with
  | intro real rest =>
      cases rest with
      | intro imag data =>
          cases data with
          | intro realCarrier rest =>
              cases rest with
              | intro imagCarrier cont =>
                  exact Exists.intro real
                    (Exists.intro (append imag q)
                      (And.intro realCarrier
                        (And.intro
                          (RatUp.RatHistoryCarrier_append_unary_denominator_closed
                            imagCarrier qUnary)
                          (cont_intro
                            ((congrArg (fun visible => append visible q) cont).trans
                              (append_assoc real imag q))))))

theorem ComplexHistoryClassifier_unary_context_closed {p p' h k q q' : BHist} :
    UnaryHistory p -> hsame p p' -> ComplexHistoryClassifier h k ->
      UnaryHistory q -> hsame q q' ->
        ComplexHistoryClassifier
          (BEDC.FKernel.Cont.append p (BEDC.FKernel.Cont.append h q))
          (BEDC.FKernel.Cont.append p' (BEDC.FKernel.Cont.append k q')) := by
  intro pUnary sameP classified qUnary sameQ
  cases classified with
  | intro carrierH rest =>
      cases rest with
      | intro carrierK sameHK =>
          have pUnary' : UnaryHistory p' := unary_transport pUnary sameP
          have qUnary' : UnaryHistory q' := unary_transport qUnary sameQ
          have tailCarrierH : ComplexHistoryCarrier (append h q) :=
            ComplexHistoryCarrier_append_unary_closed carrierH qUnary
          have tailCarrierK : ComplexHistoryCarrier (append k q') :=
            ComplexHistoryCarrier_append_unary_closed carrierK qUnary'
          have contextCarrierH : ComplexHistoryCarrier (append p (append h q)) :=
            ComplexHistoryCarrier_prepend_unary_closed pUnary tailCarrierH
          have contextCarrierK : ComplexHistoryCarrier (append p' (append k q')) :=
            ComplexHistoryCarrier_prepend_unary_closed pUnary' tailCarrierK
          have sameContext :
              hsame (append p (append h q)) (append p' (append k q')) := by
            cases sameP
            cases sameHK
            cases sameQ
            rfl
          exact And.intro contextCarrierH (And.intro contextCarrierK sameContext)

theorem ComplexHistoryClassifier_unary_context_positive_components {p p' h k q q' : BHist} :
    UnaryHistory p -> hsame p p' -> ComplexHistoryClassifier h k -> UnaryHistory q ->
      hsame q q' ->
        ∃ hr hi kr ki : BHist,
          RatUp.RatHistoryCarrier hr ∧ RatUp.RatHistoryCarrier hi ∧
            RatUp.RatHistoryCarrier kr ∧ RatUp.RatHistoryCarrier ki ∧
              Cont hr hi (append p (append h q)) ∧
                Cont kr ki (append p' (append k q')) ∧
                  hsame (append p (append h q)) (append p' (append k q')) ∧
                    RatUp.PositiveUnaryDenominator hr ∧
                      RatUp.PositiveUnaryDenominator hi ∧
                        RatUp.PositiveUnaryDenominator kr ∧
                          RatUp.PositiveUnaryDenominator ki := by
  intro pUnary sameP classified qUnary sameQ
  have contextClassified :
      ComplexHistoryClassifier (append p (append h q)) (append p' (append k q')) :=
    ComplexHistoryClassifier_unary_context_closed pUnary sameP classified qUnary sameQ
  exact ComplexHistoryClassifier_positive_components contextClassified

theorem ComplexHistoryLedgerPolicy_classifier_extension {raw visible t : BHist} :
    ComplexHistoryLedgerPolicy raw visible -> ComplexHistoryClassifier visible t ->
      ComplexHistoryClassifier raw t := by
  intro ledger classified
  cases ledger with
  | intro rawCarrier sameRawVisible =>
      cases classified with
      | intro _visibleCarrier rest =>
          cases rest with
          | intro targetCarrier sameVisibleTarget =>
              exact And.intro rawCarrier
                (And.intro targetCarrier (hsame_trans sameRawVisible sameVisibleTarget))

theorem ComplexHistoryCarrier_unary {h : BHist} :
    ComplexHistoryCarrier h -> BEDC.FKernel.Unary.UnaryHistory h := by
  intro carrier
  exact BEDC.Derived.ProdUp.ProdHistoryCarrier_unary_of_components
    (fun {d : BHist} ratCarrier =>
      (BEDC.Derived.RatUp.PositiveUnaryDenominator_unary_and_nonempty
        (BEDC.Derived.RatUp.RatHistoryCarrier_iff_positive_denominator.mp ratCarrier)).left)
    (fun {d : BHist} ratCarrier =>
      (BEDC.Derived.RatUp.PositiveUnaryDenominator_unary_and_nonempty
        (BEDC.Derived.RatUp.RatHistoryCarrier_iff_positive_denominator.mp ratCarrier)).left)
    carrier

theorem complex_history_semantic_name_certificate :
    SemanticNameCert ComplexHistoryCarrier ComplexHistoryCarrier ComplexHistoryCarrier
      ComplexHistoryClassifier := by
  have ratCert :
      SemanticNameCert BEDC.Derived.RatUp.RatHistoryCarrier
        BEDC.Derived.RatUp.RatHistoryCarrier BEDC.Derived.RatUp.RatHistoryCarrier
        BEDC.Derived.RatUp.RatHistoryClassifier :=
    BEDC.Derived.RatUp.rat_history_semantic_name_certificate
  cases ratCert.core.carrier_inhabited with
  | intro realHist realCarrier =>
      cases ratCert.core.carrier_inhabited with
      | intro imagHist imagCarrier =>
          exact {
            core := {
              carrier_inhabited := Exists.intro (append realHist imagHist)
                (Exists.intro realHist
                  (Exists.intro imagHist
                    (And.intro realCarrier
                      (And.intro imagCarrier
                        (cont_intro (h := realHist) (k := imagHist) rfl)))))
              equiv_refl := by
                intro h carrier
                exact And.intro carrier (And.intro carrier (hsame_refl h))
              equiv_symm := by
                intro h k classified
                cases classified with
                | intro carrierH rest =>
                    cases rest with
                    | intro carrierK sameHK =>
                        exact And.intro carrierK (And.intro carrierH (hsame_symm sameHK))
              equiv_trans := by
                intro h k r classifiedHK classifiedKR
                cases classifiedHK with
                | intro carrierH restHK =>
                    cases restHK with
                    | intro _ sameHK =>
                        cases classifiedKR with
                        | intro _ restKR =>
                            cases restKR with
                            | intro carrierR sameKR =>
                                exact And.intro carrierH
                                  (And.intro carrierR (hsame_trans sameHK sameKR))
              carrier_respects_equiv := by
                intro h k classified carrier
                cases carrier with
                | intro leftHist rest =>
                    cases rest with
                    | intro rightHist data =>
                        cases data with
                        | intro leftCarrier rightData =>
                            cases rightData with
                            | intro rightCarrier cont =>
                                exact Exists.intro leftHist
                                  (Exists.intro rightHist
                                    (And.intro leftCarrier
                                      (And.intro rightCarrier
                                        (cont_result_hsame_transport cont
                                          classified.right.right))))
            }
            pattern_sound := by
              intro h source
              exact source
            ledger_sound := by
              intro h source
              exact source
          }

theorem ComplexHistoryClassifier_component_classifier_intro
    {real imag real' imag' h k : BHist} :
    RatUp.RatHistoryClassifier real real' -> RatUp.RatHistoryClassifier imag imag' ->
      Cont real imag h -> Cont real' imag' k -> ComplexHistoryClassifier h k := by
  intro realClassifier imagClassifier contH contK
  have carrierH : ComplexHistoryCarrier h :=
    Exists.intro real
      (Exists.intro imag
        (And.intro realClassifier.left (And.intro imagClassifier.left contH)))
  have carrierK : ComplexHistoryCarrier k :=
    Exists.intro real'
      (Exists.intro imag'
        (And.intro realClassifier.right.left (And.intro imagClassifier.right.left contK)))
  have sameHK : hsame h k :=
    cont_respects_hsame realClassifier.right.right imagClassifier.right.right contH contK
  exact And.intro carrierH (And.intro carrierK sameHK)

end BEDC.Derived.ComplexUp
