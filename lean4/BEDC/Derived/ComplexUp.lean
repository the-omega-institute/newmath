import BEDC.Derived.ProdUp
import BEDC.Derived.RatUp

namespace BEDC.Derived.ComplexUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

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

end BEDC.Derived.ComplexUp
