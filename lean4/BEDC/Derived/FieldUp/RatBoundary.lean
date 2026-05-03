import BEDC.Derived.FieldUp
import BEDC.Derived.RatUp
import BEDC.Derived.RatUp.HistoryClassifier

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem field_rat_denominator_continuation_carrier_closure {d e r : BHist} :
    BEDC.Derived.RatUp.RatHistoryCarrier d ->
      BEDC.Derived.RatUp.RatHistoryCarrier e ->
        BEDC.FKernel.Cont.Cont d e r ->
          BEDC.Derived.RatUp.RatHistoryCarrier r := by
  intro carrierD carrierE contDER
  have positiveE : PositiveUnaryDenominator e :=
    RatHistoryCarrier_iff_positive_denominator.mp carrierE
  have unaryE : UnaryHistory e :=
    (PositiveUnaryDenominator_unary_and_nonempty positiveE).left
  have appendCarrier : RatHistoryCarrier (append d e) :=
    RatHistoryCarrier_append_unary_denominator_closed carrierD unaryE
  have sameResult : hsame (append d e) r :=
    cont_deterministic (cont_intro (h := d) (k := e) (r := append d e) rfl) contDER
  exact RatHistoryCarrier_hsame_transport sameResult appendCarrier

theorem field_rat_history_carrier_non_singleton_boundary_witness :
    BEDC.Derived.RatUp.RatHistoryCarrier (BHist.e1 BHist.Empty) /\
      (fieldSingletonEmptyCarrier (BHist.e1 BHist.Empty) -> False) /\
      ((forall h : BHist, BEDC.Derived.RatUp.RatHistoryCarrier h ->
        fieldSingletonEmptyCarrier h) -> False) := by
  have positiveDenominator :
      BEDC.Derived.RatUp.PositiveUnaryDenominator (BHist.e1 BHist.Empty) :=
    BEDC.Derived.RatUp.PositiveUnaryDenominator_e1_iff_unary.mpr unary_empty
  have ratCarrier :
      BEDC.Derived.RatUp.RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    BEDC.Derived.RatUp.RatHistoryCarrier_iff_positive_denominator.mpr positiveDenominator
  have singletonAbsurd : fieldSingletonEmptyCarrier (BHist.e1 BHist.Empty) -> False := by
    intro singletonCarrier
    exact BEDC.Derived.RatUp.RatHistoryCarrier_not_empty ratCarrier singletonCarrier
  exact And.intro ratCarrier
    (And.intro singletonAbsurd
      (by
        intro coverage
        exact singletonAbsurd (coverage (BHist.e1 BHist.Empty) ratCarrier)))

theorem field_rat_carrier_non_singleton_boundary_witness :
    BEDC.Derived.RatUp.RatHistoryCarrier (BHist.e1 BHist.Empty) ∧
      (FieldSingletonCarrier (BHist.e1 BHist.Empty) -> False) ∧
        ((forall h : BHist, BEDC.Derived.RatUp.RatHistoryCarrier h ->
          FieldSingletonCarrier h) -> False) := by
  have ratBoundary : BEDC.Derived.RatUp.RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    BEDC.Derived.RatUp.RatHistoryCarrier_e1_tail_unary_iff.mpr
      BEDC.FKernel.Unary.unary_empty
  have singletonAbsurd : FieldSingletonCarrier (BHist.e1 BHist.Empty) -> False := by
    intro singleton
    exact BEDC.Derived.RatUp.RatHistoryCarrier_not_empty ratBoundary singleton
  constructor
  · exact ratBoundary
  · constructor
    · exact singletonAbsurd
    · intro carrierCoverage
      exact singletonAbsurd (carrierCoverage (BHist.e1 BHist.Empty) ratBoundary)

theorem field_rat_carrier_singleton_coverage_obstruction :
    BEDC.Derived.RatUp.RatHistoryCarrier (BHist.e1 BHist.Empty) ∧
      (fieldSingletonEmptyCarrier (BHist.e1 BHist.Empty) -> False) ∧
      ((∀ h : BHist, BEDC.Derived.RatUp.RatHistoryCarrier h -> fieldSingletonEmptyCarrier h) ->
        False) := by
  have carrierD1 : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have notSingleton : fieldSingletonEmptyCarrier (BHist.e1 BHist.Empty) -> False := by
    intro singletonD1
    exact RatHistoryCarrier_not_empty carrierD1 singletonD1
  constructor
  · exact carrierD1
  · constructor
    · exact notSingleton
    · intro coverage
      exact notSingleton (coverage (BHist.e1 BHist.Empty) carrierD1)

theorem field_rat_singleton_classifier_ledger_coverage_obstruction :
    RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) ∧
      RatHistoryLedgerPolicy (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) ∧
        (FieldSingletonClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) -> False) ∧
          ((∀ h k : BHist, RatHistoryClassifier h k -> FieldSingletonClassifier h k) ->
            False) ∧
            ((∀ raw visible : BHist, RatHistoryLedgerPolicy raw visible ->
              FieldSingletonCarrier raw ∧ FieldSingletonCarrier visible) -> False) := by
  have boundary := field_rat_carrier_non_singleton_boundary_witness
  have carrierD1 : RatHistoryCarrier (BHist.e1 BHist.Empty) := boundary.left
  have notSingleton : FieldSingletonCarrier (BHist.e1 BHist.Empty) -> False :=
    boundary.right.left
  have classifierD1 :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    ⟨carrierD1, carrierD1, hsame_refl (BHist.e1 BHist.Empty)⟩
  have ledgerD1 :
      RatHistoryLedgerPolicy (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    ⟨carrierD1, hsame_refl (BHist.e1 BHist.Empty)⟩
  have classifierAbsurd :
      FieldSingletonClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) -> False := by
    intro singletonClassifier
    exact notSingleton singletonClassifier.left
  constructor
  · exact classifierD1
  · constructor
    · exact ledgerD1
    · constructor
      · exact classifierAbsurd
      · constructor
        · intro classifierCoverage
          exact classifierAbsurd
            (classifierCoverage (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) classifierD1)
        · intro ledgerCoverage
          exact notSingleton (ledgerCoverage (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)
            ledgerD1).left

theorem RatHistoryLedgerPolicy_fieldSingletonEmptyCarrier_endpoints_absurd {raw visible : BHist} :
    RatHistoryLedgerPolicy raw visible ->
      (hsame raw BHist.Empty -> False) ∧
        (hsame visible BHist.Empty -> False) ∧
          (fieldSingletonEmptyCarrier raw -> False) ∧
            (fieldSingletonEmptyCarrier visible -> False) := by
  intro ledger
  have rawAbsurd : hsame raw BHist.Empty -> False := by
    intro rawEmpty
    exact RatHistoryCarrier_not_empty ledger.left rawEmpty
  have visibleAbsurd : hsame visible BHist.Empty -> False := by
    intro visibleEmpty
    exact RatHistoryCarrier_not_empty (RatHistoryLedgerPolicy_visible_carrier ledger) visibleEmpty
  exact And.intro rawAbsurd (And.intro visibleAbsurd (And.intro rawAbsurd visibleAbsurd))

theorem RatHistoryClassifier_fieldSingleton_empty_endpoints_absurd {h k : BHist} :
    RatHistoryClassifier h k ->
      (hsame h BHist.Empty -> False) ∧ (hsame k BHist.Empty -> False) ∧
        (FieldSingletonClassifier h k -> False) := by
  intro classified
  have leftAbsurd : hsame h BHist.Empty -> False := by
    intro sameEmpty
    exact RatHistoryCarrier_not_empty classified.left sameEmpty
  have rightAbsurd : hsame k BHist.Empty -> False := by
    intro sameEmpty
    exact RatHistoryCarrier_not_empty classified.right.left sameEmpty
  have singletonAbsurd : FieldSingletonClassifier h k -> False := by
    intro singleton
    exact leftAbsurd singleton.left
  exact And.intro leftAbsurd (And.intro rightAbsurd singletonAbsurd)

theorem fieldSingletonEmptyCarrier_append_ratHistoryCarrier_absurd {p h : BHist} :
    fieldSingletonEmptyCarrier (append p h) -> RatHistoryCarrier h -> False := by
  intro appendEmpty ratH
  have splitEmpty := append_eq_empty_iff.mp appendEmpty
  exact RatHistoryCarrier_not_empty ratH splitEmpty.right

theorem fieldSingletonEmptyCarrier_append_left_ratHistoryCarrier_absurd {p h : BHist} :
    fieldSingletonEmptyCarrier (append h p) -> RatHistoryCarrier h -> False := by
  intro appendEmpty ratH
  have splitEmpty := append_eq_empty_iff.mp appendEmpty
  exact RatHistoryCarrier_not_empty ratH splitEmpty.left

theorem fieldSingletonEmptyClassifier_append_RatHistoryClassifier_absurd {L R h k : BHist} :
    RatHistoryClassifier h k ->
      fieldSingletonEmptyClassifier (append L h) (append R k) -> False := by
  intro classifier singleton
  have splitLeft := append_eq_empty_iff.mp singleton.left
  exact (RatHistoryClassifier_endpoints_not_empty classifier).left splitLeft.right

theorem fieldSingletonEmptyClassifier_append_RatHistoryLedgerPolicy_absurd
    {L R raw visible : BHist} :
    RatHistoryLedgerPolicy raw visible ->
      fieldSingletonEmptyClassifier (append L raw) (append R visible) -> False := by
  intro ledger singleton
  have splitLeft := append_eq_empty_iff.mp singleton.left
  exact (RatHistoryLedgerPolicy_fieldSingletonEmptyCarrier_endpoints_absurd ledger).left
    splitLeft.right

end BEDC.Derived.FieldUp
