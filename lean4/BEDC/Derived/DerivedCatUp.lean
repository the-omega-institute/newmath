import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DerivedCatUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DerivedCatLocalizationRoof_carrier_obligation
    {object morph weak roof localized : BHist} :
    UnaryHistory object -> UnaryHistory morph -> UnaryHistory weak -> Cont object morph roof ->
      Cont roof weak localized ->
        UnaryHistory roof ∧ UnaryHistory localized ∧
          hsame localized (append (append object morph) weak) := by
  intro objectUnary morphUnary weakUnary roofRow localizedRow
  have roofUnary : UnaryHistory roof :=
    unary_cont_closed objectUnary morphUnary roofRow
  have localizedUnary : UnaryHistory localized :=
    unary_cont_closed roofUnary weakUnary localizedRow
  have localizedReadback : hsame localized (append (append object morph) weak) := by
    cases roofRow
    exact localizedRow
  exact And.intro roofUnary (And.intro localizedUnary localizedReadback)

def DerivedCatVisibleLocalizationCarrier (h : BHist) : Prop :=
  ∃ object morphism quasi : BHist,
    UnaryHistory h ∧ UnaryHistory object ∧ UnaryHistory morphism ∧ UnaryHistory quasi ∧
      Cont h object morphism ∧ Cont morphism quasi h

inductive DerivedCatVisibleLocalizationClassifier : BHist -> BHist -> Prop where
  | refl {h : BHist} :
      DerivedCatVisibleLocalizationCarrier h -> DerivedCatVisibleLocalizationClassifier h h
  | category_step {h k witness : BHist} :
      DerivedCatVisibleLocalizationCarrier h -> DerivedCatVisibleLocalizationCarrier k ->
      Cont h k witness -> UnaryHistory witness -> DerivedCatVisibleLocalizationClassifier h k
  | quasi_step {h k witness : BHist} :
      DerivedCatVisibleLocalizationCarrier h -> DerivedCatVisibleLocalizationCarrier k ->
      Cont k h witness -> UnaryHistory witness -> DerivedCatVisibleLocalizationClassifier h k
  | symm {h k : BHist} :
      DerivedCatVisibleLocalizationClassifier h k ->
        DerivedCatVisibleLocalizationClassifier k h
  | trans {h k r : BHist} :
      DerivedCatVisibleLocalizationClassifier h k ->
      DerivedCatVisibleLocalizationClassifier k r ->
        DerivedCatVisibleLocalizationClassifier h r

theorem DerivedCatVisibleLocalizationCarrier_unary {h : BHist} :
    DerivedCatVisibleLocalizationCarrier h -> UnaryHistory h := by
  intro carrier
  cases carrier with
  | intro object data =>
      cases data with
      | intro morphism data =>
          cases data with
          | intro quasi rows =>
              exact rows.left

theorem DerivedCatVisibleLocalizationClassifier_endpoints :
    forall {h k : BHist}, DerivedCatVisibleLocalizationClassifier h k ->
      DerivedCatVisibleLocalizationCarrier h ∧ DerivedCatVisibleLocalizationCarrier k ∧
        UnaryHistory h ∧ UnaryHistory k
  | _, _, DerivedCatVisibleLocalizationClassifier.refl carrier => by
      have carrierUnary := DerivedCatVisibleLocalizationCarrier_unary carrier
      exact And.intro carrier
        (And.intro carrier (And.intro carrierUnary carrierUnary))
  | _, _, DerivedCatVisibleLocalizationClassifier.category_step carrierH carrierK _ _ => by
      have carrierHUnary := DerivedCatVisibleLocalizationCarrier_unary carrierH
      have carrierKUnary := DerivedCatVisibleLocalizationCarrier_unary carrierK
      exact And.intro carrierH
        (And.intro carrierK (And.intro carrierHUnary carrierKUnary))
  | _, _, DerivedCatVisibleLocalizationClassifier.quasi_step carrierH carrierK _ _ => by
      have carrierHUnary := DerivedCatVisibleLocalizationCarrier_unary carrierH
      have carrierKUnary := DerivedCatVisibleLocalizationCarrier_unary carrierK
      exact And.intro carrierH
        (And.intro carrierK (And.intro carrierHUnary carrierKUnary))
  | _, _, DerivedCatVisibleLocalizationClassifier.symm classified => by
      have endpoints := DerivedCatVisibleLocalizationClassifier_endpoints classified
      exact And.intro endpoints.right.left
        (And.intro endpoints.left (And.intro endpoints.right.right.right endpoints.right.right.left))
  | _, _, DerivedCatVisibleLocalizationClassifier.trans classifiedHK classifiedKR => by
      have leftEndpoints := DerivedCatVisibleLocalizationClassifier_endpoints classifiedHK
      have rightEndpoints := DerivedCatVisibleLocalizationClassifier_endpoints classifiedKR
      exact And.intro leftEndpoints.left
        (And.intro rightEndpoints.right.left
          (And.intro leftEndpoints.right.right.left rightEndpoints.right.right.right))

theorem DerivedCatVisibleLocalizationClassifier_name_certificate :
    NameCert DerivedCatVisibleLocalizationCarrier DerivedCatVisibleLocalizationClassifier ∧
      (forall {h k : BHist}, DerivedCatVisibleLocalizationClassifier h k ->
        UnaryHistory h ∧ UnaryHistory k) := by
  have emptyCarrier : DerivedCatVisibleLocalizationCarrier BHist.Empty :=
    Exists.intro BHist.Empty
      (Exists.intro BHist.Empty
        (Exists.intro BHist.Empty
          (And.intro unary_empty
            (And.intro unary_empty
              (And.intro unary_empty
                (And.intro unary_empty
                  (And.intro (cont_left_unit BHist.Empty) (cont_left_unit BHist.Empty))))))))
  constructor
  · exact {
      carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
      equiv_refl := by
        intro h carrier
        exact DerivedCatVisibleLocalizationClassifier.refl carrier
      equiv_symm := by
        intro h k classified
        exact DerivedCatVisibleLocalizationClassifier.symm classified
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact DerivedCatVisibleLocalizationClassifier.trans classifiedHK classifiedKR
      carrier_respects_equiv := by
        intro h k classified _carrierH
        exact (DerivedCatVisibleLocalizationClassifier_endpoints classified).right.left
    }
  · intro h k classified
    exact (DerivedCatVisibleLocalizationClassifier_endpoints classified).right.right

end BEDC.Derived.DerivedCatUp
