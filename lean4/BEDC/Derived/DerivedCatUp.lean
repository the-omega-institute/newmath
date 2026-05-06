import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DerivedCatUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.DerivedCatUp
