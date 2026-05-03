import BEDC.Derived.FieldUp.RatDenomUnit

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem field_rat_denominator_empty_unit_strict_product_support_exactness {h k : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k ->
      (RatHistoryCarrier (append h k) ↔ RatHistoryCarrier h ∨ RatHistoryCarrier k) := by
  intro carrierH carrierK
  constructor
  · intro productRat
    have productNonempty : hsame (append h k) BHist.Empty -> False :=
      RatHistoryCarrier_not_empty productRat
    exact Iff.mp (field_rat_denominator_empty_unit_product_nonempty_iff carrierH carrierK)
      productNonempty
  · intro support
    have productCarrier : RatDenomUnitCarrier (append h k) :=
      RatDenomUnitCarrier_continuation_closed carrierH carrierK (cont_intro rfl)
    have productNonempty : hsame (append h k) BHist.Empty -> False :=
      Iff.mpr (field_rat_denominator_empty_unit_product_nonempty_iff carrierH carrierK) support
    exact RatDenomUnitCarrier_nonempty_rat productCarrier productNonempty

end BEDC.Derived.FieldUp
