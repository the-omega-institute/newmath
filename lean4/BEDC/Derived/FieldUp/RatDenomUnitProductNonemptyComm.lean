import BEDC.Derived.FieldUp.RatDenomUnit

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem field_rat_denominator_empty_unit_product_nonempty_comm_iff {h k : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier k ->
      ((hsame (append h k) BHist.Empty -> False) ↔
        (hsame (append k h) BHist.Empty -> False)) := by
  intro carrierH carrierK
  have leftSupport := field_rat_denominator_empty_unit_product_nonempty_iff carrierH carrierK
  have rightSupport := field_rat_denominator_empty_unit_product_nonempty_iff carrierK carrierH
  constructor
  · intro leftNonempty
    have factors : RatHistoryCarrier h ∨ RatHistoryCarrier k := leftSupport.mp leftNonempty
    exact rightSupport.mpr (Or.elim factors (fun ratH => Or.inr ratH) (fun ratK => Or.inl ratK))
  · intro rightNonempty
    have factors : RatHistoryCarrier k ∨ RatHistoryCarrier h := rightSupport.mp rightNonempty
    exact leftSupport.mpr (Or.elim factors (fun ratK => Or.inr ratK) (fun ratH => Or.inl ratH))

end BEDC.Derived.FieldUp
