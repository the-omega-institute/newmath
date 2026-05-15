import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RegularCauchyWitnessScheduleUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def RegularCauchyWitnessScheduleCarrier
    (_family modulus window dyadic readback sealRow _transport route provenance name : BHist) : Prop :=
  Cont modulus window route ∧ Cont window dyadic readback ∧ hsame sealRow readback ∧
    hsame name name

theorem RegularCauchyWitnessScheduleSemanticNameCert :
    SemanticNameCert
      (fun row : BHist =>
        RegularCauchyWitnessScheduleCarrier BHist.Empty BHist.Empty BHist.Empty BHist.Empty row
          row BHist.Empty BHist.Empty BHist.Empty row)
      (fun row : BHist =>
        RegularCauchyWitnessScheduleCarrier BHist.Empty BHist.Empty BHist.Empty BHist.Empty row
          row BHist.Empty BHist.Empty BHist.Empty row)
      (fun row : BHist =>
        RegularCauchyWitnessScheduleCarrier BHist.Empty BHist.Empty BHist.Empty BHist.Empty row
          row BHist.Empty BHist.Empty BHist.Empty row)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert RegularCauchyWitnessScheduleCarrier
  let Carrier : BHist -> Prop := fun row : BHist =>
    RegularCauchyWitnessScheduleCarrier BHist.Empty BHist.Empty BHist.Empty BHist.Empty row
      row BHist.Empty BHist.Empty BHist.Empty row
  have modulusWindowRoute : Cont BHist.Empty BHist.Empty BHist.Empty := by
    rfl
  have windowDyadicReadback : Cont BHist.Empty BHist.Empty BHist.Empty := by
    rfl
  have witness : Carrier BHist.Empty := by
    exact And.intro modulusWindowRoute
      (And.intro windowDyadicReadback (And.intro (hsame_refl BHist.Empty) rfl))
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty witness
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

theorem RegularCauchyWitnessScheduleCarrier_window_modulus_alignment
    {family modulus window dyadic readback sealRow transport route provenance name
      scheduledWindow : BHist} :
    RegularCauchyWitnessScheduleCarrier family modulus window dyadic readback sealRow transport
        route provenance name ->
      Cont modulus window scheduledWindow ->
        Cont window dyadic readback /\ hsame scheduledWindow route /\ hsame sealRow readback := by
  intro carrier scheduledWindowRead
  obtain ⟨modulusWindowRoute, windowDyadicReadback, sealReadback, _nameSame⟩ := carrier
  exact
    ⟨windowDyadicReadback, hsame_symm (cont_deterministic modulusWindowRoute scheduledWindowRead),
      sealReadback⟩

theorem RegularCauchyWitnessScheduleCarrier_diagonal_readback_lock
    {family modulus window dyadic readback sealRow transport route provenance name scheduledWindow
      scheduledRead : BHist} :
    RegularCauchyWitnessScheduleCarrier family modulus window dyadic readback sealRow transport
        route provenance name ->
      Cont modulus window scheduledWindow ->
        Cont window dyadic scheduledRead ->
          hsame scheduledWindow route ∧ hsame scheduledRead readback ∧
            hsame sealRow scheduledRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont RegularCauchyWitnessScheduleCarrier
  intro carrier scheduledWindowRead scheduledReadRoute
  obtain ⟨modulusWindowRoute, windowDyadicReadback, sealReadback, _nameSame⟩ := carrier
  have scheduledWindowRoute : hsame scheduledWindow route :=
    hsame_symm (cont_deterministic modulusWindowRoute scheduledWindowRead)
  have scheduledReadReadback : hsame scheduledRead readback :=
    hsame_symm (cont_deterministic windowDyadicReadback scheduledReadRoute)
  have sealScheduledRead : hsame sealRow scheduledRead :=
    hsame_trans sealReadback (hsame_symm scheduledReadReadback)
  exact ⟨scheduledWindowRoute, scheduledReadReadback, sealScheduledRead⟩

theorem RegularCauchyWitnessScheduleCarrier_seal_source_determinacy
    {family modulus window dyadic readback sealRow transport route provenance name readbackPrime
      sealRowPrime : BHist} :
    RegularCauchyWitnessScheduleCarrier family modulus window dyadic readback sealRow transport
        route provenance name →
      Cont window dyadic readbackPrime →
        hsame sealRowPrime readbackPrime →
          hsame sealRow sealRowPrime := by
  -- BEDC touchpoint anchor: BHist hsame Cont RegularCauchyWitnessScheduleCarrier
  intro carrier alternateReadback alternateSeal
  obtain ⟨_modulusWindowRoute, windowDyadicReadback, sealReadback, _nameSame⟩ := carrier
  have readbackSame : hsame readback readbackPrime :=
    cont_deterministic windowDyadicReadback alternateReadback
  exact hsame_trans sealReadback (hsame_trans readbackSame (hsame_symm alternateSeal))

end BEDC.Derived.RegularCauchyWitnessScheduleUp
