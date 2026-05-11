import BEDC.Derived.DyadicRatCoreUp

namespace BEDC.Derived.DyadicRatCoreUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DyadicRatCoreRegSeqRatWindow_radius_handoff
    {m0 e0 l0 p0 m1 e1 l1 p1 m0' e0' l0' p0' m1' e1' l1' p1' common common'
      scale0 scale0' scale1 scale1' left left' right right' diff diff' abs abs' window
      window' tail refinedExponent refinedLedger : BHist} :
    DyadicRatCoreCarrier m0 e0 l0 p0 ->
      DyadicRatCoreCarrier m1 e1 l1 p1 ->
        hsame m0 m0' ->
          hsame e0 e0' ->
            hsame l0 l0' ->
              hsame p0 p0' ->
                hsame m1 m1' ->
                  hsame e1 e1' ->
                    hsame l1 l1' ->
                      hsame p1 p1' ->
                        PositiveUnaryDenominator common ->
                          hsame common common' ->
                            Cont e0 common scale0 ->
                              Cont e0' common' scale0' ->
                                Cont e1 common scale1 ->
                                  Cont e1' common' scale1' ->
                                    Cont m0 scale0 left ->
                                      Cont m0' scale0' left' ->
                                        Cont m1 scale1 right ->
                                          Cont m1' scale1' right' ->
                                            Cont left right diff ->
                                              Cont left' right' diff' ->
                                                Cont diff common abs ->
                                                  Cont diff' common' abs' ->
                                                    Cont abs p0 window ->
                                                      Cont abs' p0' window' ->
                                                        UnaryHistory tail ->
                                                          Cont e0 tail refinedExponent ->
                                                            Cont refinedExponent m0
                                                              refinedLedger ->
                                                              DyadicRatCoreCarrier m0
                                                                  refinedExponent
                                                                  refinedLedger p0 ∧
                                                                PositiveUnaryDenominator
                                                                  refinedExponent ∧
                                                                  UnaryHistory window' ∧
                                                                    hsame window window' ∧
                                                                      hsame refinedExponent
                                                                        (append e0 tail) := by
  intro carrier0 carrier1 sameM0 sameE0 sameL0 sameP0 sameM1 sameE1 sameL1 sameP1
  intro commonPositive sameCommon scale0Row scale0Row' scale1Row scale1Row'
  intro leftRow leftRow' rightRow rightRow' diffRow diffRow' absRow absRow'
  intro windowRow windowRow' tailUnary refinedExponentRow refinedLedgerRow
  have windowClosure :=
    DyadicRatCoreCarrier_distance_window_transport_closure carrier0 carrier1 sameM0 sameE0
      sameL0 sameP0 sameM1 sameE1 sameL1 sameP1 commonPositive sameCommon scale0Row
      scale0Row' scale1Row scale1Row' leftRow leftRow' rightRow rightRow' diffRow
      diffRow' absRow absRow' windowRow windowRow'
  have radiusObligation :=
    DyadicRatCoreCarrier_monotone_radius_obligation carrier0 tailUnary refinedExponentRow
      refinedLedgerRow
  have windowUnary' : UnaryHistory window' :=
    unary_cont_closed windowClosure.right.right.right.right
      (unary_transport carrier0.right.right.left sameP0) windowRow'
  exact
    ⟨radiusObligation.left,
      radiusObligation.right.left,
      windowUnary',
      windowClosure.left,
      radiusObligation.right.right.left⟩

theorem DyadicRatCoreCarrier_regseqrat_bridge_handoff_exactness
    {mantissa exponent ledger provenance radiusWindow handoffWindow : BHist} :
    DyadicRatCoreCarrier mantissa exponent ledger provenance ->
      Cont ledger exponent radiusWindow ->
        Cont radiusWindow provenance handoffWindow ->
          UnaryHistory radiusWindow ∧ UnaryHistory handoffWindow ∧
            hsame radiusWindow (append ledger exponent) ∧
              hsame handoffWindow (append radiusWindow provenance) ∧
                RatHistoryCarrier mantissa ∧ PositiveUnaryDenominator exponent ∧
                  UnaryHistory ledger := by
  intro carrier radiusRow handoffRow
  have exponentUnary : UnaryHistory exponent :=
    (PositiveUnaryDenominator_unary_and_nonempty carrier.right.left).left
  have radiusUnary : UnaryHistory radiusWindow :=
    unary_cont_closed carrier.right.right.right.right exponentUnary radiusRow
  have handoffUnary : UnaryHistory handoffWindow :=
    unary_cont_closed radiusUnary carrier.right.right.left handoffRow
  exact
    ⟨radiusUnary,
      handoffUnary,
      radiusRow,
      handoffRow,
      carrier.left,
      carrier.right.left,
      carrier.right.right.right.right⟩

theorem DyadicRatCoreCarrier_regseqrat_radius_monotone_window_extraction
    {mantissa exponent ledger provenance tail refinedExponent refinedLedger radiusWindow
      handoffWindow : BHist} :
    DyadicRatCoreCarrier mantissa exponent ledger provenance ->
      UnaryHistory tail ->
        Cont exponent tail refinedExponent ->
          Cont refinedExponent mantissa refinedLedger ->
            Cont refinedLedger provenance radiusWindow ->
              Cont radiusWindow ledger handoffWindow ->
                DyadicRatCoreCarrier mantissa refinedExponent refinedLedger provenance ∧
                  PositiveUnaryDenominator refinedExponent ∧
                    UnaryHistory radiusWindow ∧ UnaryHistory handoffWindow ∧
                      hsame refinedExponent (append exponent tail) ∧
                        hsame radiusWindow (append refinedLedger provenance) ∧
                          hsame handoffWindow (append radiusWindow ledger) := by
  intro carrier tailUnary refinedExponentRow refinedLedgerRow radiusRow handoffRow
  have refined :=
    DyadicRatCoreCarrier_monotone_radius_obligation carrier tailUnary refinedExponentRow
      refinedLedgerRow
  have radiusUnary : UnaryHistory radiusWindow :=
    unary_cont_closed refined.left.right.right.right.right refined.left.right.right.left
      radiusRow
  have handoffUnary : UnaryHistory handoffWindow :=
    unary_cont_closed radiusUnary carrier.right.right.right.right handoffRow
  exact
    ⟨refined.left,
      refined.right.left,
      radiusUnary,
      handoffUnary,
      refined.right.right.left,
      radiusRow,
      handoffRow⟩

end BEDC.Derived.DyadicRatCoreUp
