import BEDC.Derived.DyadicRatCoreUp

namespace BEDC.Derived.DyadicRatCoreUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DyadicRatCoreCarrier_common_scale_window_four_face_pullback_correspondence
    {mantissa exponent ledger provenance streamFace regFace realFace terminal : BHist} :
    DyadicRatCoreCarrier mantissa exponent ledger provenance ->
      Cont ledger provenance streamFace ->
        Cont streamFace mantissa regFace ->
          Cont regFace provenance realFace ->
            Cont realFace BHist.Empty terminal ->
              UnaryHistory ledger ∧ UnaryHistory streamFace ∧ UnaryHistory regFace ∧
                UnaryHistory realFace ∧ UnaryHistory terminal ∧
                  Cont ledger provenance streamFace ∧ Cont streamFace mantissa regFace ∧
                    Cont regFace provenance realFace ∧ Cont realFace BHist.Empty terminal := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory PositiveUnaryDenominator
  intro carrier streamRoute regRoute realRoute terminalRoute
  have mantissaPositive : PositiveUnaryDenominator mantissa :=
    RatHistoryCarrier_iff_positive_denominator.mp carrier.left
  have mantissaUnary : UnaryHistory mantissa :=
    (PositiveUnaryDenominator_unary_and_nonempty mantissaPositive).left
  have ledgerUnary : UnaryHistory ledger := carrier.right.right.right.right
  have provenanceUnary : UnaryHistory provenance := carrier.right.right.left
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed ledgerUnary provenanceUnary streamRoute
  have regUnary : UnaryHistory regFace :=
    unary_cont_closed streamUnary mantissaUnary regRoute
  have realUnary : UnaryHistory realFace :=
    unary_cont_closed regUnary provenanceUnary realRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed realUnary unary_empty terminalRoute
  exact
    ⟨ledgerUnary, streamUnary, regUnary, realUnary, terminalUnary, streamRoute, regRoute,
      realRoute, terminalRoute⟩

end BEDC.Derived.DyadicRatCoreUp
