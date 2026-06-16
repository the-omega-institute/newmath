import BEDC.Derived.NestedClosedBallUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.NestedClosedBallUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem NestedClosedBallRegSeqRatCenterExtraction
    {M K F S R D E H C P N centerWindow dyadicRefinement realSeal : BHist} :
    Cont F S centerWindow ->
      Cont centerWindow R dyadicRefinement ->
        Cont dyadicRefinement D realSeal ->
          UnaryHistory F ->
            UnaryHistory S ->
              UnaryHistory R ->
                UnaryHistory D ->
                  UnaryHistory centerWindow ∧ UnaryHistory dyadicRefinement ∧
                    UnaryHistory realSeal ∧ Cont F S centerWindow ∧
                      Cont centerWindow R dyadicRefinement ∧
                        Cont dyadicRefinement D realSeal ∧
                          TasteGate.NestedClosedBallTasteGate_single_carrier_alignment_fields
                              (TasteGate.NestedClosedBallUp.mk M K F S R D E H C P N) =
                            [M, K, F, S, R, D, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro filterStreamRoute streamReadbackRoute readbackDyadicRoute filterUnary streamUnary
    readbackUnary dyadicUnary
  have centerWindowUnary : UnaryHistory centerWindow :=
    unary_cont_closed filterUnary streamUnary filterStreamRoute
  have dyadicRefinementUnary : UnaryHistory dyadicRefinement :=
    unary_cont_closed centerWindowUnary readbackUnary streamReadbackRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed dyadicRefinementUnary dyadicUnary readbackDyadicRoute
  exact
    ⟨centerWindowUnary, dyadicRefinementUnary, realSealUnary, filterStreamRoute,
      streamReadbackRoute, readbackDyadicRoute, rfl⟩

theorem NestedClosedBallCauchyCenterRoute
    {M K F S R D E H C P N centerWindow readbackWindow dyadicSeal realSeal : BHist} :
    Cont F S centerWindow ->
      Cont centerWindow R readbackWindow ->
        Cont readbackWindow D dyadicSeal ->
          Cont dyadicSeal E realSeal ->
            UnaryHistory F ->
              UnaryHistory S ->
                UnaryHistory R ->
                  UnaryHistory D ->
                    UnaryHistory E ->
                      UnaryHistory centerWindow ∧ UnaryHistory readbackWindow ∧
                        UnaryHistory dyadicSeal ∧ UnaryHistory realSeal ∧
                          Cont F S centerWindow ∧ Cont centerWindow R readbackWindow ∧
                            Cont readbackWindow D dyadicSeal ∧ Cont dyadicSeal E realSeal ∧
                              TasteGate.NestedClosedBallTasteGate_single_carrier_alignment_fields
                                  (TasteGate.NestedClosedBallUp.mk M K F S R D E H C P N) =
                                [M, K, F, S, R, D, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro filterStreamRoute streamReadbackRoute readbackDyadicRoute dyadicRealRoute filterUnary
    streamUnary readbackUnary dyadicUnary realUnary
  have centerWindowUnary : UnaryHistory centerWindow :=
    unary_cont_closed filterUnary streamUnary filterStreamRoute
  have readbackWindowUnary : UnaryHistory readbackWindow :=
    unary_cont_closed centerWindowUnary readbackUnary streamReadbackRoute
  have dyadicSealUnary : UnaryHistory dyadicSeal :=
    unary_cont_closed readbackWindowUnary dyadicUnary readbackDyadicRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed dyadicSealUnary realUnary dyadicRealRoute
  exact
    ⟨centerWindowUnary, readbackWindowUnary, dyadicSealUnary, realSealUnary,
      filterStreamRoute, streamReadbackRoute, readbackDyadicRoute, dyadicRealRoute, rfl⟩

theorem NestedClosedBallNameCertObligations
    {M K F S R D E H C P N filterRead windowRead readbackRead diameterRead sealRead :
      BHist} :
    Cont M K filterRead ->
      Cont filterRead S windowRead ->
        Cont windowRead R readbackRead ->
          Cont readbackRead D diameterRead ->
            Cont diameterRead E sealRead ->
              UnaryHistory M ->
                UnaryHistory K ->
                  UnaryHistory S ->
                    UnaryHistory R ->
                      UnaryHistory D ->
                        UnaryHistory E ->
                          SemanticNameCert
                              (fun row : BHist => hsame row sealRead /\ UnaryHistory row)
                              (fun row : BHist => hsame row sealRead)
                              (fun row : BHist => hsame row sealRead /\
                                Cont diameterRead E sealRead)
                              hsame /\
                            UnaryHistory filterRead /\ UnaryHistory windowRead /\
                              UnaryHistory readbackRead /\ UnaryHistory diameterRead /\
                                UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory SemanticNameCert NameCert
  intro filterRoute windowRoute readbackRoute diameterRoute sealRoute mUnary kUnary sUnary
    rUnary dUnary eUnary
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed mUnary kUnary filterRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed filterUnary sUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have diameterUnary : UnaryHistory diameterRead :=
    unary_cont_closed readbackUnary dUnary diameterRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed diameterUnary eUnary sealRoute
  have sourceSeal : hsame sealRead sealRead /\ UnaryHistory sealRead :=
    ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead /\ UnaryHistory row)
        (fun row : BHist => hsame row sealRead)
        (fun row : BHist => hsame row sealRead /\ Cont diameterRead E sealRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro sealRead sourceSeal
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.left, sealRoute⟩
    }
  exact ⟨cert, filterUnary, windowUnary, readbackUnary, diameterUnary, sealUnary⟩

end BEDC.Derived.NestedClosedBallUp
