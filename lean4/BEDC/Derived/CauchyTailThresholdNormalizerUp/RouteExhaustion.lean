import BEDC.Derived.CauchyTailThresholdNormalizerUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyTailThresholdNormalizerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CauchyTailThresholdNormalizerCarrier_route_exhaustion
    (T : CauchyTailThresholdNormalizerUp)
    {S M Theta W0 W1 D R A E H C P L N terminalRead : BHist} :
    cauchyTailThresholdNormalizerFields T =
        [S, M, Theta, W0, W1, D, R, A, E, H, C, P, L, N] →
      UnaryHistory S →
        UnaryHistory M →
          UnaryHistory Theta →
            UnaryHistory W0 →
              UnaryHistory W1 →
                UnaryHistory D →
                  UnaryHistory R →
                    UnaryHistory A →
                      UnaryHistory E →
                        UnaryHistory C →
                          Cont S M Theta →
                            Cont Theta W0 W1 →
                              Cont W1 D R →
                                Cont R A E →
                                  Cont E C terminalRead →
                                    UnaryHistory terminalRead ∧ Cont S M Theta ∧
                                      Cont Theta W0 W1 ∧ Cont W1 D R ∧
                                        Cont R A E ∧ Cont E C terminalRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro fieldRows sourceUnary sealUnary _thresholdUnary _leftWindowUnary rightWindowUnary
    toleranceUnary readbackUnary agreementUnary realUnary replayUnary sourceRoute
    thresholdRoute readbackRoute agreementRoute terminalRoute
  cases T with
  | mk _source _seal _threshold _leftWindow _rightWindow _tolerance _readback
      _agreement _real _transport _replay _provenance _ledger _localName =>
      change
        [_source, _seal, _threshold, _leftWindow, _rightWindow, _tolerance, _readback,
          _agreement, _real, _transport, _replay, _provenance, _ledger, _localName] =
          [S, M, Theta, W0, W1, D, R, A, E, H, C, P, L, N] at fieldRows
      have terminalUnary : UnaryHistory terminalRead :=
        unary_cont_closed realUnary replayUnary terminalRoute
      exact
        ⟨terminalUnary, sourceRoute, thresholdRoute, readbackRoute, agreementRoute,
          terminalRoute⟩

end BEDC.Derived.CauchyTailThresholdNormalizerUp
