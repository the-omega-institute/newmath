import BEDC.FKernel.Cont
import BEDC.FKernel.Unary
import BEDC.Derived.BolzanoWeierstrassSelectorUp.TasteGate

namespace BEDC.Derived.BolzanoWeierstrassSelectorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassSelectorClusterRoute (x : BolzanoWeierstrassSelectorUp) :
    (exists boundedWindow monotoneSelector cofinalEvidence selectedWindow dyadicLedger
        regularHandoff realSeal transport route provenance name : BHist,
        x =
          BolzanoWeierstrassSelectorUp.mk boundedWindow monotoneSelector cofinalEvidence
            selectedWindow dyadicLedger regularHandoff realSeal transport route provenance name ∧
          bolzanoWeierstrassSelectorFields x =
            [boundedWindow, monotoneSelector, cofinalEvidence, selectedWindow, dyadicLedger,
              regularHandoff, realSeal, transport, route, provenance, name] ∧
          bolzanoWeierstrassSelectorDecodeBHist
              (bolzanoWeierstrassSelectorEncodeBHist selectedWindow) =
            selectedWindow ∧
          bolzanoWeierstrassSelectorDecodeBHist
              (bolzanoWeierstrassSelectorEncodeBHist dyadicLedger) =
            dyadicLedger ∧
          bolzanoWeierstrassSelectorDecodeBHist
              (bolzanoWeierstrassSelectorEncodeBHist regularHandoff) =
            regularHandoff ∧
          bolzanoWeierstrassSelectorDecodeBHist
              (bolzanoWeierstrassSelectorEncodeBHist realSeal) =
            realSeal) ∧
      bolzanoWeierstrassSelectorEncodeBHist (BHist.e1 (BHist.e1 BHist.Empty)) =
        [BMark.b1, BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  have decodeEncode :
      ∀ h : BHist,
        bolzanoWeierstrassSelectorDecodeBHist
            (bolzanoWeierstrassSelectorEncodeBHist h) =
          h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  cases x with
  | mk boundedWindow monotoneSelector cofinalEvidence selectedWindow dyadicLedger
      regularHandoff realSeal transport route provenance name =>
      constructor
      · exact
          ⟨boundedWindow, monotoneSelector, cofinalEvidence, selectedWindow, dyadicLedger,
            regularHandoff, realSeal, transport, route, provenance, name, rfl, rfl,
            decodeEncode selectedWindow, decodeEncode dyadicLedger, decodeEncode regularHandoff,
            decodeEncode realSeal⟩
      · rfl

theorem BolzanoWeierstrassSelectorFiniteWindowInduction
    (x : BolzanoWeierstrassSelectorUp) :
    ∃ boundedWindow monotoneSelector cofinalEvidence selectedWindow dyadicLedger regularHandoff
      realSeal transport route provenance name : BHist,
      x =
        BolzanoWeierstrassSelectorUp.mk boundedWindow monotoneSelector cofinalEvidence
          selectedWindow dyadicLedger regularHandoff realSeal transport route provenance name ∧
        bolzanoWeierstrassSelectorFields x =
          [boundedWindow, monotoneSelector, cofinalEvidence, selectedWindow, dyadicLedger,
            regularHandoff, realSeal, transport, route, provenance, name] ∧
          hsame transport transport ∧
            bolzanoWeierstrassSelectorDecodeBHist
                (bolzanoWeierstrassSelectorEncodeBHist selectedWindow) =
              selectedWindow ∧
              bolzanoWeierstrassSelectorDecodeBHist
                  (bolzanoWeierstrassSelectorEncodeBHist realSeal) =
                realSeal := by
  -- BEDC touchpoint anchor: BHist BMark hsame
  have decodeEncode :
      ∀ h : BHist,
        bolzanoWeierstrassSelectorDecodeBHist
            (bolzanoWeierstrassSelectorEncodeBHist h) =
          h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  cases x with
  | mk boundedWindow monotoneSelector cofinalEvidence selectedWindow dyadicLedger regularHandoff
      realSeal transport route provenance name =>
      exact
        ⟨boundedWindow, monotoneSelector, cofinalEvidence, selectedWindow, dyadicLedger,
          regularHandoff, realSeal, transport, route, provenance, name, rfl, rfl,
          hsame_refl transport, decodeEncode selectedWindow, decodeEncode realSeal⟩

theorem BolzanoWeierstrassSelectorFiniteMonotoneInduction
    {boundedWindow monotoneSelector cofinalEvidence selectedWindow dyadicLedger regularHandoff
      realSeal transport route provenance name inductionStep : BHist} :
    Cont boundedWindow monotoneSelector selectedWindow ->
      Cont selectedWindow cofinalEvidence inductionStep ->
        UnaryHistory boundedWindow ->
          UnaryHistory monotoneSelector ->
            UnaryHistory cofinalEvidence ->
              UnaryHistory selectedWindow ∧ UnaryHistory inductionStep ∧
                Cont boundedWindow monotoneSelector selectedWindow ∧
                  Cont selectedWindow cofinalEvidence inductionStep ∧
                    bolzanoWeierstrassSelectorFields
                        (BolzanoWeierstrassSelectorUp.mk boundedWindow monotoneSelector
                          cofinalEvidence selectedWindow dyadicLedger regularHandoff realSeal
                          transport route provenance name) =
                      [boundedWindow, monotoneSelector, cofinalEvidence, selectedWindow,
                        dyadicLedger, regularHandoff, realSeal, transport, route, provenance,
                        name] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro selectedRoute inductionRoute boundedUnary selectorUnary cofinalUnary
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed boundedUnary selectorUnary selectedRoute
  have inductionUnary : UnaryHistory inductionStep :=
    unary_cont_closed selectedUnary cofinalUnary inductionRoute
  exact ⟨selectedUnary, inductionUnary, selectedRoute, inductionRoute, rfl⟩

end BEDC.Derived.BolzanoWeierstrassSelectorUp
