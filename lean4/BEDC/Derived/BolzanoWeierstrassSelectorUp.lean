import BEDC.Derived.BolzanoWeierstrassSelectorUp.TasteGate

namespace BEDC.Derived.BolzanoWeierstrassSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

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

end BEDC.Derived.BolzanoWeierstrassSelectorUp
