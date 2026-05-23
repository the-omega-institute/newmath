import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BolzanoWeierstrassSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BolzanoWeierstrassSelectorUp : Type where
  | mk :
      (boundedWindow monotoneSelector cofinalEvidence selectedWindow dyadicLedger
        regularHandoff realSeal transport route provenance name : BHist) →
      BolzanoWeierstrassSelectorUp
  deriving DecidableEq

def bolzanoWeierstrassSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bolzanoWeierstrassSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bolzanoWeierstrassSelectorEncodeBHist h

def bolzanoWeierstrassSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bolzanoWeierstrassSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bolzanoWeierstrassSelectorDecodeBHist tail)

private theorem bolzanoWeierstrassSelector_decode_encode_bhist :
    ∀ h : BHist,
      bolzanoWeierstrassSelectorDecodeBHist
          (bolzanoWeierstrassSelectorEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bolzanoWeierstrassSelectorFields :
    BolzanoWeierstrassSelectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BolzanoWeierstrassSelectorUp.mk boundedWindow monotoneSelector cofinalEvidence
      selectedWindow dyadicLedger regularHandoff realSeal transport route provenance name =>
      [boundedWindow, monotoneSelector, cofinalEvidence, selectedWindow, dyadicLedger,
        regularHandoff, realSeal, transport, route, provenance, name]

def bolzanoWeierstrassSelectorToEventFlow :
    BolzanoWeierstrassSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bolzanoWeierstrassSelectorFields x).map bolzanoWeierstrassSelectorEncodeBHist

def bolzanoWeierstrassSelectorFromEventFlow :
    EventFlow → Option BolzanoWeierstrassSelectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | boundedWindow :: monotoneSelector :: cofinalEvidence :: selectedWindow ::
      dyadicLedger :: regularHandoff :: realSeal :: transport :: route :: provenance ::
        name :: [] =>
      some
        (BolzanoWeierstrassSelectorUp.mk
          (bolzanoWeierstrassSelectorDecodeBHist boundedWindow)
          (bolzanoWeierstrassSelectorDecodeBHist monotoneSelector)
          (bolzanoWeierstrassSelectorDecodeBHist cofinalEvidence)
          (bolzanoWeierstrassSelectorDecodeBHist selectedWindow)
          (bolzanoWeierstrassSelectorDecodeBHist dyadicLedger)
          (bolzanoWeierstrassSelectorDecodeBHist regularHandoff)
          (bolzanoWeierstrassSelectorDecodeBHist realSeal)
          (bolzanoWeierstrassSelectorDecodeBHist transport)
          (bolzanoWeierstrassSelectorDecodeBHist route)
          (bolzanoWeierstrassSelectorDecodeBHist provenance)
          (bolzanoWeierstrassSelectorDecodeBHist name))
  | _ => none

private theorem bolzanoWeierstrassSelector_round_trip :
    ∀ x : BolzanoWeierstrassSelectorUp,
      bolzanoWeierstrassSelectorFromEventFlow
          (bolzanoWeierstrassSelectorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk boundedWindow monotoneSelector cofinalEvidence selectedWindow dyadicLedger
      regularHandoff realSeal transport route provenance name =>
      simp only [bolzanoWeierstrassSelectorToEventFlow,
        bolzanoWeierstrassSelectorFields, bolzanoWeierstrassSelectorFromEventFlow,
        List.map_cons, List.map_nil, bolzanoWeierstrassSelector_decode_encode_bhist]

private theorem bolzanoWeierstrassSelectorToEventFlow_injective
    {x y : BolzanoWeierstrassSelectorUp} :
    bolzanoWeierstrassSelectorToEventFlow x =
        bolzanoWeierstrassSelectorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bolzanoWeierstrassSelectorFromEventFlow
          (bolzanoWeierstrassSelectorToEventFlow x) =
        bolzanoWeierstrassSelectorFromEventFlow
          (bolzanoWeierstrassSelectorToEventFlow y) :=
    congrArg bolzanoWeierstrassSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bolzanoWeierstrassSelector_round_trip x).symm
      (Eq.trans hread (bolzanoWeierstrassSelector_round_trip y)))

instance bolzanoWeierstrassSelectorBHistCarrier :
    BHistCarrier BolzanoWeierstrassSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bolzanoWeierstrassSelectorToEventFlow
  fromEventFlow := bolzanoWeierstrassSelectorFromEventFlow

instance bolzanoWeierstrassSelectorChapterTasteGate :
    ChapterTasteGate BolzanoWeierstrassSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bolzanoWeierstrassSelectorFromEventFlow
          (bolzanoWeierstrassSelectorToEventFlow x) =
        some x
    exact bolzanoWeierstrassSelector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bolzanoWeierstrassSelectorToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BolzanoWeierstrassSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bolzanoWeierstrassSelectorChapterTasteGate

theorem BolzanoWeierstrassSelectorSubsequenceHandoff (x : BolzanoWeierstrassSelectorUp) :
    (exists boundedWindow monotoneSelector cofinalEvidence selectedWindow dyadicLedger
        regularHandoff realSeal transport route provenance name : BHist,
        x =
          BolzanoWeierstrassSelectorUp.mk boundedWindow monotoneSelector cofinalEvidence
            selectedWindow dyadicLedger regularHandoff realSeal transport route provenance name ∧
          bolzanoWeierstrassSelectorFields x =
            [boundedWindow, monotoneSelector, cofinalEvidence, selectedWindow, dyadicLedger,
              regularHandoff, realSeal, transport, route, provenance, name]) ∧
      bolzanoWeierstrassSelectorEncodeBHist BHist.Empty = ([] : RawEvent) ∧
        bolzanoWeierstrassSelectorEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
          bolzanoWeierstrassSelectorDecodeBHist
              (bolzanoWeierstrassSelectorEncodeBHist BHist.Empty) =
            BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  cases x with
  | mk boundedWindow monotoneSelector cofinalEvidence selectedWindow dyadicLedger
      regularHandoff realSeal transport route provenance name =>
      constructor
      · exact
          ⟨boundedWindow, monotoneSelector, cofinalEvidence, selectedWindow, dyadicLedger,
            regularHandoff, realSeal, transport, route, provenance, name, rfl, rfl⟩
      · constructor
        · rfl
        · constructor
          · rfl
          · rfl

end BEDC.Derived.BolzanoWeierstrassSelectorUp
