import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRegularizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRegularizationUp : Type where
  | mk (S M A W R D E H C P N : BHist) : LocatedRegularizationUp
  deriving DecidableEq

def locatedRegularizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRegularizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRegularizationEncodeBHist h

def locatedRegularizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRegularizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRegularizationDecodeBHist tail)

private theorem locatedRegularizationDecode_encode :
    ∀ h : BHist,
      locatedRegularizationDecodeBHist (locatedRegularizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRegularizationFields : LocatedRegularizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRegularizationUp.mk S M A W R D E H C P N => [S, M, A, W, R, D, E, H, C, P, N]

def locatedRegularizationToEventFlow : LocatedRegularizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedRegularizationFields x).map locatedRegularizationEncodeBHist

private def locatedRegularizationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedRegularizationEventAtDefault index rest

def locatedRegularizationFromEventFlow (ef : EventFlow) : Option LocatedRegularizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedRegularizationUp.mk
      (locatedRegularizationDecodeBHist (locatedRegularizationEventAtDefault 0 ef))
      (locatedRegularizationDecodeBHist (locatedRegularizationEventAtDefault 1 ef))
      (locatedRegularizationDecodeBHist (locatedRegularizationEventAtDefault 2 ef))
      (locatedRegularizationDecodeBHist (locatedRegularizationEventAtDefault 3 ef))
      (locatedRegularizationDecodeBHist (locatedRegularizationEventAtDefault 4 ef))
      (locatedRegularizationDecodeBHist (locatedRegularizationEventAtDefault 5 ef))
      (locatedRegularizationDecodeBHist (locatedRegularizationEventAtDefault 6 ef))
      (locatedRegularizationDecodeBHist (locatedRegularizationEventAtDefault 7 ef))
      (locatedRegularizationDecodeBHist (locatedRegularizationEventAtDefault 8 ef))
      (locatedRegularizationDecodeBHist (locatedRegularizationEventAtDefault 9 ef))
      (locatedRegularizationDecodeBHist (locatedRegularizationEventAtDefault 10 ef)))

private theorem locatedRegularization_round_trip :
    ∀ x : LocatedRegularizationUp,
      locatedRegularizationFromEventFlow (locatedRegularizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M A W R D E H C P N =>
      change
        some
          (LocatedRegularizationUp.mk
            (locatedRegularizationDecodeBHist (locatedRegularizationEncodeBHist S))
            (locatedRegularizationDecodeBHist (locatedRegularizationEncodeBHist M))
            (locatedRegularizationDecodeBHist (locatedRegularizationEncodeBHist A))
            (locatedRegularizationDecodeBHist (locatedRegularizationEncodeBHist W))
            (locatedRegularizationDecodeBHist (locatedRegularizationEncodeBHist R))
            (locatedRegularizationDecodeBHist (locatedRegularizationEncodeBHist D))
            (locatedRegularizationDecodeBHist (locatedRegularizationEncodeBHist E))
            (locatedRegularizationDecodeBHist (locatedRegularizationEncodeBHist H))
            (locatedRegularizationDecodeBHist (locatedRegularizationEncodeBHist C))
            (locatedRegularizationDecodeBHist (locatedRegularizationEncodeBHist P))
            (locatedRegularizationDecodeBHist (locatedRegularizationEncodeBHist N))) =
          some (LocatedRegularizationUp.mk S M A W R D E H C P N)
      rw [locatedRegularizationDecode_encode S, locatedRegularizationDecode_encode M,
        locatedRegularizationDecode_encode A, locatedRegularizationDecode_encode W,
        locatedRegularizationDecode_encode R, locatedRegularizationDecode_encode D,
        locatedRegularizationDecode_encode E, locatedRegularizationDecode_encode H,
        locatedRegularizationDecode_encode C, locatedRegularizationDecode_encode P,
        locatedRegularizationDecode_encode N]

private theorem locatedRegularizationToEventFlow_injective
    {x y : LocatedRegularizationUp} :
    locatedRegularizationToEventFlow x = locatedRegularizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRegularizationFromEventFlow (locatedRegularizationToEventFlow x) =
        locatedRegularizationFromEventFlow (locatedRegularizationToEventFlow y) :=
    congrArg locatedRegularizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedRegularization_round_trip x).symm
      (Eq.trans hread (locatedRegularization_round_trip y)))

instance locatedRegularizationBHistCarrier :
    BHistCarrier LocatedRegularizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRegularizationToEventFlow
  fromEventFlow := locatedRegularizationFromEventFlow

instance locatedRegularizationChapterTasteGate :
    ChapterTasteGate LocatedRegularizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedRegularizationFromEventFlow (locatedRegularizationToEventFlow x) = some x
    exact locatedRegularization_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedRegularizationToEventFlow_injective heq)

theorem LocatedRegularizationTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedRegularizationDecodeBHist (locatedRegularizationEncodeBHist h) = h) ∧
      (∀ x : LocatedRegularizationUp,
        locatedRegularizationFromEventFlow (locatedRegularizationToEventFlow x) = some x) ∧
      (∀ x y : LocatedRegularizationUp,
        locatedRegularizationToEventFlow x = locatedRegularizationToEventFlow y → x = y) ∧
      locatedRegularizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨locatedRegularizationDecode_encode,
      locatedRegularization_round_trip,
      fun _ _ heq => locatedRegularizationToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.LocatedRegularizationUp
