import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCompletionUniversalPropertyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCompletionUniversalPropertyUp : Type where
  | mk (L U E Q M H C P N : BHist) : LocatedCompletionUniversalPropertyUp
  deriving DecidableEq

def locatedCompletionUniversalPropertyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCompletionUniversalPropertyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCompletionUniversalPropertyEncodeBHist h

def locatedCompletionUniversalPropertyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCompletionUniversalPropertyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCompletionUniversalPropertyDecodeBHist tail)

private theorem locatedCompletionUniversalProperty_decode_encode :
    ∀ h : BHist,
      locatedCompletionUniversalPropertyDecodeBHist
        (locatedCompletionUniversalPropertyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCompletionUniversalPropertyFields :
    LocatedCompletionUniversalPropertyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCompletionUniversalPropertyUp.mk L U E Q M H C P N =>
      [L, U, E, Q, M, H, C, P, N]

def locatedCompletionUniversalPropertyToEventFlow :
    LocatedCompletionUniversalPropertyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (locatedCompletionUniversalPropertyFields x).map
      locatedCompletionUniversalPropertyEncodeBHist

private def locatedCompletionUniversalPropertyEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      locatedCompletionUniversalPropertyEventAtDefault index rest

def locatedCompletionUniversalPropertyFromEventFlow
    (ef : EventFlow) : Option LocatedCompletionUniversalPropertyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCompletionUniversalPropertyUp.mk
      (locatedCompletionUniversalPropertyDecodeBHist
        (locatedCompletionUniversalPropertyEventAtDefault 0 ef))
      (locatedCompletionUniversalPropertyDecodeBHist
        (locatedCompletionUniversalPropertyEventAtDefault 1 ef))
      (locatedCompletionUniversalPropertyDecodeBHist
        (locatedCompletionUniversalPropertyEventAtDefault 2 ef))
      (locatedCompletionUniversalPropertyDecodeBHist
        (locatedCompletionUniversalPropertyEventAtDefault 3 ef))
      (locatedCompletionUniversalPropertyDecodeBHist
        (locatedCompletionUniversalPropertyEventAtDefault 4 ef))
      (locatedCompletionUniversalPropertyDecodeBHist
        (locatedCompletionUniversalPropertyEventAtDefault 5 ef))
      (locatedCompletionUniversalPropertyDecodeBHist
        (locatedCompletionUniversalPropertyEventAtDefault 6 ef))
      (locatedCompletionUniversalPropertyDecodeBHist
        (locatedCompletionUniversalPropertyEventAtDefault 7 ef))
      (locatedCompletionUniversalPropertyDecodeBHist
        (locatedCompletionUniversalPropertyEventAtDefault 8 ef)))

private theorem locatedCompletionUniversalProperty_round_trip :
    ∀ x : LocatedCompletionUniversalPropertyUp,
      locatedCompletionUniversalPropertyFromEventFlow
        (locatedCompletionUniversalPropertyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U E Q M H C P N =>
      change
        some
          (LocatedCompletionUniversalPropertyUp.mk
            (locatedCompletionUniversalPropertyDecodeBHist
              (locatedCompletionUniversalPropertyEncodeBHist L))
            (locatedCompletionUniversalPropertyDecodeBHist
              (locatedCompletionUniversalPropertyEncodeBHist U))
            (locatedCompletionUniversalPropertyDecodeBHist
              (locatedCompletionUniversalPropertyEncodeBHist E))
            (locatedCompletionUniversalPropertyDecodeBHist
              (locatedCompletionUniversalPropertyEncodeBHist Q))
            (locatedCompletionUniversalPropertyDecodeBHist
              (locatedCompletionUniversalPropertyEncodeBHist M))
            (locatedCompletionUniversalPropertyDecodeBHist
              (locatedCompletionUniversalPropertyEncodeBHist H))
            (locatedCompletionUniversalPropertyDecodeBHist
              (locatedCompletionUniversalPropertyEncodeBHist C))
            (locatedCompletionUniversalPropertyDecodeBHist
              (locatedCompletionUniversalPropertyEncodeBHist P))
            (locatedCompletionUniversalPropertyDecodeBHist
              (locatedCompletionUniversalPropertyEncodeBHist N))) =
          some (LocatedCompletionUniversalPropertyUp.mk L U E Q M H C P N)
      rw [locatedCompletionUniversalProperty_decode_encode L,
        locatedCompletionUniversalProperty_decode_encode U,
        locatedCompletionUniversalProperty_decode_encode E,
        locatedCompletionUniversalProperty_decode_encode Q,
        locatedCompletionUniversalProperty_decode_encode M,
        locatedCompletionUniversalProperty_decode_encode H,
        locatedCompletionUniversalProperty_decode_encode C,
        locatedCompletionUniversalProperty_decode_encode P,
        locatedCompletionUniversalProperty_decode_encode N]

private theorem locatedCompletionUniversalPropertyToEventFlow_injective
    {x y : LocatedCompletionUniversalPropertyUp} :
    locatedCompletionUniversalPropertyToEventFlow x =
      locatedCompletionUniversalPropertyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCompletionUniversalPropertyFromEventFlow
          (locatedCompletionUniversalPropertyToEventFlow x) =
        locatedCompletionUniversalPropertyFromEventFlow
          (locatedCompletionUniversalPropertyToEventFlow y) :=
    congrArg locatedCompletionUniversalPropertyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (locatedCompletionUniversalProperty_round_trip x).symm
      (Eq.trans hread (locatedCompletionUniversalProperty_round_trip y)))

instance locatedCompletionUniversalPropertyBHistCarrier :
    BHistCarrier LocatedCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCompletionUniversalPropertyToEventFlow
  fromEventFlow := locatedCompletionUniversalPropertyFromEventFlow

instance locatedCompletionUniversalPropertyChapterTasteGate :
    ChapterTasteGate LocatedCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedCompletionUniversalPropertyFromEventFlow
        (locatedCompletionUniversalPropertyToEventFlow x) = some x
    exact locatedCompletionUniversalProperty_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedCompletionUniversalPropertyToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedCompletionUniversalPropertyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCompletionUniversalPropertyChapterTasteGate

theorem LocatedCompletionUniversalPropertyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        locatedCompletionUniversalPropertyDecodeBHist
          (locatedCompletionUniversalPropertyEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedCompletionUniversalPropertyUp) ∧
      Nonempty (ChapterTasteGate LocatedCompletionUniversalPropertyUp) ∧
      locatedCompletionUniversalPropertyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨locatedCompletionUniversalProperty_decode_encode,
      ⟨locatedCompletionUniversalPropertyBHistCarrier⟩,
      ⟨locatedCompletionUniversalPropertyChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedCompletionUniversalPropertyUp
