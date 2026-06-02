import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCauchyNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCauchyNetUp : Type where
  | mk (D M A N U F S W H C P K : BHist) : LocatedCauchyNetUp
  deriving DecidableEq

def locatedCauchyNetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCauchyNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCauchyNetEncodeBHist h

def locatedCauchyNetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCauchyNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCauchyNetDecodeBHist tail)

private theorem LocatedCauchyNetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, locatedCauchyNetDecodeBHist (locatedCauchyNetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCauchyNetFields : LocatedCauchyNetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCauchyNetUp.mk D M A N U F S W H C P K => [D, M, A, N, U, F, S, W, H, C, P, K]

def locatedCauchyNetToEventFlow : LocatedCauchyNetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedCauchyNetFields x).map locatedCauchyNetEncodeBHist

private def locatedCauchyNetEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedCauchyNetEventAt index rest

def locatedCauchyNetFromEventFlow : EventFlow → Option LocatedCauchyNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (LocatedCauchyNetUp.mk
        (locatedCauchyNetDecodeBHist (locatedCauchyNetEventAt 0 flow))
        (locatedCauchyNetDecodeBHist (locatedCauchyNetEventAt 1 flow))
        (locatedCauchyNetDecodeBHist (locatedCauchyNetEventAt 2 flow))
        (locatedCauchyNetDecodeBHist (locatedCauchyNetEventAt 3 flow))
        (locatedCauchyNetDecodeBHist (locatedCauchyNetEventAt 4 flow))
        (locatedCauchyNetDecodeBHist (locatedCauchyNetEventAt 5 flow))
        (locatedCauchyNetDecodeBHist (locatedCauchyNetEventAt 6 flow))
        (locatedCauchyNetDecodeBHist (locatedCauchyNetEventAt 7 flow))
        (locatedCauchyNetDecodeBHist (locatedCauchyNetEventAt 8 flow))
        (locatedCauchyNetDecodeBHist (locatedCauchyNetEventAt 9 flow))
        (locatedCauchyNetDecodeBHist (locatedCauchyNetEventAt 10 flow))
        (locatedCauchyNetDecodeBHist (locatedCauchyNetEventAt 11 flow)))

private theorem LocatedCauchyNetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedCauchyNetUp,
      locatedCauchyNetFromEventFlow (locatedCauchyNetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D M A N U F S W H C P K =>
      change
        some
          (LocatedCauchyNetUp.mk
            (locatedCauchyNetDecodeBHist (locatedCauchyNetEncodeBHist D))
            (locatedCauchyNetDecodeBHist (locatedCauchyNetEncodeBHist M))
            (locatedCauchyNetDecodeBHist (locatedCauchyNetEncodeBHist A))
            (locatedCauchyNetDecodeBHist (locatedCauchyNetEncodeBHist N))
            (locatedCauchyNetDecodeBHist (locatedCauchyNetEncodeBHist U))
            (locatedCauchyNetDecodeBHist (locatedCauchyNetEncodeBHist F))
            (locatedCauchyNetDecodeBHist (locatedCauchyNetEncodeBHist S))
            (locatedCauchyNetDecodeBHist (locatedCauchyNetEncodeBHist W))
            (locatedCauchyNetDecodeBHist (locatedCauchyNetEncodeBHist H))
            (locatedCauchyNetDecodeBHist (locatedCauchyNetEncodeBHist C))
            (locatedCauchyNetDecodeBHist (locatedCauchyNetEncodeBHist P))
            (locatedCauchyNetDecodeBHist (locatedCauchyNetEncodeBHist K))) =
          some (LocatedCauchyNetUp.mk D M A N U F S W H C P K)
      rw [LocatedCauchyNetTasteGate_single_carrier_alignment_decode_encode D,
        LocatedCauchyNetTasteGate_single_carrier_alignment_decode_encode M,
        LocatedCauchyNetTasteGate_single_carrier_alignment_decode_encode A,
        LocatedCauchyNetTasteGate_single_carrier_alignment_decode_encode N,
        LocatedCauchyNetTasteGate_single_carrier_alignment_decode_encode U,
        LocatedCauchyNetTasteGate_single_carrier_alignment_decode_encode F,
        LocatedCauchyNetTasteGate_single_carrier_alignment_decode_encode S,
        LocatedCauchyNetTasteGate_single_carrier_alignment_decode_encode W,
        LocatedCauchyNetTasteGate_single_carrier_alignment_decode_encode H,
        LocatedCauchyNetTasteGate_single_carrier_alignment_decode_encode C,
        LocatedCauchyNetTasteGate_single_carrier_alignment_decode_encode P,
        LocatedCauchyNetTasteGate_single_carrier_alignment_decode_encode K]

private theorem LocatedCauchyNetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedCauchyNetUp} :
    locatedCauchyNetToEventFlow x = locatedCauchyNetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCauchyNetFromEventFlow (locatedCauchyNetToEventFlow x) =
        locatedCauchyNetFromEventFlow (locatedCauchyNetToEventFlow y) :=
    congrArg locatedCauchyNetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedCauchyNetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedCauchyNetTasteGate_single_carrier_alignment_round_trip y)))

instance locatedCauchyNetBHistCarrier : BHistCarrier LocatedCauchyNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCauchyNetToEventFlow
  fromEventFlow := locatedCauchyNetFromEventFlow

instance locatedCauchyNetChapterTasteGate : ChapterTasteGate LocatedCauchyNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCauchyNetFromEventFlow (locatedCauchyNetToEventFlow x) = some x
    exact LocatedCauchyNetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedCauchyNetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedCauchyNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCauchyNetChapterTasteGate

theorem LocatedCauchyNetTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedCauchyNetDecodeBHist (locatedCauchyNetEncodeBHist h) = h) ∧
      (∀ x : LocatedCauchyNetUp,
        locatedCauchyNetFromEventFlow (locatedCauchyNetToEventFlow x) = some x) ∧
      (∀ x y : LocatedCauchyNetUp,
        locatedCauchyNetToEventFlow x = locatedCauchyNetToEventFlow y → x = y) ∧
      locatedCauchyNetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedCauchyNetTasteGate_single_carrier_alignment_decode_encode,
      LocatedCauchyNetTasteGate_single_carrier_alignment_round_trip,
      fun x y => LocatedCauchyNetTasteGate_single_carrier_alignment_toEventFlow_injective,
      rfl⟩

end BEDC.Derived.LocatedCauchyNetUp
