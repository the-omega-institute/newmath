import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProperMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProperMapUp : Type where
  | mk (X Y F K E H C P N : BHist) : ProperMapUp
  deriving DecidableEq

def properMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: properMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: properMapEncodeBHist h

def properMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (properMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (properMapDecodeBHist tail)

private theorem ProperMapTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, properMapDecodeBHist (properMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def properMapFields : ProperMapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProperMapUp.mk X Y F K E H C P N => [X, Y, F, K, E, H, C, P, N]

def properMapToEventFlow : ProperMapUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (properMapFields x).map properMapEncodeBHist

def properMapEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => properMapEventAtDefault index rest

def properMapFromEventFlow : EventFlow → Option ProperMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ProperMapUp.mk
        (properMapDecodeBHist (properMapEventAtDefault 0 ef))
        (properMapDecodeBHist (properMapEventAtDefault 1 ef))
        (properMapDecodeBHist (properMapEventAtDefault 2 ef))
        (properMapDecodeBHist (properMapEventAtDefault 3 ef))
        (properMapDecodeBHist (properMapEventAtDefault 4 ef))
        (properMapDecodeBHist (properMapEventAtDefault 5 ef))
        (properMapDecodeBHist (properMapEventAtDefault 6 ef))
        (properMapDecodeBHist (properMapEventAtDefault 7 ef))
        (properMapDecodeBHist (properMapEventAtDefault 8 ef)))

private theorem ProperMapTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ProperMapUp, properMapFromEventFlow (properMapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y F K E H C P N =>
      change
        some
          (ProperMapUp.mk
            (properMapDecodeBHist (properMapEncodeBHist X))
            (properMapDecodeBHist (properMapEncodeBHist Y))
            (properMapDecodeBHist (properMapEncodeBHist F))
            (properMapDecodeBHist (properMapEncodeBHist K))
            (properMapDecodeBHist (properMapEncodeBHist E))
            (properMapDecodeBHist (properMapEncodeBHist H))
            (properMapDecodeBHist (properMapEncodeBHist C))
            (properMapDecodeBHist (properMapEncodeBHist P))
            (properMapDecodeBHist (properMapEncodeBHist N))) =
          some (ProperMapUp.mk X Y F K E H C P N)
      rw [ProperMapTasteGate_single_carrier_alignment_decode X,
        ProperMapTasteGate_single_carrier_alignment_decode Y,
        ProperMapTasteGate_single_carrier_alignment_decode F,
        ProperMapTasteGate_single_carrier_alignment_decode K,
        ProperMapTasteGate_single_carrier_alignment_decode E,
        ProperMapTasteGate_single_carrier_alignment_decode H,
        ProperMapTasteGate_single_carrier_alignment_decode C,
        ProperMapTasteGate_single_carrier_alignment_decode P,
        ProperMapTasteGate_single_carrier_alignment_decode N]

private theorem ProperMapTasteGate_single_carrier_alignment_injective
    {x y : ProperMapUp} :
    properMapToEventFlow x = properMapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      properMapFromEventFlow (properMapToEventFlow x) =
        properMapFromEventFlow (properMapToEventFlow y) :=
    congrArg properMapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ProperMapTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ProperMapTasteGate_single_carrier_alignment_round_trip y)))

instance properMapBHistCarrier : BHistCarrier ProperMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := properMapToEventFlow
  fromEventFlow := properMapFromEventFlow

instance properMapChapterTasteGate : ChapterTasteGate ProperMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change properMapFromEventFlow (properMapToEventFlow x) = some x
    exact ProperMapTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ProperMapTasteGate_single_carrier_alignment_injective heq)

theorem ProperMapTasteGate_single_carrier_alignment :
    (∀ h : BHist, properMapDecodeBHist (properMapEncodeBHist h) = h) ∧
      (∀ x : ProperMapUp, properMapFromEventFlow (properMapToEventFlow x) = some x) ∧
      (∀ x y : ProperMapUp, properMapToEventFlow x = properMapToEventFlow y → x = y) ∧
      properMapEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ProperMapTasteGate_single_carrier_alignment_decode
  constructor
  · exact ProperMapTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact ProperMapTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.ProperMapUp
