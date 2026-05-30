import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealRootIsolationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealRootIsolationUp : Type where
  | mk (P E S B D T L H C Q N : BHist) : RealRootIsolationUp
  deriving DecidableEq

def realRootIsolationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realRootIsolationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realRootIsolationEncodeBHist h

def realRootIsolationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realRootIsolationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realRootIsolationDecodeBHist tail)

private theorem RealRootIsolationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realRootIsolationDecodeBHist (realRootIsolationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realRootIsolationFields : RealRootIsolationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealRootIsolationUp.mk P E S B D T L H C Q N => [P, E, S, B, D, T, L, H, C, Q, N]

def realRootIsolationToEventFlow : RealRootIsolationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realRootIsolationFields x).map realRootIsolationEncodeBHist

private def realRootIsolationRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realRootIsolationRawAt index rest

def realRootIsolationFromEventFlow (flow : EventFlow) : Option RealRootIsolationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealRootIsolationUp.mk
      (realRootIsolationDecodeBHist (realRootIsolationRawAt 0 flow))
      (realRootIsolationDecodeBHist (realRootIsolationRawAt 1 flow))
      (realRootIsolationDecodeBHist (realRootIsolationRawAt 2 flow))
      (realRootIsolationDecodeBHist (realRootIsolationRawAt 3 flow))
      (realRootIsolationDecodeBHist (realRootIsolationRawAt 4 flow))
      (realRootIsolationDecodeBHist (realRootIsolationRawAt 5 flow))
      (realRootIsolationDecodeBHist (realRootIsolationRawAt 6 flow))
      (realRootIsolationDecodeBHist (realRootIsolationRawAt 7 flow))
      (realRootIsolationDecodeBHist (realRootIsolationRawAt 8 flow))
      (realRootIsolationDecodeBHist (realRootIsolationRawAt 9 flow))
      (realRootIsolationDecodeBHist (realRootIsolationRawAt 10 flow)))

private theorem RealRootIsolationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealRootIsolationUp,
      realRootIsolationFromEventFlow (realRootIsolationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk P E S B D T L H C Q N =>
      change
        some
          (RealRootIsolationUp.mk
            (realRootIsolationDecodeBHist (realRootIsolationEncodeBHist P))
            (realRootIsolationDecodeBHist (realRootIsolationEncodeBHist E))
            (realRootIsolationDecodeBHist (realRootIsolationEncodeBHist S))
            (realRootIsolationDecodeBHist (realRootIsolationEncodeBHist B))
            (realRootIsolationDecodeBHist (realRootIsolationEncodeBHist D))
            (realRootIsolationDecodeBHist (realRootIsolationEncodeBHist T))
            (realRootIsolationDecodeBHist (realRootIsolationEncodeBHist L))
            (realRootIsolationDecodeBHist (realRootIsolationEncodeBHist H))
            (realRootIsolationDecodeBHist (realRootIsolationEncodeBHist C))
            (realRootIsolationDecodeBHist (realRootIsolationEncodeBHist Q))
            (realRootIsolationDecodeBHist (realRootIsolationEncodeBHist N))) =
          some (RealRootIsolationUp.mk P E S B D T L H C Q N)
      rw [RealRootIsolationTasteGate_single_carrier_alignment_decode P,
        RealRootIsolationTasteGate_single_carrier_alignment_decode E,
        RealRootIsolationTasteGate_single_carrier_alignment_decode S,
        RealRootIsolationTasteGate_single_carrier_alignment_decode B,
        RealRootIsolationTasteGate_single_carrier_alignment_decode D,
        RealRootIsolationTasteGate_single_carrier_alignment_decode T,
        RealRootIsolationTasteGate_single_carrier_alignment_decode L,
        RealRootIsolationTasteGate_single_carrier_alignment_decode H,
        RealRootIsolationTasteGate_single_carrier_alignment_decode C,
        RealRootIsolationTasteGate_single_carrier_alignment_decode Q,
        RealRootIsolationTasteGate_single_carrier_alignment_decode N]

private theorem realRootIsolationToEventFlow_injective {x y : RealRootIsolationUp} :
    realRootIsolationToEventFlow x = realRootIsolationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realRootIsolationFromEventFlow (realRootIsolationToEventFlow x) =
        realRootIsolationFromEventFlow (realRootIsolationToEventFlow y) :=
    congrArg realRootIsolationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealRootIsolationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealRootIsolationTasteGate_single_carrier_alignment_round_trip y)))

instance realRootIsolationBHistCarrier : BHistCarrier RealRootIsolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realRootIsolationToEventFlow
  fromEventFlow := realRootIsolationFromEventFlow

instance realRootIsolationChapterTasteGate : ChapterTasteGate RealRootIsolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realRootIsolationFromEventFlow (realRootIsolationToEventFlow x) = some x
    exact RealRootIsolationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realRootIsolationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealRootIsolationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realRootIsolationChapterTasteGate

theorem RealRootIsolationTasteGate_single_carrier_alignment :
    (∀ h : BHist, realRootIsolationDecodeBHist (realRootIsolationEncodeBHist h) = h) ∧
      (∀ x : RealRootIsolationUp,
        realRootIsolationFromEventFlow (realRootIsolationToEventFlow x) = some x) ∧
        (∀ x y : RealRootIsolationUp,
          realRootIsolationToEventFlow x = realRootIsolationToEventFlow y → x = y) ∧
          realRootIsolationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RealRootIsolationTasteGate_single_carrier_alignment_decode,
      RealRootIsolationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => realRootIsolationToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealRootIsolationUp
