import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.YoungSymmetrizerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive YoungSymmetrizerUp : Type where
  | mk (P D T R C S A E M H U V G N : BHist) : YoungSymmetrizerUp
  deriving DecidableEq

def youngSymmetrizerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: youngSymmetrizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: youngSymmetrizerEncodeBHist h

def youngSymmetrizerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (youngSymmetrizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (youngSymmetrizerDecodeBHist tail)

private theorem YoungSymmetrizerTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, youngSymmetrizerDecodeBHist (youngSymmetrizerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def youngSymmetrizerFields : YoungSymmetrizerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | YoungSymmetrizerUp.mk P D T R C S A E M H U V G N =>
      [P, D, T, R, C, S, A, E, M, H, U, V, G, N]

def youngSymmetrizerToEventFlow : YoungSymmetrizerUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (youngSymmetrizerFields x).map youngSymmetrizerEncodeBHist

private def youngSymmetrizerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => youngSymmetrizerEventAtDefault index rest

def youngSymmetrizerFromEventFlow (ef : EventFlow) : Option YoungSymmetrizerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (YoungSymmetrizerUp.mk
      (youngSymmetrizerDecodeBHist (youngSymmetrizerEventAtDefault 0 ef))
      (youngSymmetrizerDecodeBHist (youngSymmetrizerEventAtDefault 1 ef))
      (youngSymmetrizerDecodeBHist (youngSymmetrizerEventAtDefault 2 ef))
      (youngSymmetrizerDecodeBHist (youngSymmetrizerEventAtDefault 3 ef))
      (youngSymmetrizerDecodeBHist (youngSymmetrizerEventAtDefault 4 ef))
      (youngSymmetrizerDecodeBHist (youngSymmetrizerEventAtDefault 5 ef))
      (youngSymmetrizerDecodeBHist (youngSymmetrizerEventAtDefault 6 ef))
      (youngSymmetrizerDecodeBHist (youngSymmetrizerEventAtDefault 7 ef))
      (youngSymmetrizerDecodeBHist (youngSymmetrizerEventAtDefault 8 ef))
      (youngSymmetrizerDecodeBHist (youngSymmetrizerEventAtDefault 9 ef))
      (youngSymmetrizerDecodeBHist (youngSymmetrizerEventAtDefault 10 ef))
      (youngSymmetrizerDecodeBHist (youngSymmetrizerEventAtDefault 11 ef))
      (youngSymmetrizerDecodeBHist (youngSymmetrizerEventAtDefault 12 ef))
      (youngSymmetrizerDecodeBHist (youngSymmetrizerEventAtDefault 13 ef)))

private theorem YoungSymmetrizerTasteGate_single_carrier_alignment_round_trip :
    ∀ x : YoungSymmetrizerUp,
      youngSymmetrizerFromEventFlow (youngSymmetrizerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P D T R C S A E M H U V G N =>
      change
        some
          (YoungSymmetrizerUp.mk
            (youngSymmetrizerDecodeBHist (youngSymmetrizerEncodeBHist P))
            (youngSymmetrizerDecodeBHist (youngSymmetrizerEncodeBHist D))
            (youngSymmetrizerDecodeBHist (youngSymmetrizerEncodeBHist T))
            (youngSymmetrizerDecodeBHist (youngSymmetrizerEncodeBHist R))
            (youngSymmetrizerDecodeBHist (youngSymmetrizerEncodeBHist C))
            (youngSymmetrizerDecodeBHist (youngSymmetrizerEncodeBHist S))
            (youngSymmetrizerDecodeBHist (youngSymmetrizerEncodeBHist A))
            (youngSymmetrizerDecodeBHist (youngSymmetrizerEncodeBHist E))
            (youngSymmetrizerDecodeBHist (youngSymmetrizerEncodeBHist M))
            (youngSymmetrizerDecodeBHist (youngSymmetrizerEncodeBHist H))
            (youngSymmetrizerDecodeBHist (youngSymmetrizerEncodeBHist U))
            (youngSymmetrizerDecodeBHist (youngSymmetrizerEncodeBHist V))
            (youngSymmetrizerDecodeBHist (youngSymmetrizerEncodeBHist G))
            (youngSymmetrizerDecodeBHist (youngSymmetrizerEncodeBHist N))) =
          some (YoungSymmetrizerUp.mk P D T R C S A E M H U V G N)
      rw [YoungSymmetrizerTasteGate_single_carrier_alignment_decode P,
        YoungSymmetrizerTasteGate_single_carrier_alignment_decode D,
        YoungSymmetrizerTasteGate_single_carrier_alignment_decode T,
        YoungSymmetrizerTasteGate_single_carrier_alignment_decode R,
        YoungSymmetrizerTasteGate_single_carrier_alignment_decode C,
        YoungSymmetrizerTasteGate_single_carrier_alignment_decode S,
        YoungSymmetrizerTasteGate_single_carrier_alignment_decode A,
        YoungSymmetrizerTasteGate_single_carrier_alignment_decode E,
        YoungSymmetrizerTasteGate_single_carrier_alignment_decode M,
        YoungSymmetrizerTasteGate_single_carrier_alignment_decode H,
        YoungSymmetrizerTasteGate_single_carrier_alignment_decode U,
        YoungSymmetrizerTasteGate_single_carrier_alignment_decode V,
        YoungSymmetrizerTasteGate_single_carrier_alignment_decode G,
        YoungSymmetrizerTasteGate_single_carrier_alignment_decode N]

private theorem YoungSymmetrizerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : YoungSymmetrizerUp} :
    youngSymmetrizerToEventFlow x = youngSymmetrizerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      youngSymmetrizerFromEventFlow (youngSymmetrizerToEventFlow x) =
        youngSymmetrizerFromEventFlow (youngSymmetrizerToEventFlow y) :=
    congrArg youngSymmetrizerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (YoungSymmetrizerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (YoungSymmetrizerTasteGate_single_carrier_alignment_round_trip y)))

instance youngSymmetrizerBHistCarrier : BHistCarrier YoungSymmetrizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := youngSymmetrizerToEventFlow
  fromEventFlow := youngSymmetrizerFromEventFlow

instance youngSymmetrizerChapterTasteGate : ChapterTasteGate YoungSymmetrizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change youngSymmetrizerFromEventFlow (youngSymmetrizerToEventFlow x) = some x
    exact YoungSymmetrizerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (YoungSymmetrizerTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate YoungSymmetrizerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  youngSymmetrizerChapterTasteGate

theorem YoungSymmetrizerTasteGate_single_carrier_alignment :
    (∀ h : BHist, youngSymmetrizerDecodeBHist (youngSymmetrizerEncodeBHist h) = h) ∧
      (∀ x : YoungSymmetrizerUp,
        youngSymmetrizerFromEventFlow (youngSymmetrizerToEventFlow x) = some x) ∧
        (∀ x y : YoungSymmetrizerUp,
          youngSymmetrizerToEventFlow x = youngSymmetrizerToEventFlow y -> x = y) ∧
          youngSymmetrizerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: YoungSymmetrizerUp BHist BMark ChapterTasteGate
  exact
    ⟨YoungSymmetrizerTasteGate_single_carrier_alignment_decode,
      YoungSymmetrizerTasteGate_single_carrier_alignment_round_trip,
      fun _x _y heq =>
        YoungSymmetrizerTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.YoungSymmetrizerUp
