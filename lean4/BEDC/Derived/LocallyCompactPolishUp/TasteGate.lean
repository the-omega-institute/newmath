import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocallyCompactPolishUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocallyCompactPolishUp : Type where
  | mk (X M K C S E W T R H Q P N : BHist) : LocallyCompactPolishUp
  deriving DecidableEq

def locallyCompactPolishEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locallyCompactPolishEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locallyCompactPolishEncodeBHist h

def locallyCompactPolishDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locallyCompactPolishDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locallyCompactPolishDecodeBHist tail)

private theorem LocallyCompactPolishTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, locallyCompactPolishDecodeBHist (locallyCompactPolishEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locallyCompactPolishFields : LocallyCompactPolishUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocallyCompactPolishUp.mk X M K C S E W T R H Q P N =>
      [X, M, K, C, S, E, W, T, R, H, Q, P, N]

def locallyCompactPolishToEventFlow : LocallyCompactPolishUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locallyCompactPolishFields x).map locallyCompactPolishEncodeBHist

private def locallyCompactPolishEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locallyCompactPolishEventAtDefault index rest

def locallyCompactPolishFromEventFlow (ef : EventFlow) : Option LocallyCompactPolishUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocallyCompactPolishUp.mk
      (locallyCompactPolishDecodeBHist (locallyCompactPolishEventAtDefault 0 ef))
      (locallyCompactPolishDecodeBHist (locallyCompactPolishEventAtDefault 1 ef))
      (locallyCompactPolishDecodeBHist (locallyCompactPolishEventAtDefault 2 ef))
      (locallyCompactPolishDecodeBHist (locallyCompactPolishEventAtDefault 3 ef))
      (locallyCompactPolishDecodeBHist (locallyCompactPolishEventAtDefault 4 ef))
      (locallyCompactPolishDecodeBHist (locallyCompactPolishEventAtDefault 5 ef))
      (locallyCompactPolishDecodeBHist (locallyCompactPolishEventAtDefault 6 ef))
      (locallyCompactPolishDecodeBHist (locallyCompactPolishEventAtDefault 7 ef))
      (locallyCompactPolishDecodeBHist (locallyCompactPolishEventAtDefault 8 ef))
      (locallyCompactPolishDecodeBHist (locallyCompactPolishEventAtDefault 9 ef))
      (locallyCompactPolishDecodeBHist (locallyCompactPolishEventAtDefault 10 ef))
      (locallyCompactPolishDecodeBHist (locallyCompactPolishEventAtDefault 11 ef))
      (locallyCompactPolishDecodeBHist (locallyCompactPolishEventAtDefault 12 ef)))

private theorem LocallyCompactPolishTasteGate_single_carrier_alignment_round_trip
    (x : LocallyCompactPolishUp) :
    locallyCompactPolishFromEventFlow (locallyCompactPolishToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X M K C S E W T R H Q P N =>
      change
        some
          (LocallyCompactPolishUp.mk
            (locallyCompactPolishDecodeBHist (locallyCompactPolishEncodeBHist X))
            (locallyCompactPolishDecodeBHist (locallyCompactPolishEncodeBHist M))
            (locallyCompactPolishDecodeBHist (locallyCompactPolishEncodeBHist K))
            (locallyCompactPolishDecodeBHist (locallyCompactPolishEncodeBHist C))
            (locallyCompactPolishDecodeBHist (locallyCompactPolishEncodeBHist S))
            (locallyCompactPolishDecodeBHist (locallyCompactPolishEncodeBHist E))
            (locallyCompactPolishDecodeBHist (locallyCompactPolishEncodeBHist W))
            (locallyCompactPolishDecodeBHist (locallyCompactPolishEncodeBHist T))
            (locallyCompactPolishDecodeBHist (locallyCompactPolishEncodeBHist R))
            (locallyCompactPolishDecodeBHist (locallyCompactPolishEncodeBHist H))
            (locallyCompactPolishDecodeBHist (locallyCompactPolishEncodeBHist Q))
            (locallyCompactPolishDecodeBHist (locallyCompactPolishEncodeBHist P))
            (locallyCompactPolishDecodeBHist (locallyCompactPolishEncodeBHist N))) =
          some (LocallyCompactPolishUp.mk X M K C S E W T R H Q P N)
      rw [LocallyCompactPolishTasteGate_single_carrier_alignment_decode_encode X,
        LocallyCompactPolishTasteGate_single_carrier_alignment_decode_encode M,
        LocallyCompactPolishTasteGate_single_carrier_alignment_decode_encode K,
        LocallyCompactPolishTasteGate_single_carrier_alignment_decode_encode C,
        LocallyCompactPolishTasteGate_single_carrier_alignment_decode_encode S,
        LocallyCompactPolishTasteGate_single_carrier_alignment_decode_encode E,
        LocallyCompactPolishTasteGate_single_carrier_alignment_decode_encode W,
        LocallyCompactPolishTasteGate_single_carrier_alignment_decode_encode T,
        LocallyCompactPolishTasteGate_single_carrier_alignment_decode_encode R,
        LocallyCompactPolishTasteGate_single_carrier_alignment_decode_encode H,
        LocallyCompactPolishTasteGate_single_carrier_alignment_decode_encode Q,
        LocallyCompactPolishTasteGate_single_carrier_alignment_decode_encode P,
        LocallyCompactPolishTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocallyCompactPolishTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocallyCompactPolishUp} :
    locallyCompactPolishToEventFlow x = locallyCompactPolishToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locallyCompactPolishFromEventFlow (locallyCompactPolishToEventFlow x) =
        locallyCompactPolishFromEventFlow (locallyCompactPolishToEventFlow y) :=
    congrArg locallyCompactPolishFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocallyCompactPolishTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocallyCompactPolishTasteGate_single_carrier_alignment_round_trip y)))

instance locallyCompactPolishBHistCarrier : BHistCarrier LocallyCompactPolishUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locallyCompactPolishToEventFlow
  fromEventFlow := locallyCompactPolishFromEventFlow

instance locallyCompactPolishChapterTasteGate : ChapterTasteGate LocallyCompactPolishUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locallyCompactPolishFromEventFlow (locallyCompactPolishToEventFlow x) = some x
    exact LocallyCompactPolishTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocallyCompactPolishTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LocallyCompactPolishTasteGate_single_carrier_alignment :
    (∀ h : BHist, locallyCompactPolishDecodeBHist (locallyCompactPolishEncodeBHist h) = h) ∧
      (∀ x : LocallyCompactPolishUp,
        locallyCompactPolishFromEventFlow (locallyCompactPolishToEventFlow x) = some x) ∧
        (∀ x y : LocallyCompactPolishUp,
          locallyCompactPolishToEventFlow x = locallyCompactPolishToEventFlow y → x = y) ∧
          locallyCompactPolishEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocallyCompactPolishTasteGate_single_carrier_alignment_decode_encode,
      LocallyCompactPolishTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        LocallyCompactPolishTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocallyCompactPolishUp
