import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BisectionRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BisectionRealUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (I M S T W R E H C P N : BHist) : BisectionRealUp
  deriving DecidableEq

def bisectionRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bisectionRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bisectionRealEncodeBHist h

def bisectionRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bisectionRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bisectionRealDecodeBHist tail)

private theorem bisectionRealDecode_encode :
    ∀ h : BHist, bisectionRealDecodeBHist (bisectionRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bisectionRealFields : BisectionRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BisectionRealUp.mk I M S T W R E H C P N => [I, M, S, T, W, R, E, H, C, P, N]

def bisectionRealToEventFlow : BisectionRealUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bisectionRealFields x).map bisectionRealEncodeBHist

private def bisectionRealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bisectionRealEventAtDefault index rest

def bisectionRealFromEventFlow (ef : EventFlow) : Option BisectionRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BisectionRealUp.mk
      (bisectionRealDecodeBHist (bisectionRealEventAtDefault 0 ef))
      (bisectionRealDecodeBHist (bisectionRealEventAtDefault 1 ef))
      (bisectionRealDecodeBHist (bisectionRealEventAtDefault 2 ef))
      (bisectionRealDecodeBHist (bisectionRealEventAtDefault 3 ef))
      (bisectionRealDecodeBHist (bisectionRealEventAtDefault 4 ef))
      (bisectionRealDecodeBHist (bisectionRealEventAtDefault 5 ef))
      (bisectionRealDecodeBHist (bisectionRealEventAtDefault 6 ef))
      (bisectionRealDecodeBHist (bisectionRealEventAtDefault 7 ef))
      (bisectionRealDecodeBHist (bisectionRealEventAtDefault 8 ef))
      (bisectionRealDecodeBHist (bisectionRealEventAtDefault 9 ef))
      (bisectionRealDecodeBHist (bisectionRealEventAtDefault 10 ef)))

private theorem bisectionReal_round_trip (x : BisectionRealUp) :
    bisectionRealFromEventFlow (bisectionRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I M S T W R E H C P N =>
      change
        some
          (BisectionRealUp.mk
            (bisectionRealDecodeBHist (bisectionRealEncodeBHist I))
            (bisectionRealDecodeBHist (bisectionRealEncodeBHist M))
            (bisectionRealDecodeBHist (bisectionRealEncodeBHist S))
            (bisectionRealDecodeBHist (bisectionRealEncodeBHist T))
            (bisectionRealDecodeBHist (bisectionRealEncodeBHist W))
            (bisectionRealDecodeBHist (bisectionRealEncodeBHist R))
            (bisectionRealDecodeBHist (bisectionRealEncodeBHist E))
            (bisectionRealDecodeBHist (bisectionRealEncodeBHist H))
            (bisectionRealDecodeBHist (bisectionRealEncodeBHist C))
            (bisectionRealDecodeBHist (bisectionRealEncodeBHist P))
            (bisectionRealDecodeBHist (bisectionRealEncodeBHist N))) =
          some (BisectionRealUp.mk I M S T W R E H C P N)
      rw [bisectionRealDecode_encode I, bisectionRealDecode_encode M,
        bisectionRealDecode_encode S, bisectionRealDecode_encode T,
        bisectionRealDecode_encode W, bisectionRealDecode_encode R,
        bisectionRealDecode_encode E, bisectionRealDecode_encode H,
        bisectionRealDecode_encode C, bisectionRealDecode_encode P,
        bisectionRealDecode_encode N]

private theorem bisectionRealToEventFlow_injective {x y : BisectionRealUp} :
    bisectionRealToEventFlow x = bisectionRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bisectionRealFromEventFlow (bisectionRealToEventFlow x) =
        bisectionRealFromEventFlow (bisectionRealToEventFlow y) :=
    congrArg bisectionRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bisectionReal_round_trip x).symm
      (Eq.trans hread (bisectionReal_round_trip y)))

instance bisectionRealBHistCarrier : BHistCarrier BisectionRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bisectionRealToEventFlow
  fromEventFlow := bisectionRealFromEventFlow

instance bisectionRealChapterTasteGate : ChapterTasteGate BisectionRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bisectionRealFromEventFlow (bisectionRealToEventFlow x) = some x
    exact bisectionReal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bisectionRealToEventFlow_injective heq)

theorem BisectionRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, bisectionRealDecodeBHist (bisectionRealEncodeBHist h) = h) ∧
      (∀ x : BisectionRealUp, bisectionRealFromEventFlow (bisectionRealToEventFlow x) =
        some x) ∧
        Nonempty (BHistCarrier BisectionRealUp) ∧
          Nonempty (ChapterTasteGate BisectionRealUp) ∧
            bisectionRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact bisectionRealDecode_encode
  · constructor
    · exact bisectionReal_round_trip
    · constructor
      · exact
          ⟨{
            toEventFlow := bisectionRealToEventFlow
            fromEventFlow := bisectionRealFromEventFlow
          }⟩
      · constructor
        · let carrier : BHistCarrier BisectionRealUp := {
            toEventFlow := bisectionRealToEventFlow
            fromEventFlow := bisectionRealFromEventFlow
          }
          let gate : @ChapterTasteGate BisectionRealUp carrier := {
            round_trip := by
              intro x
              change bisectionRealFromEventFlow (bisectionRealToEventFlow x) = some x
              exact bisectionReal_round_trip x
            layer_separation := by
              intro x y hxy heq
              exact hxy (bisectionRealToEventFlow_injective heq)
          }
          letI : BHistCarrier BisectionRealUp := carrier
          exact ⟨gate⟩
        · rfl

end BEDC.Derived.BisectionRealUp
