import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegulatedRealFunctionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegulatedRealFunctionUp : Type where
  | mk (I A T U E H C P N : BHist) : RegulatedRealFunctionUp
  deriving DecidableEq

def regulatedRealFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regulatedRealFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regulatedRealFunctionEncodeBHist h

def regulatedRealFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regulatedRealFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regulatedRealFunctionDecodeBHist tail)

private theorem regulatedRealFunction_decode_encode_bhist :
    ∀ h : BHist, regulatedRealFunctionDecodeBHist (regulatedRealFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regulatedRealFunctionFields : RegulatedRealFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegulatedRealFunctionUp.mk I A T U E H C P N => [I, A, T, U, E, H, C, P, N]

def regulatedRealFunctionToEventFlow : RegulatedRealFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regulatedRealFunctionFields x).map regulatedRealFunctionEncodeBHist

private def regulatedRealFunctionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regulatedRealFunctionEventAt index rest

def regulatedRealFunctionFromEventFlow : EventFlow → Option RegulatedRealFunctionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RegulatedRealFunctionUp.mk
          (regulatedRealFunctionDecodeBHist (regulatedRealFunctionEventAt 0 ef))
          (regulatedRealFunctionDecodeBHist (regulatedRealFunctionEventAt 1 ef))
          (regulatedRealFunctionDecodeBHist (regulatedRealFunctionEventAt 2 ef))
          (regulatedRealFunctionDecodeBHist (regulatedRealFunctionEventAt 3 ef))
          (regulatedRealFunctionDecodeBHist (regulatedRealFunctionEventAt 4 ef))
          (regulatedRealFunctionDecodeBHist (regulatedRealFunctionEventAt 5 ef))
          (regulatedRealFunctionDecodeBHist (regulatedRealFunctionEventAt 6 ef))
          (regulatedRealFunctionDecodeBHist (regulatedRealFunctionEventAt 7 ef))
          (regulatedRealFunctionDecodeBHist (regulatedRealFunctionEventAt 8 ef)))

private theorem regulatedRealFunction_round_trip :
    ∀ x : RegulatedRealFunctionUp,
      regulatedRealFunctionFromEventFlow (regulatedRealFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I A T U E H C P N =>
      change
        some
          (RegulatedRealFunctionUp.mk
            (regulatedRealFunctionDecodeBHist (regulatedRealFunctionEncodeBHist I))
            (regulatedRealFunctionDecodeBHist (regulatedRealFunctionEncodeBHist A))
            (regulatedRealFunctionDecodeBHist (regulatedRealFunctionEncodeBHist T))
            (regulatedRealFunctionDecodeBHist (regulatedRealFunctionEncodeBHist U))
            (regulatedRealFunctionDecodeBHist (regulatedRealFunctionEncodeBHist E))
            (regulatedRealFunctionDecodeBHist (regulatedRealFunctionEncodeBHist H))
            (regulatedRealFunctionDecodeBHist (regulatedRealFunctionEncodeBHist C))
            (regulatedRealFunctionDecodeBHist (regulatedRealFunctionEncodeBHist P))
            (regulatedRealFunctionDecodeBHist (regulatedRealFunctionEncodeBHist N))) =
          some (RegulatedRealFunctionUp.mk I A T U E H C P N)
      rw [regulatedRealFunction_decode_encode_bhist I,
        regulatedRealFunction_decode_encode_bhist A,
        regulatedRealFunction_decode_encode_bhist T,
        regulatedRealFunction_decode_encode_bhist U,
        regulatedRealFunction_decode_encode_bhist E,
        regulatedRealFunction_decode_encode_bhist H,
        regulatedRealFunction_decode_encode_bhist C,
        regulatedRealFunction_decode_encode_bhist P,
        regulatedRealFunction_decode_encode_bhist N]

private theorem regulatedRealFunctionToEventFlow_injective {x y : RegulatedRealFunctionUp} :
    regulatedRealFunctionToEventFlow x = regulatedRealFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regulatedRealFunctionFromEventFlow (regulatedRealFunctionToEventFlow x) =
        regulatedRealFunctionFromEventFlow (regulatedRealFunctionToEventFlow y) :=
    congrArg regulatedRealFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regulatedRealFunction_round_trip x).symm
      (Eq.trans hread (regulatedRealFunction_round_trip y)))

instance regulatedRealFunctionBHistCarrier : BHistCarrier RegulatedRealFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regulatedRealFunctionToEventFlow
  fromEventFlow := regulatedRealFunctionFromEventFlow

instance regulatedRealFunctionChapterTasteGate :
    ChapterTasteGate RegulatedRealFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regulatedRealFunctionFromEventFlow (regulatedRealFunctionToEventFlow x) = some x
    exact regulatedRealFunction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regulatedRealFunctionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegulatedRealFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regulatedRealFunctionChapterTasteGate

end BEDC.Derived.RegulatedRealFunctionUp.TasteGate

namespace BEDC.Derived.RegulatedRealFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem RegulatedRealFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      TasteGate.regulatedRealFunctionDecodeBHist
          (TasteGate.regulatedRealFunctionEncodeBHist h) =
        h) ∧
      (∀ x : TasteGate.RegulatedRealFunctionUp,
        TasteGate.regulatedRealFunctionFromEventFlow
            (TasteGate.regulatedRealFunctionToEventFlow x) =
          some x) ∧
        (∀ x y : TasteGate.RegulatedRealFunctionUp,
          TasteGate.regulatedRealFunctionToEventFlow x =
              TasteGate.regulatedRealFunctionToEventFlow y →
            x = y) ∧
          TasteGate.regulatedRealFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨TasteGate.regulatedRealFunction_decode_encode_bhist,
      TasteGate.regulatedRealFunction_round_trip,
      (fun _ _ heq => TasteGate.regulatedRealFunctionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegulatedRealFunctionUp
