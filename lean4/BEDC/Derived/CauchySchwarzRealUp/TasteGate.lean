import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySchwarzRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySchwarzRealUp : Type where
  | mk (V X Y I A B D Q S E H T P N : BHist) : CauchySchwarzRealUp

def cauchySchwarzRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySchwarzRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySchwarzRealEncodeBHist h

def cauchySchwarzRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySchwarzRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySchwarzRealDecodeBHist tail)

private theorem cauchySchwarzReal_decode_encode_bhist :
    ∀ h : BHist, cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchySchwarzRealToEventFlow : CauchySchwarzRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySchwarzRealUp.mk V X Y I A B D Q S E H T P N =>
      [cauchySchwarzRealEncodeBHist V,
        cauchySchwarzRealEncodeBHist X,
        cauchySchwarzRealEncodeBHist Y,
        cauchySchwarzRealEncodeBHist I,
        cauchySchwarzRealEncodeBHist A,
        cauchySchwarzRealEncodeBHist B,
        cauchySchwarzRealEncodeBHist D,
        cauchySchwarzRealEncodeBHist Q,
        cauchySchwarzRealEncodeBHist S,
        cauchySchwarzRealEncodeBHist E,
        cauchySchwarzRealEncodeBHist H,
        cauchySchwarzRealEncodeBHist T,
        cauchySchwarzRealEncodeBHist P,
        cauchySchwarzRealEncodeBHist N]

private def cauchySchwarzRealEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySchwarzRealEventAt index rest

def cauchySchwarzRealFromEventFlow : EventFlow → Option CauchySchwarzRealUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CauchySchwarzRealUp.mk
          (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAt 0 ef))
          (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAt 1 ef))
          (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAt 2 ef))
          (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAt 3 ef))
          (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAt 4 ef))
          (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAt 5 ef))
          (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAt 6 ef))
          (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAt 7 ef))
          (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAt 8 ef))
          (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAt 9 ef))
          (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAt 10 ef))
          (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAt 11 ef))
          (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAt 12 ef))
          (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEventAt 13 ef)))

private theorem cauchySchwarzReal_round_trip :
    ∀ x : CauchySchwarzRealUp,
      cauchySchwarzRealFromEventFlow (cauchySchwarzRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk V X Y I A B D Q S E H T P N =>
      change
        some
            (CauchySchwarzRealUp.mk
              (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist V))
              (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist X))
              (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist Y))
              (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist I))
              (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist A))
              (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist B))
              (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist D))
              (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist Q))
              (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist S))
              (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist E))
              (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist H))
              (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist T))
              (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist P))
              (cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist N))) =
          some (CauchySchwarzRealUp.mk V X Y I A B D Q S E H T P N)
      rw [cauchySchwarzReal_decode_encode_bhist V,
        cauchySchwarzReal_decode_encode_bhist X,
        cauchySchwarzReal_decode_encode_bhist Y,
        cauchySchwarzReal_decode_encode_bhist I,
        cauchySchwarzReal_decode_encode_bhist A,
        cauchySchwarzReal_decode_encode_bhist B,
        cauchySchwarzReal_decode_encode_bhist D,
        cauchySchwarzReal_decode_encode_bhist Q,
        cauchySchwarzReal_decode_encode_bhist S,
        cauchySchwarzReal_decode_encode_bhist E,
        cauchySchwarzReal_decode_encode_bhist H,
        cauchySchwarzReal_decode_encode_bhist T,
        cauchySchwarzReal_decode_encode_bhist P,
        cauchySchwarzReal_decode_encode_bhist N]

private theorem cauchySchwarzRealToEventFlow_injective
    {x y : CauchySchwarzRealUp} :
    cauchySchwarzRealToEventFlow x = cauchySchwarzRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySchwarzRealFromEventFlow (cauchySchwarzRealToEventFlow x) =
        cauchySchwarzRealFromEventFlow (cauchySchwarzRealToEventFlow y) :=
    congrArg cauchySchwarzRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySchwarzReal_round_trip x).symm
      (Eq.trans hread (cauchySchwarzReal_round_trip y)))

instance cauchySchwarzRealBHistCarrier : BHistCarrier CauchySchwarzRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySchwarzRealToEventFlow
  fromEventFlow := cauchySchwarzRealFromEventFlow

instance cauchySchwarzRealChapterTasteGate : ChapterTasteGate CauchySchwarzRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySchwarzRealFromEventFlow (cauchySchwarzRealToEventFlow x) = some x
    exact cauchySchwarzReal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySchwarzRealToEventFlow_injective heq)

theorem CauchySchwarzRealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchySchwarzRealUp) ∧
      (∀ h : BHist,
        cauchySchwarzRealDecodeBHist (cauchySchwarzRealEncodeBHist h) = h) ∧
        (∀ x : CauchySchwarzRealUp,
          cauchySchwarzRealFromEventFlow (cauchySchwarzRealToEventFlow x) = some x) ∧
          cauchySchwarzRealEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨cauchySchwarzRealChapterTasteGate⟩,
      cauchySchwarzReal_decode_encode_bhist,
      cauchySchwarzReal_round_trip,
      rfl⟩

end BEDC.Derived.CauchySchwarzRealUp
