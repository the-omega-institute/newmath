import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySqueezeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySqueezeUp : Type where
  | mk (L M U W D T E H C P N : BHist) : RegularCauchySqueezeUp
  deriving DecidableEq

def regularCauchySqueezeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySqueezeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySqueezeEncodeBHist h

def regularCauchySqueezeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySqueezeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySqueezeDecodeBHist tail)

private theorem regularCauchySqueezeDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySqueezeToEventFlow : RegularCauchySqueezeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySqueezeUp.mk L M U W D T E H C P N =>
      [regularCauchySqueezeEncodeBHist L,
        regularCauchySqueezeEncodeBHist M,
        regularCauchySqueezeEncodeBHist U,
        regularCauchySqueezeEncodeBHist W,
        regularCauchySqueezeEncodeBHist D,
        regularCauchySqueezeEncodeBHist T,
        regularCauchySqueezeEncodeBHist E,
        regularCauchySqueezeEncodeBHist H,
        regularCauchySqueezeEncodeBHist C,
        regularCauchySqueezeEncodeBHist P,
        regularCauchySqueezeEncodeBHist N]

private def regularCauchySqueezeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchySqueezeEventAt index rest

def regularCauchySqueezeFromEventFlow : EventFlow → Option RegularCauchySqueezeUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RegularCauchySqueezeUp.mk
          (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 0 ef))
          (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 1 ef))
          (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 2 ef))
          (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 3 ef))
          (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 4 ef))
          (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 5 ef))
          (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 6 ef))
          (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 7 ef))
          (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 8 ef))
          (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 9 ef))
          (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 10 ef)))

private theorem regularCauchySqueeze_round_trip :
    ∀ x : RegularCauchySqueezeUp,
      regularCauchySqueezeFromEventFlow (regularCauchySqueezeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L M U W D T E H C P N =>
      change
        some
          (RegularCauchySqueezeUp.mk
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist L))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist M))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist U))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist W))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist D))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist T))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist E))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist H))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist C))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist P))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist N))) =
          some (RegularCauchySqueezeUp.mk L M U W D T E H C P N)
      rw [regularCauchySqueezeDecode_encode_bhist L,
        regularCauchySqueezeDecode_encode_bhist M,
        regularCauchySqueezeDecode_encode_bhist U,
        regularCauchySqueezeDecode_encode_bhist W,
        regularCauchySqueezeDecode_encode_bhist D,
        regularCauchySqueezeDecode_encode_bhist T,
        regularCauchySqueezeDecode_encode_bhist E,
        regularCauchySqueezeDecode_encode_bhist H,
        regularCauchySqueezeDecode_encode_bhist C,
        regularCauchySqueezeDecode_encode_bhist P,
        regularCauchySqueezeDecode_encode_bhist N]

private theorem regularCauchySqueezeToEventFlow_injective
    {x y : RegularCauchySqueezeUp} :
    regularCauchySqueezeToEventFlow x = regularCauchySqueezeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySqueezeFromEventFlow (regularCauchySqueezeToEventFlow x) =
        regularCauchySqueezeFromEventFlow (regularCauchySqueezeToEventFlow y) :=
    congrArg regularCauchySqueezeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchySqueeze_round_trip x).symm
      (Eq.trans hread (regularCauchySqueeze_round_trip y)))

instance regularCauchySqueezeBHistCarrier : BHistCarrier RegularCauchySqueezeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySqueezeToEventFlow
  fromEventFlow := regularCauchySqueezeFromEventFlow

instance regularCauchySqueezeChapterTasteGate :
    ChapterTasteGate RegularCauchySqueezeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchySqueezeFromEventFlow (regularCauchySqueezeToEventFlow x) = some x
    exact regularCauchySqueeze_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySqueezeToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchySqueezeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySqueezeChapterTasteGate

namespace TasteGate

theorem RegularCauchySqueezeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchySqueezeUp) ∧
      (∀ h : BHist,
        regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySqueezeUp,
        regularCauchySqueezeFromEventFlow (regularCauchySqueezeToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchySqueezeUp,
        regularCauchySqueezeToEventFlow x = regularCauchySqueezeToEventFlow y → x = y) ∧
      regularCauchySqueezeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨regularCauchySqueezeChapterTasteGate⟩,
      regularCauchySqueezeDecode_encode_bhist,
      regularCauchySqueeze_round_trip,
      (fun _ _ heq => regularCauchySqueezeToEventFlow_injective heq),
      rfl⟩

end TasteGate

end BEDC.Derived.RegularCauchySqueezeUp
