import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealIntervalArithmeticUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealIntervalArithmeticUp : Type where
  | mk (I J D L T addR mulR E H C P N : BHist) : RealIntervalArithmeticUp
  deriving DecidableEq

def realIntervalArithmeticEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realIntervalArithmeticEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realIntervalArithmeticEncodeBHist h

def realIntervalArithmeticDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realIntervalArithmeticDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realIntervalArithmeticDecodeBHist tail)

private theorem realIntervalArithmetic_decode_encode_bhist :
    ∀ h : BHist, realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realIntervalArithmeticFields : RealIntervalArithmeticUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealIntervalArithmeticUp.mk I J D L T addR mulR E H C P N =>
      [I, J, D, L, T, addR, mulR, E, H, C, P, N]

def realIntervalArithmeticToEventFlow : RealIntervalArithmeticUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealIntervalArithmeticUp.mk I J D L T addR mulR E H C P N =>
      [[BMark.b0],
        realIntervalArithmeticEncodeBHist I,
        [BMark.b1, BMark.b0],
        realIntervalArithmeticEncodeBHist J,
        [BMark.b1, BMark.b1, BMark.b0],
        realIntervalArithmeticEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realIntervalArithmeticEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realIntervalArithmeticEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realIntervalArithmeticEncodeBHist addR,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realIntervalArithmeticEncodeBHist mulR,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realIntervalArithmeticEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realIntervalArithmeticEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realIntervalArithmeticEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realIntervalArithmeticEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realIntervalArithmeticEncodeBHist N]

private def realIntervalArithmeticEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realIntervalArithmeticEventAtDefault index rest

def realIntervalArithmeticFromEventFlow (ef : EventFlow) : Option RealIntervalArithmeticUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealIntervalArithmeticUp.mk
      (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEventAtDefault 1 ef))
      (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEventAtDefault 3 ef))
      (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEventAtDefault 5 ef))
      (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEventAtDefault 7 ef))
      (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEventAtDefault 9 ef))
      (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEventAtDefault 11 ef))
      (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEventAtDefault 13 ef))
      (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEventAtDefault 15 ef))
      (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEventAtDefault 17 ef))
      (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEventAtDefault 19 ef))
      (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEventAtDefault 21 ef))
      (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEventAtDefault 23 ef)))

private theorem realIntervalArithmetic_round_trip :
    ∀ x : RealIntervalArithmeticUp,
      realIntervalArithmeticFromEventFlow (realIntervalArithmeticToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I J D L T addR mulR E H C P N =>
      change
        some
          (RealIntervalArithmeticUp.mk
            (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist I))
            (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist J))
            (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist D))
            (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist L))
            (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist T))
            (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist addR))
            (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist mulR))
            (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist E))
            (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist H))
            (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist C))
            (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist P))
            (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist N))) =
          some (RealIntervalArithmeticUp.mk I J D L T addR mulR E H C P N)
      rw [realIntervalArithmetic_decode_encode_bhist I,
        realIntervalArithmetic_decode_encode_bhist J,
        realIntervalArithmetic_decode_encode_bhist D,
        realIntervalArithmetic_decode_encode_bhist L,
        realIntervalArithmetic_decode_encode_bhist T,
        realIntervalArithmetic_decode_encode_bhist addR,
        realIntervalArithmetic_decode_encode_bhist mulR,
        realIntervalArithmetic_decode_encode_bhist E,
        realIntervalArithmetic_decode_encode_bhist H,
        realIntervalArithmetic_decode_encode_bhist C,
        realIntervalArithmetic_decode_encode_bhist P,
        realIntervalArithmetic_decode_encode_bhist N]

private theorem realIntervalArithmeticToEventFlow_injective
    {x y : RealIntervalArithmeticUp} :
    realIntervalArithmeticToEventFlow x = realIntervalArithmeticToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realIntervalArithmeticFromEventFlow (realIntervalArithmeticToEventFlow x) =
        realIntervalArithmeticFromEventFlow (realIntervalArithmeticToEventFlow y) :=
    congrArg realIntervalArithmeticFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realIntervalArithmetic_round_trip x).symm
      (Eq.trans hread (realIntervalArithmetic_round_trip y)))

private theorem realIntervalArithmetic_fields_faithful :
    ∀ x y : RealIntervalArithmeticUp,
      realIntervalArithmeticFields x = realIntervalArithmeticFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 J1 D1 L1 T1 addR1 mulR1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 J2 D2 L2 T2 addR2 mulR2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realIntervalArithmeticBHistCarrier : BHistCarrier RealIntervalArithmeticUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realIntervalArithmeticToEventFlow
  fromEventFlow := realIntervalArithmeticFromEventFlow

instance realIntervalArithmeticChapterTasteGate :
    ChapterTasteGate RealIntervalArithmeticUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realIntervalArithmeticFromEventFlow (realIntervalArithmeticToEventFlow x) = some x
    exact realIntervalArithmetic_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realIntervalArithmeticToEventFlow_injective heq)

instance realIntervalArithmeticFieldFaithful : FieldFaithful RealIntervalArithmeticUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realIntervalArithmeticFields
  field_faithful := realIntervalArithmetic_fields_faithful

instance realIntervalArithmeticNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RealIntervalArithmeticUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealIntervalArithmeticUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RealIntervalArithmeticUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealIntervalArithmeticUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realIntervalArithmeticChapterTasteGate

theorem RealIntervalArithmeticTasteGate_single_carrier_alignment :
    (∀ h : BHist, realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RealIntervalArithmeticUp) ∧
      Nonempty (ChapterTasteGate RealIntervalArithmeticUp) ∧
      realIntervalArithmeticEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact realIntervalArithmetic_decode_encode_bhist
  constructor
  · exact ⟨realIntervalArithmeticBHistCarrier⟩
  constructor
  · exact ⟨realIntervalArithmeticChapterTasteGate⟩
  · rfl

end BEDC.Derived.RealIntervalArithmeticUp
