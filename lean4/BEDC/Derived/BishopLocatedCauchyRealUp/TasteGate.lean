import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedCauchyRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedCauchyRealUp : Type where
  | mk (I B D S R A W H C P N : BHist) : BishopLocatedCauchyRealUp
  deriving DecidableEq

def bishopLocatedCauchyRealEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedCauchyRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedCauchyRealEncodeBHist h

def bishopLocatedCauchyRealDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedCauchyRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedCauchyRealDecodeBHist tail)

private theorem bishopLocatedCauchyRealDecodeEncodeBHist :
    forall h : BHist,
      bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedCauchyRealFields : BishopLocatedCauchyRealUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedCauchyRealUp.mk I B D S R A W H C P N => [I, B, D, S, R, A, W, H, C, P, N]

def bishopLocatedCauchyRealToEventFlow : BishopLocatedCauchyRealUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopLocatedCauchyRealFields x).map bishopLocatedCauchyRealEncodeBHist

private def bishopLocatedCauchyRealEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopLocatedCauchyRealEventAtDefault index rest

def bishopLocatedCauchyRealFromEventFlow
    (ef : EventFlow) : Option BishopLocatedCauchyRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedCauchyRealUp.mk
      (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEventAtDefault 0 ef))
      (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEventAtDefault 1 ef))
      (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEventAtDefault 2 ef))
      (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEventAtDefault 3 ef))
      (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEventAtDefault 4 ef))
      (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEventAtDefault 5 ef))
      (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEventAtDefault 6 ef))
      (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEventAtDefault 7 ef))
      (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEventAtDefault 8 ef))
      (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEventAtDefault 9 ef))
      (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEventAtDefault 10 ef)))

private theorem bishopLocatedCauchyRealRoundTrip :
    forall x : BishopLocatedCauchyRealUp,
      bishopLocatedCauchyRealFromEventFlow (bishopLocatedCauchyRealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I B D S R A W H C P N =>
      change
        some
          (BishopLocatedCauchyRealUp.mk
            (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEncodeBHist I))
            (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEncodeBHist B))
            (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEncodeBHist D))
            (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEncodeBHist S))
            (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEncodeBHist R))
            (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEncodeBHist A))
            (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEncodeBHist W))
            (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEncodeBHist H))
            (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEncodeBHist C))
            (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEncodeBHist P))
            (bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEncodeBHist N))) =
          some (BishopLocatedCauchyRealUp.mk I B D S R A W H C P N)
      rw [bishopLocatedCauchyRealDecodeEncodeBHist I,
        bishopLocatedCauchyRealDecodeEncodeBHist B,
        bishopLocatedCauchyRealDecodeEncodeBHist D,
        bishopLocatedCauchyRealDecodeEncodeBHist S,
        bishopLocatedCauchyRealDecodeEncodeBHist R,
        bishopLocatedCauchyRealDecodeEncodeBHist A,
        bishopLocatedCauchyRealDecodeEncodeBHist W,
        bishopLocatedCauchyRealDecodeEncodeBHist H,
        bishopLocatedCauchyRealDecodeEncodeBHist C,
        bishopLocatedCauchyRealDecodeEncodeBHist P,
        bishopLocatedCauchyRealDecodeEncodeBHist N]

private theorem bishopLocatedCauchyRealToEventFlow_injective
    {x y : BishopLocatedCauchyRealUp} :
    bishopLocatedCauchyRealToEventFlow x = bishopLocatedCauchyRealToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedCauchyRealFromEventFlow (bishopLocatedCauchyRealToEventFlow x) =
        bishopLocatedCauchyRealFromEventFlow (bishopLocatedCauchyRealToEventFlow y) :=
    congrArg bishopLocatedCauchyRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopLocatedCauchyRealRoundTrip x).symm
      (Eq.trans hread (bishopLocatedCauchyRealRoundTrip y)))

private theorem bishopLocatedCauchyRealFieldsFaithful :
    forall x y : BishopLocatedCauchyRealUp,
      bishopLocatedCauchyRealFields x = bishopLocatedCauchyRealFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 B1 D1 S1 R1 A1 W1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 B2 D2 S2 R2 A2 W2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopLocatedCauchyRealBHistCarrier :
    BHistCarrier BishopLocatedCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedCauchyRealToEventFlow
  fromEventFlow := bishopLocatedCauchyRealFromEventFlow

instance bishopLocatedCauchyRealChapterTasteGate :
    ChapterTasteGate BishopLocatedCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopLocatedCauchyRealFromEventFlow (bishopLocatedCauchyRealToEventFlow x) = some x
    exact bishopLocatedCauchyRealRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopLocatedCauchyRealToEventFlow_injective heq)

instance bishopLocatedCauchyRealFieldFaithful :
    FieldFaithful BishopLocatedCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopLocatedCauchyRealFields
  field_faithful := bishopLocatedCauchyRealFieldsFaithful

instance bishopLocatedCauchyRealNontrivial :
    Nontrivial BishopLocatedCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopLocatedCauchyRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopLocatedCauchyRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopLocatedCauchyRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopLocatedCauchyRealChapterTasteGate

theorem BishopLocatedCauchyRealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopLocatedCauchyRealUp) /\
      Nonempty (FieldFaithful BishopLocatedCauchyRealUp) /\
        Nonempty (Nontrivial BishopLocatedCauchyRealUp) /\
          (forall h : BHist,
            bishopLocatedCauchyRealDecodeBHist (bishopLocatedCauchyRealEncodeBHist h) = h) /\
            (forall x : BishopLocatedCauchyRealUp,
              bishopLocatedCauchyRealFromEventFlow (bishopLocatedCauchyRealToEventFlow x) =
                some x) /\
              bishopLocatedCauchyRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial ChapterTasteGate
  exact
    ⟨⟨bishopLocatedCauchyRealChapterTasteGate⟩,
      ⟨⟨bishopLocatedCauchyRealFieldFaithful⟩,
        ⟨⟨bishopLocatedCauchyRealNontrivial⟩,
          bishopLocatedCauchyRealDecodeEncodeBHist,
          bishopLocatedCauchyRealRoundTrip,
          rfl⟩⟩⟩

end BEDC.Derived.BishopLocatedCauchyRealUp
