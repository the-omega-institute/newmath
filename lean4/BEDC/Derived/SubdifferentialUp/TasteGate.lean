import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubdifferentialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubdifferentialUp : Type where
  | mk (F x xi E L G K H C P N : BHist) : SubdifferentialUp
  deriving DecidableEq

def subdifferentialEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subdifferentialEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subdifferentialEncodeBHist h

def subdifferentialDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subdifferentialDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subdifferentialDecodeBHist tail)

private theorem subdifferentialDecode_encode_bhist :
    forall h : BHist, subdifferentialDecodeBHist (subdifferentialEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def subdifferentialFields : SubdifferentialUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SubdifferentialUp.mk F x xi E L G K H C P N => [F, x, xi, E, L, G, K, H, C, P, N]

def subdifferentialToEventFlow : SubdifferentialUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SubdifferentialUp.mk F x xi E L G K H C P N =>
      [[BMark.b0],
        subdifferentialEncodeBHist F,
        [BMark.b1, BMark.b0],
        subdifferentialEncodeBHist x,
        [BMark.b1, BMark.b1, BMark.b0],
        subdifferentialEncodeBHist xi,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subdifferentialEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subdifferentialEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subdifferentialEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subdifferentialEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        subdifferentialEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        subdifferentialEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        subdifferentialEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subdifferentialEncodeBHist N]

private def subdifferentialEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => subdifferentialEventAtDefault index rest

def subdifferentialFromEventFlow (ef : EventFlow) : Option SubdifferentialUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SubdifferentialUp.mk
      (subdifferentialDecodeBHist (subdifferentialEventAtDefault 1 ef))
      (subdifferentialDecodeBHist (subdifferentialEventAtDefault 3 ef))
      (subdifferentialDecodeBHist (subdifferentialEventAtDefault 5 ef))
      (subdifferentialDecodeBHist (subdifferentialEventAtDefault 7 ef))
      (subdifferentialDecodeBHist (subdifferentialEventAtDefault 9 ef))
      (subdifferentialDecodeBHist (subdifferentialEventAtDefault 11 ef))
      (subdifferentialDecodeBHist (subdifferentialEventAtDefault 13 ef))
      (subdifferentialDecodeBHist (subdifferentialEventAtDefault 15 ef))
      (subdifferentialDecodeBHist (subdifferentialEventAtDefault 17 ef))
      (subdifferentialDecodeBHist (subdifferentialEventAtDefault 19 ef))
      (subdifferentialDecodeBHist (subdifferentialEventAtDefault 21 ef)))

private theorem subdifferential_round_trip :
    forall x : SubdifferentialUp,
      subdifferentialFromEventFlow (subdifferentialToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F x xi E L G K H C P N =>
      change
        some
          (SubdifferentialUp.mk
            (subdifferentialDecodeBHist (subdifferentialEncodeBHist F))
            (subdifferentialDecodeBHist (subdifferentialEncodeBHist x))
            (subdifferentialDecodeBHist (subdifferentialEncodeBHist xi))
            (subdifferentialDecodeBHist (subdifferentialEncodeBHist E))
            (subdifferentialDecodeBHist (subdifferentialEncodeBHist L))
            (subdifferentialDecodeBHist (subdifferentialEncodeBHist G))
            (subdifferentialDecodeBHist (subdifferentialEncodeBHist K))
            (subdifferentialDecodeBHist (subdifferentialEncodeBHist H))
            (subdifferentialDecodeBHist (subdifferentialEncodeBHist C))
            (subdifferentialDecodeBHist (subdifferentialEncodeBHist P))
            (subdifferentialDecodeBHist (subdifferentialEncodeBHist N))) =
          some (SubdifferentialUp.mk F x xi E L G K H C P N)
      rw [subdifferentialDecode_encode_bhist F, subdifferentialDecode_encode_bhist x,
        subdifferentialDecode_encode_bhist xi, subdifferentialDecode_encode_bhist E,
        subdifferentialDecode_encode_bhist L, subdifferentialDecode_encode_bhist G,
        subdifferentialDecode_encode_bhist K, subdifferentialDecode_encode_bhist H,
        subdifferentialDecode_encode_bhist C, subdifferentialDecode_encode_bhist P,
        subdifferentialDecode_encode_bhist N]

private theorem subdifferentialToEventFlow_injective {x y : SubdifferentialUp} :
    subdifferentialToEventFlow x = subdifferentialToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subdifferentialFromEventFlow (subdifferentialToEventFlow x) =
        subdifferentialFromEventFlow (subdifferentialToEventFlow y) :=
    congrArg subdifferentialFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (subdifferential_round_trip x).symm
        (Eq.trans hread (subdifferential_round_trip y)))

instance subdifferentialBHistCarrier : BHistCarrier SubdifferentialUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subdifferentialToEventFlow
  fromEventFlow := subdifferentialFromEventFlow

instance subdifferentialChapterTasteGate : ChapterTasteGate SubdifferentialUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change subdifferentialFromEventFlow (subdifferentialToEventFlow x) = some x
    exact subdifferential_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (subdifferentialToEventFlow_injective heq)

theorem SubdifferentialTasteGate_single_carrier_alignment :
    (forall h : BHist, subdifferentialDecodeBHist (subdifferentialEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SubdifferentialUp) ∧
        Nonempty (ChapterTasteGate SubdifferentialUp) ∧
          subdifferentialEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact subdifferentialDecode_encode_bhist
  · constructor
    · exact ⟨subdifferentialBHistCarrier⟩
    · constructor
      · exact ⟨subdifferentialChapterTasteGate⟩
      · rfl

end BEDC.Derived.SubdifferentialUp
