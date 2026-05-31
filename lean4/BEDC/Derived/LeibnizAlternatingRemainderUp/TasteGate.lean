import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LeibnizAlternatingRemainderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LeibnizAlternatingRemainderUp : Type where
  | mk
      (source sign monotone handoff dyadic windows readback realSeal transport replay
        provenance nameCert : BHist) :
      LeibnizAlternatingRemainderUp

def leibnizAlternatingRemainderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: leibnizAlternatingRemainderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: leibnizAlternatingRemainderEncodeBHist h

def leibnizAlternatingRemainderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (leibnizAlternatingRemainderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (leibnizAlternatingRemainderDecodeBHist tail)

private theorem leibnizAlternatingRemainder_decode_encode :
    ∀ h : BHist,
      leibnizAlternatingRemainderDecodeBHist
          (leibnizAlternatingRemainderEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def leibnizAlternatingRemainderFields :
    LeibnizAlternatingRemainderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LeibnizAlternatingRemainderUp.mk source sign monotone handoff dyadic windows
      readback realSeal transport replay provenance nameCert =>
      [source, sign, monotone, handoff, dyadic, windows, readback, realSeal, transport,
        replay, provenance, nameCert]

def leibnizAlternatingRemainderToEventFlow :
    LeibnizAlternatingRemainderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (leibnizAlternatingRemainderFields x).map
        leibnizAlternatingRemainderEncodeBHist

private def leibnizAlternatingRemainderEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => leibnizAlternatingRemainderEventAt index rest

def leibnizAlternatingRemainderFromEventFlow :
    EventFlow → Option LeibnizAlternatingRemainderUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (LeibnizAlternatingRemainderUp.mk
          (leibnizAlternatingRemainderDecodeBHist
            (leibnizAlternatingRemainderEventAt 0 ef))
          (leibnizAlternatingRemainderDecodeBHist
            (leibnizAlternatingRemainderEventAt 1 ef))
          (leibnizAlternatingRemainderDecodeBHist
            (leibnizAlternatingRemainderEventAt 2 ef))
          (leibnizAlternatingRemainderDecodeBHist
            (leibnizAlternatingRemainderEventAt 3 ef))
          (leibnizAlternatingRemainderDecodeBHist
            (leibnizAlternatingRemainderEventAt 4 ef))
          (leibnizAlternatingRemainderDecodeBHist
            (leibnizAlternatingRemainderEventAt 5 ef))
          (leibnizAlternatingRemainderDecodeBHist
            (leibnizAlternatingRemainderEventAt 6 ef))
          (leibnizAlternatingRemainderDecodeBHist
            (leibnizAlternatingRemainderEventAt 7 ef))
          (leibnizAlternatingRemainderDecodeBHist
            (leibnizAlternatingRemainderEventAt 8 ef))
          (leibnizAlternatingRemainderDecodeBHist
            (leibnizAlternatingRemainderEventAt 9 ef))
          (leibnizAlternatingRemainderDecodeBHist
            (leibnizAlternatingRemainderEventAt 10 ef))
          (leibnizAlternatingRemainderDecodeBHist
            (leibnizAlternatingRemainderEventAt 11 ef)))

private theorem leibnizAlternatingRemainder_round_trip
    (x : LeibnizAlternatingRemainderUp) :
    leibnizAlternatingRemainderFromEventFlow
        (leibnizAlternatingRemainderToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk source sign monotone handoff dyadic windows readback realSeal transport replay
      provenance nameCert =>
      change
        some
            (LeibnizAlternatingRemainderUp.mk
              (leibnizAlternatingRemainderDecodeBHist
                (leibnizAlternatingRemainderEncodeBHist source))
              (leibnizAlternatingRemainderDecodeBHist
                (leibnizAlternatingRemainderEncodeBHist sign))
              (leibnizAlternatingRemainderDecodeBHist
                (leibnizAlternatingRemainderEncodeBHist monotone))
              (leibnizAlternatingRemainderDecodeBHist
                (leibnizAlternatingRemainderEncodeBHist handoff))
              (leibnizAlternatingRemainderDecodeBHist
                (leibnizAlternatingRemainderEncodeBHist dyadic))
              (leibnizAlternatingRemainderDecodeBHist
                (leibnizAlternatingRemainderEncodeBHist windows))
              (leibnizAlternatingRemainderDecodeBHist
                (leibnizAlternatingRemainderEncodeBHist readback))
              (leibnizAlternatingRemainderDecodeBHist
                (leibnizAlternatingRemainderEncodeBHist realSeal))
              (leibnizAlternatingRemainderDecodeBHist
                (leibnizAlternatingRemainderEncodeBHist transport))
              (leibnizAlternatingRemainderDecodeBHist
                (leibnizAlternatingRemainderEncodeBHist replay))
              (leibnizAlternatingRemainderDecodeBHist
                (leibnizAlternatingRemainderEncodeBHist provenance))
              (leibnizAlternatingRemainderDecodeBHist
                (leibnizAlternatingRemainderEncodeBHist nameCert))) =
          some
            (LeibnizAlternatingRemainderUp.mk source sign monotone handoff dyadic windows
              readback realSeal transport replay provenance nameCert)
      rw [leibnizAlternatingRemainder_decode_encode source,
        leibnizAlternatingRemainder_decode_encode sign,
        leibnizAlternatingRemainder_decode_encode monotone,
        leibnizAlternatingRemainder_decode_encode handoff,
        leibnizAlternatingRemainder_decode_encode dyadic,
        leibnizAlternatingRemainder_decode_encode windows,
        leibnizAlternatingRemainder_decode_encode readback,
        leibnizAlternatingRemainder_decode_encode realSeal,
        leibnizAlternatingRemainder_decode_encode transport,
        leibnizAlternatingRemainder_decode_encode replay,
        leibnizAlternatingRemainder_decode_encode provenance,
        leibnizAlternatingRemainder_decode_encode nameCert]

private theorem leibnizAlternatingRemainderToEventFlow_injective
    {x y : LeibnizAlternatingRemainderUp} :
    leibnizAlternatingRemainderToEventFlow x =
        leibnizAlternatingRemainderToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      leibnizAlternatingRemainderFromEventFlow
          (leibnizAlternatingRemainderToEventFlow x) =
        leibnizAlternatingRemainderFromEventFlow
          (leibnizAlternatingRemainderToEventFlow y) :=
    congrArg leibnizAlternatingRemainderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (leibnizAlternatingRemainder_round_trip x).symm
      (Eq.trans hread (leibnizAlternatingRemainder_round_trip y)))

instance leibnizAlternatingRemainderBHistCarrier :
    BHistCarrier LeibnizAlternatingRemainderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := leibnizAlternatingRemainderToEventFlow
  fromEventFlow := leibnizAlternatingRemainderFromEventFlow

instance leibnizAlternatingRemainderChapterTasteGate :
    ChapterTasteGate LeibnizAlternatingRemainderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := leibnizAlternatingRemainder_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (leibnizAlternatingRemainderToEventFlow_injective heq)

theorem LeibnizAlternatingRemainderTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier LeibnizAlternatingRemainderUp) ∧
      Nonempty (ChapterTasteGate LeibnizAlternatingRemainderUp) ∧
        (∀ h : BHist,
          leibnizAlternatingRemainderDecodeBHist
              (leibnizAlternatingRemainderEncodeBHist h) =
            h) ∧
          leibnizAlternatingRemainderFields
              (LeibnizAlternatingRemainderUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨Nonempty.intro leibnizAlternatingRemainderBHistCarrier,
      Nonempty.intro leibnizAlternatingRemainderChapterTasteGate,
      leibnizAlternatingRemainder_decode_encode, rfl⟩

end BEDC.Derived.LeibnizAlternatingRemainderUp
