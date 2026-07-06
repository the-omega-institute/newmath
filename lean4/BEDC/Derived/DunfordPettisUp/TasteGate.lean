import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DunfordPettisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DunfordPettisUp : Type where
  | mk (U M I F B R W H C P N : BHist) : DunfordPettisUp
  deriving DecidableEq

def dunfordPettisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dunfordPettisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dunfordPettisEncodeBHist h

def dunfordPettisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dunfordPettisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dunfordPettisDecodeBHist tail)

private theorem dunfordPettisDecode_encode_bhist :
    ∀ h : BHist, dunfordPettisDecodeBHist (dunfordPettisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dunfordPettisFields : DunfordPettisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DunfordPettisUp.mk U M I F B R W H C P N => [U, M, I, F, B, R, W, H, C, P, N]

def dunfordPettisToEventFlow : DunfordPettisUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (dunfordPettisFields x).map dunfordPettisEncodeBHist

private def dunfordPettisRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dunfordPettisRawAt index rest

def dunfordPettisFromEventFlow (flow : EventFlow) : Option DunfordPettisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DunfordPettisUp.mk
      (dunfordPettisDecodeBHist (dunfordPettisRawAt 0 flow))
      (dunfordPettisDecodeBHist (dunfordPettisRawAt 1 flow))
      (dunfordPettisDecodeBHist (dunfordPettisRawAt 2 flow))
      (dunfordPettisDecodeBHist (dunfordPettisRawAt 3 flow))
      (dunfordPettisDecodeBHist (dunfordPettisRawAt 4 flow))
      (dunfordPettisDecodeBHist (dunfordPettisRawAt 5 flow))
      (dunfordPettisDecodeBHist (dunfordPettisRawAt 6 flow))
      (dunfordPettisDecodeBHist (dunfordPettisRawAt 7 flow))
      (dunfordPettisDecodeBHist (dunfordPettisRawAt 8 flow))
      (dunfordPettisDecodeBHist (dunfordPettisRawAt 9 flow))
      (dunfordPettisDecodeBHist (dunfordPettisRawAt 10 flow)))

private theorem dunfordPettis_round_trip :
    ∀ x : DunfordPettisUp,
      dunfordPettisFromEventFlow (dunfordPettisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U M I F B R W H C P N =>
      change
        some
          (DunfordPettisUp.mk
            (dunfordPettisDecodeBHist (dunfordPettisEncodeBHist U))
            (dunfordPettisDecodeBHist (dunfordPettisEncodeBHist M))
            (dunfordPettisDecodeBHist (dunfordPettisEncodeBHist I))
            (dunfordPettisDecodeBHist (dunfordPettisEncodeBHist F))
            (dunfordPettisDecodeBHist (dunfordPettisEncodeBHist B))
            (dunfordPettisDecodeBHist (dunfordPettisEncodeBHist R))
            (dunfordPettisDecodeBHist (dunfordPettisEncodeBHist W))
            (dunfordPettisDecodeBHist (dunfordPettisEncodeBHist H))
            (dunfordPettisDecodeBHist (dunfordPettisEncodeBHist C))
            (dunfordPettisDecodeBHist (dunfordPettisEncodeBHist P))
            (dunfordPettisDecodeBHist (dunfordPettisEncodeBHist N))) =
          some (DunfordPettisUp.mk U M I F B R W H C P N)
      rw [dunfordPettisDecode_encode_bhist U, dunfordPettisDecode_encode_bhist M,
        dunfordPettisDecode_encode_bhist I, dunfordPettisDecode_encode_bhist F,
        dunfordPettisDecode_encode_bhist B, dunfordPettisDecode_encode_bhist R,
        dunfordPettisDecode_encode_bhist W, dunfordPettisDecode_encode_bhist H,
        dunfordPettisDecode_encode_bhist C, dunfordPettisDecode_encode_bhist P,
        dunfordPettisDecode_encode_bhist N]

private theorem dunfordPettisToEventFlow_injective {x y : DunfordPettisUp} :
    dunfordPettisToEventFlow x = dunfordPettisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dunfordPettisFromEventFlow (dunfordPettisToEventFlow x) =
        dunfordPettisFromEventFlow (dunfordPettisToEventFlow y) :=
    congrArg dunfordPettisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dunfordPettis_round_trip x).symm
      (Eq.trans hread (dunfordPettis_round_trip y)))

instance dunfordPettisBHistCarrier : BHistCarrier DunfordPettisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dunfordPettisToEventFlow
  fromEventFlow := dunfordPettisFromEventFlow

instance dunfordPettisChapterTasteGate : ChapterTasteGate DunfordPettisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dunfordPettisFromEventFlow (dunfordPettisToEventFlow x) = some x
    exact dunfordPettis_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dunfordPettisToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DunfordPettisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dunfordPettisChapterTasteGate

theorem DunfordPettisTasteGate_single_carrier_alignment :
    (∀ h : BHist, dunfordPettisDecodeBHist (dunfordPettisEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DunfordPettisUp) ∧ Nonempty (ChapterTasteGate DunfordPettisUp) ∧
        dunfordPettisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨dunfordPettisDecode_encode_bhist, ⟨dunfordPettisBHistCarrier⟩,
      ⟨dunfordPettisChapterTasteGate⟩, rfl⟩

end BEDC.Derived.DunfordPettisUp
