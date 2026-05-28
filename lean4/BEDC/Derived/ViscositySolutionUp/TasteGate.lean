import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ViscositySolutionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ViscositySolutionUp : Type where
  | packet
      (domain regularity candidate operator subTest superTest boundary localization realReadback
        transport replay provenance localName : BHist) :
      ViscositySolutionUp
  deriving DecidableEq

def viscositySolutionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: viscositySolutionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: viscositySolutionEncodeBHist h

def viscositySolutionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (viscositySolutionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (viscositySolutionDecodeBHist tail)

private theorem viscositySolutionDecode_encode :
    forall h : BHist, viscositySolutionDecodeBHist (viscositySolutionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def viscositySolutionFields : ViscositySolutionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ViscositySolutionUp.packet domain regularity candidate operator subTest superTest boundary
      localization realReadback transport replay provenance localName =>
      [domain, regularity, candidate, operator, subTest, superTest, boundary, localization,
        realReadback, transport, replay, provenance, localName]

def viscositySolutionToEventFlow : ViscositySolutionUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (viscositySolutionFields x).map viscositySolutionEncodeBHist

private def viscositySolutionEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => viscositySolutionEventAtDefault index rest

def viscositySolutionFromEventFlow (ef : EventFlow) : Option ViscositySolutionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ViscositySolutionUp.packet
      (viscositySolutionDecodeBHist (viscositySolutionEventAtDefault 0 ef))
      (viscositySolutionDecodeBHist (viscositySolutionEventAtDefault 1 ef))
      (viscositySolutionDecodeBHist (viscositySolutionEventAtDefault 2 ef))
      (viscositySolutionDecodeBHist (viscositySolutionEventAtDefault 3 ef))
      (viscositySolutionDecodeBHist (viscositySolutionEventAtDefault 4 ef))
      (viscositySolutionDecodeBHist (viscositySolutionEventAtDefault 5 ef))
      (viscositySolutionDecodeBHist (viscositySolutionEventAtDefault 6 ef))
      (viscositySolutionDecodeBHist (viscositySolutionEventAtDefault 7 ef))
      (viscositySolutionDecodeBHist (viscositySolutionEventAtDefault 8 ef))
      (viscositySolutionDecodeBHist (viscositySolutionEventAtDefault 9 ef))
      (viscositySolutionDecodeBHist (viscositySolutionEventAtDefault 10 ef))
      (viscositySolutionDecodeBHist (viscositySolutionEventAtDefault 11 ef))
      (viscositySolutionDecodeBHist (viscositySolutionEventAtDefault 12 ef)))

private theorem viscositySolution_round_trip :
    forall x : ViscositySolutionUp,
      viscositySolutionFromEventFlow (viscositySolutionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | packet domain regularity candidate operator subTest superTest boundary localization
      realReadback transport replay provenance localName =>
      change
        some
          (ViscositySolutionUp.packet
            (viscositySolutionDecodeBHist (viscositySolutionEncodeBHist domain))
            (viscositySolutionDecodeBHist (viscositySolutionEncodeBHist regularity))
            (viscositySolutionDecodeBHist (viscositySolutionEncodeBHist candidate))
            (viscositySolutionDecodeBHist (viscositySolutionEncodeBHist operator))
            (viscositySolutionDecodeBHist (viscositySolutionEncodeBHist subTest))
            (viscositySolutionDecodeBHist (viscositySolutionEncodeBHist superTest))
            (viscositySolutionDecodeBHist (viscositySolutionEncodeBHist boundary))
            (viscositySolutionDecodeBHist (viscositySolutionEncodeBHist localization))
            (viscositySolutionDecodeBHist (viscositySolutionEncodeBHist realReadback))
            (viscositySolutionDecodeBHist (viscositySolutionEncodeBHist transport))
            (viscositySolutionDecodeBHist (viscositySolutionEncodeBHist replay))
            (viscositySolutionDecodeBHist (viscositySolutionEncodeBHist provenance))
            (viscositySolutionDecodeBHist (viscositySolutionEncodeBHist localName))) =
          some
            (ViscositySolutionUp.packet domain regularity candidate operator subTest
              superTest boundary localization realReadback transport replay provenance localName)
      rw [viscositySolutionDecode_encode domain, viscositySolutionDecode_encode regularity,
        viscositySolutionDecode_encode candidate, viscositySolutionDecode_encode operator,
        viscositySolutionDecode_encode subTest, viscositySolutionDecode_encode superTest,
        viscositySolutionDecode_encode boundary, viscositySolutionDecode_encode localization,
        viscositySolutionDecode_encode realReadback, viscositySolutionDecode_encode transport,
        viscositySolutionDecode_encode replay, viscositySolutionDecode_encode provenance,
        viscositySolutionDecode_encode localName]

private theorem viscositySolutionToEventFlow_injective {x y : ViscositySolutionUp} :
    viscositySolutionToEventFlow x = viscositySolutionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      viscositySolutionFromEventFlow (viscositySolutionToEventFlow x) =
        viscositySolutionFromEventFlow (viscositySolutionToEventFlow y) :=
    congrArg viscositySolutionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (viscositySolution_round_trip x).symm
      (Eq.trans hread (viscositySolution_round_trip y)))

instance viscositySolutionBHistCarrier : BHistCarrier ViscositySolutionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := viscositySolutionToEventFlow
  fromEventFlow := viscositySolutionFromEventFlow

instance viscositySolutionChapterTasteGate : ChapterTasteGate ViscositySolutionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change viscositySolutionFromEventFlow (viscositySolutionToEventFlow x) = some x
    exact viscositySolution_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (viscositySolutionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ViscositySolutionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  viscositySolutionChapterTasteGate

theorem ViscositySolutionTasteGate_single_carrier_alignment :
    (forall h : BHist, viscositySolutionDecodeBHist (viscositySolutionEncodeBHist h) = h) /\
      (forall x : ViscositySolutionUp,
        viscositySolutionFromEventFlow (viscositySolutionToEventFlow x) = some x) /\
        (forall x y : ViscositySolutionUp,
          viscositySolutionToEventFlow x = viscositySolutionToEventFlow y -> x = y) /\
          viscositySolutionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨viscositySolutionDecode_encode, viscositySolution_round_trip,
      (fun _ _ heq => viscositySolutionToEventFlow_injective heq), rfl⟩

end BEDC.Derived.ViscositySolutionUp
