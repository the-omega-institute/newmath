import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyMeshCofinalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyMeshCofinalityUp : Type where
  | mk (Q R D B S A E H C P N : BHist) : RegularCauchyMeshCofinalityUp
  deriving DecidableEq

def regularCauchyMeshCofinalityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyMeshCofinalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyMeshCofinalityEncodeBHist h

def regularCauchyMeshCofinalityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyMeshCofinalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyMeshCofinalityDecodeBHist tail)

private theorem RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      regularCauchyMeshCofinalityDecodeBHist (regularCauchyMeshCofinalityEncodeBHist h) =
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

def regularCauchyMeshCofinalityFields :
    RegularCauchyMeshCofinalityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMeshCofinalityUp.mk Q R D B S A E H C P N =>
      [Q, R, D, B, S, A, E, H, C, P, N]

def regularCauchyMeshCofinalityToEventFlow :
    RegularCauchyMeshCofinalityUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyMeshCofinalityFields x).map regularCauchyMeshCofinalityEncodeBHist

private def regularCauchyMeshCofinalityEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyMeshCofinalityEventAt index rest

def regularCauchyMeshCofinalityFromEventFlow
    (ef : EventFlow) : Option RegularCauchyMeshCofinalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyMeshCofinalityUp.mk
      (regularCauchyMeshCofinalityDecodeBHist (regularCauchyMeshCofinalityEventAt 0 ef))
      (regularCauchyMeshCofinalityDecodeBHist (regularCauchyMeshCofinalityEventAt 1 ef))
      (regularCauchyMeshCofinalityDecodeBHist (regularCauchyMeshCofinalityEventAt 2 ef))
      (regularCauchyMeshCofinalityDecodeBHist (regularCauchyMeshCofinalityEventAt 3 ef))
      (regularCauchyMeshCofinalityDecodeBHist (regularCauchyMeshCofinalityEventAt 4 ef))
      (regularCauchyMeshCofinalityDecodeBHist (regularCauchyMeshCofinalityEventAt 5 ef))
      (regularCauchyMeshCofinalityDecodeBHist (regularCauchyMeshCofinalityEventAt 6 ef))
      (regularCauchyMeshCofinalityDecodeBHist (regularCauchyMeshCofinalityEventAt 7 ef))
      (regularCauchyMeshCofinalityDecodeBHist (regularCauchyMeshCofinalityEventAt 8 ef))
      (regularCauchyMeshCofinalityDecodeBHist (regularCauchyMeshCofinalityEventAt 9 ef))
      (regularCauchyMeshCofinalityDecodeBHist (regularCauchyMeshCofinalityEventAt 10 ef)))

private theorem RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyMeshCofinalityUp) :
    regularCauchyMeshCofinalityFromEventFlow
      (regularCauchyMeshCofinalityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q R D B S A E H C P N =>
      change
        some
          (RegularCauchyMeshCofinalityUp.mk
            (regularCauchyMeshCofinalityDecodeBHist
              (regularCauchyMeshCofinalityEncodeBHist Q))
            (regularCauchyMeshCofinalityDecodeBHist
              (regularCauchyMeshCofinalityEncodeBHist R))
            (regularCauchyMeshCofinalityDecodeBHist
              (regularCauchyMeshCofinalityEncodeBHist D))
            (regularCauchyMeshCofinalityDecodeBHist
              (regularCauchyMeshCofinalityEncodeBHist B))
            (regularCauchyMeshCofinalityDecodeBHist
              (regularCauchyMeshCofinalityEncodeBHist S))
            (regularCauchyMeshCofinalityDecodeBHist
              (regularCauchyMeshCofinalityEncodeBHist A))
            (regularCauchyMeshCofinalityDecodeBHist
              (regularCauchyMeshCofinalityEncodeBHist E))
            (regularCauchyMeshCofinalityDecodeBHist
              (regularCauchyMeshCofinalityEncodeBHist H))
            (regularCauchyMeshCofinalityDecodeBHist
              (regularCauchyMeshCofinalityEncodeBHist C))
            (regularCauchyMeshCofinalityDecodeBHist
              (regularCauchyMeshCofinalityEncodeBHist P))
            (regularCauchyMeshCofinalityDecodeBHist
              (regularCauchyMeshCofinalityEncodeBHist N))) =
          some (RegularCauchyMeshCofinalityUp.mk Q R D B S A E H C P N)
      rw [RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_decode_encode Q,
        RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_decode_encode B,
        RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_decode_encode A,
        RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyMeshCofinalityUp} :
    regularCauchyMeshCofinalityToEventFlow x =
        regularCauchyMeshCofinalityToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyMeshCofinalityFromEventFlow
          (regularCauchyMeshCofinalityToEventFlow x) =
        regularCauchyMeshCofinalityFromEventFlow
          (regularCauchyMeshCofinalityToEventFlow y) :=
    congrArg regularCauchyMeshCofinalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyMeshCofinalityBHistCarrier :
    BHistCarrier RegularCauchyMeshCofinalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyMeshCofinalityToEventFlow
  fromEventFlow := regularCauchyMeshCofinalityFromEventFlow

instance regularCauchyMeshCofinalityChapterTasteGate :
    ChapterTasteGate RegularCauchyMeshCofinalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyMeshCofinalityFromEventFlow
        (regularCauchyMeshCofinalityToEventFlow x) = some x
    exact RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RegularCauchyMeshCofinalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyMeshCofinalityChapterTasteGate

theorem RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment :
    (forall h : BHist,
      regularCauchyMeshCofinalityDecodeBHist
        (regularCauchyMeshCofinalityEncodeBHist h) = h) ∧
      (forall x : RegularCauchyMeshCofinalityUp,
        regularCauchyMeshCofinalityFromEventFlow
          (regularCauchyMeshCofinalityToEventFlow x) = some x) ∧
        (forall x y : RegularCauchyMeshCofinalityUp,
          regularCauchyMeshCofinalityToEventFlow x =
              regularCauchyMeshCofinalityToEventFlow y ->
            x = y) ∧
          regularCauchyMeshCofinalityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyMeshCofinalityTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyMeshCofinalityUp
