import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntervalBisectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntervalBisectionUp : Type where
  | mk (I M L R D S Q E H C P N : BHist) : IntervalBisectionUp
  deriving DecidableEq

def intervalBisectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: intervalBisectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: intervalBisectionEncodeBHist h

def intervalBisectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (intervalBisectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (intervalBisectionDecodeBHist tail)

private theorem intervalBisection_decode_encode :
    ∀ h : BHist, intervalBisectionDecodeBHist (intervalBisectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def intervalBisectionToEventFlow : IntervalBisectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | IntervalBisectionUp.mk I M L R D S Q E H C P N =>
      [intervalBisectionEncodeBHist I, intervalBisectionEncodeBHist M,
        intervalBisectionEncodeBHist L, intervalBisectionEncodeBHist R,
        intervalBisectionEncodeBHist D, intervalBisectionEncodeBHist S,
        intervalBisectionEncodeBHist Q, intervalBisectionEncodeBHist E,
        intervalBisectionEncodeBHist H, intervalBisectionEncodeBHist C,
        intervalBisectionEncodeBHist P, intervalBisectionEncodeBHist N]

def intervalBisectionFromEventFlow (flow : EventFlow) : Option IntervalBisectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | [] => none
  | I :: rest =>
      match rest with
      | [] => none
      | M :: rest =>
          match rest with
          | [] => none
          | L :: rest =>
              match rest with
              | [] => none
              | R :: rest =>
                  match rest with
                  | [] => none
                  | D :: rest =>
                      match rest with
                      | [] => none
                      | S :: rest =>
                          match rest with
                          | [] => none
                          | Q :: rest =>
                              match rest with
                              | [] => none
                              | E :: rest =>
                                  match rest with
                                  | [] => none
                                  | H :: rest =>
                                      match rest with
                                      | [] => none
                                      | C :: rest =>
                                          match rest with
                                          | [] => none
                                          | P :: rest =>
                                              match rest with
                                              | [] => none
                                              | N :: rest =>
                                                  match rest with
                                                  | [] =>
                                                      some
                                                        (IntervalBisectionUp.mk
                                                          (intervalBisectionDecodeBHist I)
                                                          (intervalBisectionDecodeBHist M)
                                                          (intervalBisectionDecodeBHist L)
                                                          (intervalBisectionDecodeBHist R)
                                                          (intervalBisectionDecodeBHist D)
                                                          (intervalBisectionDecodeBHist S)
                                                          (intervalBisectionDecodeBHist Q)
                                                          (intervalBisectionDecodeBHist E)
                                                          (intervalBisectionDecodeBHist H)
                                                          (intervalBisectionDecodeBHist C)
                                                          (intervalBisectionDecodeBHist P)
                                                          (intervalBisectionDecodeBHist N))
                                                  | _ :: _ => none

private theorem intervalBisection_round_trip :
    ∀ x : IntervalBisectionUp,
      intervalBisectionFromEventFlow (intervalBisectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I M L R D S Q E H C P N =>
      rw [intervalBisectionToEventFlow, intervalBisectionFromEventFlow,
        intervalBisection_decode_encode I, intervalBisection_decode_encode M,
        intervalBisection_decode_encode L, intervalBisection_decode_encode R,
        intervalBisection_decode_encode D, intervalBisection_decode_encode S,
        intervalBisection_decode_encode Q, intervalBisection_decode_encode E,
        intervalBisection_decode_encode H, intervalBisection_decode_encode C,
        intervalBisection_decode_encode P, intervalBisection_decode_encode N]

private theorem intervalBisectionToEventFlow_injective {x y : IntervalBisectionUp} :
    intervalBisectionToEventFlow x = intervalBisectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      intervalBisectionFromEventFlow (intervalBisectionToEventFlow x) =
        intervalBisectionFromEventFlow (intervalBisectionToEventFlow y) :=
    congrArg intervalBisectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (intervalBisection_round_trip x).symm
      (Eq.trans hread (intervalBisection_round_trip y)))

instance intervalBisectionBHistCarrier : BHistCarrier IntervalBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := intervalBisectionToEventFlow
  fromEventFlow := intervalBisectionFromEventFlow

instance intervalBisectionChapterTasteGate : ChapterTasteGate IntervalBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change intervalBisectionFromEventFlow (intervalBisectionToEventFlow x) = some x
    exact intervalBisection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (intervalBisectionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate IntervalBisectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  intervalBisectionChapterTasteGate

theorem IntervalBisectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, intervalBisectionDecodeBHist (intervalBisectionEncodeBHist h) = h) ∧
      (∀ x : IntervalBisectionUp,
        intervalBisectionFromEventFlow (intervalBisectionToEventFlow x) = some x) ∧
      (∀ x y : IntervalBisectionUp,
        intervalBisectionToEventFlow x = intervalBisectionToEventFlow y → x = y) ∧
      intervalBisectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨intervalBisection_decode_encode,
      intervalBisection_round_trip,
      fun _ _ heq => intervalBisectionToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.IntervalBisectionUp
