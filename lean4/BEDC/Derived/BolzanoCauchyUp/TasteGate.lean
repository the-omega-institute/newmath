import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BolzanoCauchyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BolzanoCauchyUp : Type where
  | mk (S M D R E L H C P N : BHist) : BolzanoCauchyUp
  deriving DecidableEq

def bolzanoCauchyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bolzanoCauchyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bolzanoCauchyEncodeBHist h

def bolzanoCauchyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bolzanoCauchyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bolzanoCauchyDecodeBHist tail)

private theorem bolzanoCauchyDecodeEncodeBHist :
    ∀ h : BHist, bolzanoCauchyDecodeBHist (bolzanoCauchyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bolzanoCauchyFields : BolzanoCauchyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BolzanoCauchyUp.mk S M D R E L H C P N => [S, M, D, R, E, L, H, C, P, N]

def bolzanoCauchyToEventFlow : BolzanoCauchyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bolzanoCauchyFields x).map bolzanoCauchyEncodeBHist

private def bolzanoCauchyEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bolzanoCauchyEventAtDefault index rest

def bolzanoCauchyFromEventFlow (ef : EventFlow) : Option BolzanoCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BolzanoCauchyUp.mk
      (bolzanoCauchyDecodeBHist (bolzanoCauchyEventAtDefault 0 ef))
      (bolzanoCauchyDecodeBHist (bolzanoCauchyEventAtDefault 1 ef))
      (bolzanoCauchyDecodeBHist (bolzanoCauchyEventAtDefault 2 ef))
      (bolzanoCauchyDecodeBHist (bolzanoCauchyEventAtDefault 3 ef))
      (bolzanoCauchyDecodeBHist (bolzanoCauchyEventAtDefault 4 ef))
      (bolzanoCauchyDecodeBHist (bolzanoCauchyEventAtDefault 5 ef))
      (bolzanoCauchyDecodeBHist (bolzanoCauchyEventAtDefault 6 ef))
      (bolzanoCauchyDecodeBHist (bolzanoCauchyEventAtDefault 7 ef))
      (bolzanoCauchyDecodeBHist (bolzanoCauchyEventAtDefault 8 ef))
      (bolzanoCauchyDecodeBHist (bolzanoCauchyEventAtDefault 9 ef)))

private theorem BolzanoCauchyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BolzanoCauchyUp,
      bolzanoCauchyFromEventFlow (bolzanoCauchyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk S M D R E L H C P N =>
      change
        some
          (BolzanoCauchyUp.mk
            (bolzanoCauchyDecodeBHist (bolzanoCauchyEncodeBHist S))
            (bolzanoCauchyDecodeBHist (bolzanoCauchyEncodeBHist M))
            (bolzanoCauchyDecodeBHist (bolzanoCauchyEncodeBHist D))
            (bolzanoCauchyDecodeBHist (bolzanoCauchyEncodeBHist R))
            (bolzanoCauchyDecodeBHist (bolzanoCauchyEncodeBHist E))
            (bolzanoCauchyDecodeBHist (bolzanoCauchyEncodeBHist L))
            (bolzanoCauchyDecodeBHist (bolzanoCauchyEncodeBHist H))
            (bolzanoCauchyDecodeBHist (bolzanoCauchyEncodeBHist C))
            (bolzanoCauchyDecodeBHist (bolzanoCauchyEncodeBHist P))
            (bolzanoCauchyDecodeBHist (bolzanoCauchyEncodeBHist N))) =
          some (BolzanoCauchyUp.mk S M D R E L H C P N)
      rw [bolzanoCauchyDecodeEncodeBHist S,
        bolzanoCauchyDecodeEncodeBHist M,
        bolzanoCauchyDecodeEncodeBHist D,
        bolzanoCauchyDecodeEncodeBHist R,
        bolzanoCauchyDecodeEncodeBHist E,
        bolzanoCauchyDecodeEncodeBHist L,
        bolzanoCauchyDecodeEncodeBHist H,
        bolzanoCauchyDecodeEncodeBHist C,
        bolzanoCauchyDecodeEncodeBHist P,
        bolzanoCauchyDecodeEncodeBHist N]

private theorem bolzanoCauchyToEventFlow_injective {x y : BolzanoCauchyUp} :
    bolzanoCauchyToEventFlow x = bolzanoCauchyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bolzanoCauchyFromEventFlow (bolzanoCauchyToEventFlow x) =
        bolzanoCauchyFromEventFlow (bolzanoCauchyToEventFlow y) :=
    congrArg bolzanoCauchyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BolzanoCauchyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BolzanoCauchyTasteGate_single_carrier_alignment_round_trip y)))

instance bolzanoCauchyBHistCarrier : BHistCarrier BolzanoCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bolzanoCauchyToEventFlow
  fromEventFlow := bolzanoCauchyFromEventFlow

instance bolzanoCauchyChapterTasteGate : ChapterTasteGate BolzanoCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bolzanoCauchyFromEventFlow (bolzanoCauchyToEventFlow x) = some x
    exact BolzanoCauchyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bolzanoCauchyToEventFlow_injective heq)

theorem BolzanoCauchyTasteGate_single_carrier_alignment :
    (∀ h : BHist, bolzanoCauchyDecodeBHist (bolzanoCauchyEncodeBHist h) = h) ∧
      (∀ x : BolzanoCauchyUp,
        bolzanoCauchyFromEventFlow (bolzanoCauchyToEventFlow x) = some x) ∧
        (∀ x y : BolzanoCauchyUp,
          bolzanoCauchyToEventFlow x = bolzanoCauchyToEventFlow y → x = y) ∧
          bolzanoCauchyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨bolzanoCauchyDecodeEncodeBHist,
      BolzanoCauchyTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => bolzanoCauchyToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BolzanoCauchyUp
