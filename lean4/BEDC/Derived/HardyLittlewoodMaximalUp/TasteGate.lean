import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HardyLittlewoodMaximalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HardyLittlewoodMaximalUp : Type where
  | mk (X B R A V D E H C P N : BHist) : HardyLittlewoodMaximalUp
  deriving DecidableEq

def hardyLittlewoodMaximalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hardyLittlewoodMaximalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hardyLittlewoodMaximalEncodeBHist h

def hardyLittlewoodMaximalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hardyLittlewoodMaximalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hardyLittlewoodMaximalDecodeBHist tail)

private theorem hardyLittlewoodMaximal_decode_encode_bhist :
    ∀ h : BHist,
      hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hardyLittlewoodMaximalFields : HardyLittlewoodMaximalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HardyLittlewoodMaximalUp.mk X B R A V D E H C P N => [X, B, R, A, V, D, E, H, C, P, N]

def hardyLittlewoodMaximalToEventFlow : HardyLittlewoodMaximalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hardyLittlewoodMaximalFields x).map hardyLittlewoodMaximalEncodeBHist

private def hardyLittlewoodMaximalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hardyLittlewoodMaximalEventAtDefault index rest

def hardyLittlewoodMaximalFromEventFlow (ef : EventFlow) :
    Option HardyLittlewoodMaximalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HardyLittlewoodMaximalUp.mk
      (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEventAtDefault 0 ef))
      (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEventAtDefault 1 ef))
      (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEventAtDefault 2 ef))
      (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEventAtDefault 3 ef))
      (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEventAtDefault 4 ef))
      (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEventAtDefault 5 ef))
      (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEventAtDefault 6 ef))
      (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEventAtDefault 7 ef))
      (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEventAtDefault 8 ef))
      (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEventAtDefault 9 ef))
      (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEventAtDefault 10 ef)))

private theorem hardyLittlewoodMaximal_round_trip :
    ∀ x : HardyLittlewoodMaximalUp,
      hardyLittlewoodMaximalFromEventFlow (hardyLittlewoodMaximalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X B R A V D E H C P N =>
      change
        some
          (HardyLittlewoodMaximalUp.mk
            (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEncodeBHist X))
            (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEncodeBHist B))
            (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEncodeBHist R))
            (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEncodeBHist A))
            (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEncodeBHist V))
            (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEncodeBHist D))
            (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEncodeBHist E))
            (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEncodeBHist H))
            (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEncodeBHist C))
            (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEncodeBHist P))
            (hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEncodeBHist N))) =
          some (HardyLittlewoodMaximalUp.mk X B R A V D E H C P N)
      rw [hardyLittlewoodMaximal_decode_encode_bhist X,
        hardyLittlewoodMaximal_decode_encode_bhist B,
        hardyLittlewoodMaximal_decode_encode_bhist R,
        hardyLittlewoodMaximal_decode_encode_bhist A,
        hardyLittlewoodMaximal_decode_encode_bhist V,
        hardyLittlewoodMaximal_decode_encode_bhist D,
        hardyLittlewoodMaximal_decode_encode_bhist E,
        hardyLittlewoodMaximal_decode_encode_bhist H,
        hardyLittlewoodMaximal_decode_encode_bhist C,
        hardyLittlewoodMaximal_decode_encode_bhist P,
        hardyLittlewoodMaximal_decode_encode_bhist N]

private theorem hardyLittlewoodMaximalToEventFlow_injective {x y : HardyLittlewoodMaximalUp} :
    hardyLittlewoodMaximalToEventFlow x = hardyLittlewoodMaximalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hardyLittlewoodMaximalFromEventFlow (hardyLittlewoodMaximalToEventFlow x) =
        hardyLittlewoodMaximalFromEventFlow (hardyLittlewoodMaximalToEventFlow y) :=
    congrArg hardyLittlewoodMaximalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hardyLittlewoodMaximal_round_trip x).symm
      (Eq.trans hread (hardyLittlewoodMaximal_round_trip y)))

instance hardyLittlewoodMaximalBHistCarrier : BHistCarrier HardyLittlewoodMaximalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hardyLittlewoodMaximalToEventFlow
  fromEventFlow := hardyLittlewoodMaximalFromEventFlow

instance hardyLittlewoodMaximalChapterTasteGate : ChapterTasteGate HardyLittlewoodMaximalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hardyLittlewoodMaximalFromEventFlow (hardyLittlewoodMaximalToEventFlow x) = some x
    exact hardyLittlewoodMaximal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hardyLittlewoodMaximalToEventFlow_injective heq)

theorem HardyLittlewoodMaximalTasteGate_single_carrier_alignment :
    (∀ h : BHist, hardyLittlewoodMaximalDecodeBHist (hardyLittlewoodMaximalEncodeBHist h) = h) ∧
      (∀ x : HardyLittlewoodMaximalUp,
        hardyLittlewoodMaximalFromEventFlow (hardyLittlewoodMaximalToEventFlow x) = some x) ∧
        (∀ x y : HardyLittlewoodMaximalUp,
          hardyLittlewoodMaximalToEventFlow x = hardyLittlewoodMaximalToEventFlow y → x = y) ∧
          hardyLittlewoodMaximalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨hardyLittlewoodMaximal_decode_encode_bhist,
      hardyLittlewoodMaximal_round_trip,
      (fun _ _ heq => hardyLittlewoodMaximalToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HardyLittlewoodMaximalUp
