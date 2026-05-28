import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LipschitzFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LipschitzFunctionUp : Type where
  | mk (X Y G K D H C P N : BHist) : LipschitzFunctionUp
  deriving DecidableEq

def lipschitzFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lipschitzFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lipschitzFunctionEncodeBHist h

def lipschitzFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lipschitzFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lipschitzFunctionDecodeBHist tail)

private theorem lipschitzFunctionDecode_encode :
    ∀ h : BHist, lipschitzFunctionDecodeBHist (lipschitzFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lipschitzFunctionToEventFlow : LipschitzFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LipschitzFunctionUp.mk X Y G K D H C P N =>
      [lipschitzFunctionEncodeBHist X,
        lipschitzFunctionEncodeBHist Y,
        lipschitzFunctionEncodeBHist G,
        lipschitzFunctionEncodeBHist K,
        lipschitzFunctionEncodeBHist D,
        lipschitzFunctionEncodeBHist H,
        lipschitzFunctionEncodeBHist C,
        lipschitzFunctionEncodeBHist P,
        lipschitzFunctionEncodeBHist N]

def lipschitzFunctionFromEventFlow : EventFlow → Option LipschitzFunctionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest =>
      match rest with
      | [] => none
      | Y :: rest =>
          match rest with
          | [] => none
          | G :: rest =>
              match rest with
              | [] => none
              | K :: rest =>
                  match rest with
                  | [] => none
                  | D :: rest =>
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
                                            (LipschitzFunctionUp.mk
                                              (lipschitzFunctionDecodeBHist X)
                                              (lipschitzFunctionDecodeBHist Y)
                                              (lipschitzFunctionDecodeBHist G)
                                              (lipschitzFunctionDecodeBHist K)
                                              (lipschitzFunctionDecodeBHist D)
                                              (lipschitzFunctionDecodeBHist H)
                                              (lipschitzFunctionDecodeBHist C)
                                              (lipschitzFunctionDecodeBHist P)
                                              (lipschitzFunctionDecodeBHist N))
                                      | _ :: _ => none

private theorem lipschitzFunction_round_trip :
    ∀ x : LipschitzFunctionUp,
      lipschitzFunctionFromEventFlow (lipschitzFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y G K D H C P N =>
      rw [lipschitzFunctionToEventFlow, lipschitzFunctionFromEventFlow,
        lipschitzFunctionDecode_encode X,
        lipschitzFunctionDecode_encode Y,
        lipschitzFunctionDecode_encode G,
        lipschitzFunctionDecode_encode K,
        lipschitzFunctionDecode_encode D,
        lipschitzFunctionDecode_encode H,
        lipschitzFunctionDecode_encode C,
        lipschitzFunctionDecode_encode P,
        lipschitzFunctionDecode_encode N]

private theorem lipschitzFunctionToEventFlow_injective {x y : LipschitzFunctionUp} :
    lipschitzFunctionToEventFlow x = lipschitzFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lipschitzFunctionFromEventFlow (lipschitzFunctionToEventFlow x) =
        lipschitzFunctionFromEventFlow (lipschitzFunctionToEventFlow y) :=
    congrArg lipschitzFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (lipschitzFunction_round_trip x).symm
      (Eq.trans hread (lipschitzFunction_round_trip y)))

instance lipschitzFunctionBHistCarrier : BHistCarrier LipschitzFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lipschitzFunctionToEventFlow
  fromEventFlow := lipschitzFunctionFromEventFlow

instance lipschitzFunctionChapterTasteGate : ChapterTasteGate LipschitzFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lipschitzFunctionFromEventFlow (lipschitzFunctionToEventFlow x) = some x
    exact lipschitzFunction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lipschitzFunctionToEventFlow_injective heq)

theorem LipschitzFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist, lipschitzFunctionDecodeBHist (lipschitzFunctionEncodeBHist h) = h) ∧
      (∀ x : LipschitzFunctionUp,
        lipschitzFunctionFromEventFlow (lipschitzFunctionToEventFlow x) = some x) ∧
      (∀ x y : LipschitzFunctionUp,
        lipschitzFunctionToEventFlow x = lipschitzFunctionToEventFlow y → x = y) ∧
      lipschitzFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨lipschitzFunctionDecode_encode,
      lipschitzFunction_round_trip,
      fun _ _ heq => lipschitzFunctionToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.LipschitzFunctionUp
