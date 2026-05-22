import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealMinMaxUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealMinMaxUp : Type where
  | mk (X Y RX RY SX SY D E C O L U H T P N : BHist) : RealMinMaxUp
  deriving DecidableEq

def realMinMaxEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realMinMaxEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realMinMaxEncodeBHist h

def realMinMaxDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realMinMaxDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realMinMaxDecodeBHist tail)

private theorem realMinMaxDecode_encode :
    ∀ h : BHist, realMinMaxDecodeBHist (realMinMaxEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realMinMaxFields : RealMinMaxUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealMinMaxUp.mk X Y RX RY SX SY D E C O L U H T P N =>
      [X, Y, RX, RY, SX, SY, D, E, C, O, L, U, H, T, P, N]

def realMinMaxToEventFlow : RealMinMaxUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map realMinMaxEncodeBHist (realMinMaxFields x)

private def realMinMaxEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realMinMaxEventAtDefault index rest

def realMinMaxFromEventFlow : EventFlow → Option RealMinMaxUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RealMinMaxUp.mk
        (realMinMaxDecodeBHist (realMinMaxEventAtDefault 0 ef))
        (realMinMaxDecodeBHist (realMinMaxEventAtDefault 1 ef))
        (realMinMaxDecodeBHist (realMinMaxEventAtDefault 2 ef))
        (realMinMaxDecodeBHist (realMinMaxEventAtDefault 3 ef))
        (realMinMaxDecodeBHist (realMinMaxEventAtDefault 4 ef))
        (realMinMaxDecodeBHist (realMinMaxEventAtDefault 5 ef))
        (realMinMaxDecodeBHist (realMinMaxEventAtDefault 6 ef))
        (realMinMaxDecodeBHist (realMinMaxEventAtDefault 7 ef))
        (realMinMaxDecodeBHist (realMinMaxEventAtDefault 8 ef))
        (realMinMaxDecodeBHist (realMinMaxEventAtDefault 9 ef))
        (realMinMaxDecodeBHist (realMinMaxEventAtDefault 10 ef))
        (realMinMaxDecodeBHist (realMinMaxEventAtDefault 11 ef))
        (realMinMaxDecodeBHist (realMinMaxEventAtDefault 12 ef))
        (realMinMaxDecodeBHist (realMinMaxEventAtDefault 13 ef))
        (realMinMaxDecodeBHist (realMinMaxEventAtDefault 14 ef))
        (realMinMaxDecodeBHist (realMinMaxEventAtDefault 15 ef)))

private theorem realMinMax_round_trip :
    ∀ x : RealMinMaxUp, realMinMaxFromEventFlow (realMinMaxToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y RX RY SX SY D E C O L U H T P N =>
      change
        some
          (RealMinMaxUp.mk
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist X))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist Y))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist RX))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist RY))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist SX))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist SY))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist D))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist E))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist C))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist O))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist L))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist U))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist H))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist T))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist P))
            (realMinMaxDecodeBHist (realMinMaxEncodeBHist N))) =
          some (RealMinMaxUp.mk X Y RX RY SX SY D E C O L U H T P N)
      rw [realMinMaxDecode_encode X, realMinMaxDecode_encode Y,
        realMinMaxDecode_encode RX, realMinMaxDecode_encode RY,
        realMinMaxDecode_encode SX, realMinMaxDecode_encode SY,
        realMinMaxDecode_encode D, realMinMaxDecode_encode E, realMinMaxDecode_encode C,
        realMinMaxDecode_encode O, realMinMaxDecode_encode L, realMinMaxDecode_encode U,
        realMinMaxDecode_encode H, realMinMaxDecode_encode T, realMinMaxDecode_encode P,
        realMinMaxDecode_encode N]

private theorem realMinMaxToEventFlow_injective {x y : RealMinMaxUp} :
    realMinMaxToEventFlow x = realMinMaxToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realMinMaxFromEventFlow (realMinMaxToEventFlow x) =
        realMinMaxFromEventFlow (realMinMaxToEventFlow y) :=
    congrArg realMinMaxFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realMinMax_round_trip x).symm
      (Eq.trans hread (realMinMax_round_trip y)))

private theorem realMinMax_field_faithful :
    ∀ x y : RealMinMaxUp, realMinMaxFields x = realMinMaxFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk X₁ Y₁ RX₁ RY₁ SX₁ SY₁ D₁ E₁ C₁ O₁ L₁ U₁ H₁ T₁ P₁ N₁ =>
      cases y with
      | mk X₂ Y₂ RX₂ RY₂ SX₂ SY₂ D₂ E₂ C₂ O₂ L₂ U₂ H₂ T₂ P₂ N₂ =>
          cases h
          rfl

instance realMinMaxBHistCarrier : BHistCarrier RealMinMaxUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realMinMaxToEventFlow
  fromEventFlow := realMinMaxFromEventFlow

instance realMinMaxChapterTasteGate : ChapterTasteGate RealMinMaxUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realMinMaxFromEventFlow (realMinMaxToEventFlow x) = some x
    exact realMinMax_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realMinMaxToEventFlow_injective heq)

instance realMinMaxFieldFaithful : FieldFaithful RealMinMaxUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realMinMaxFields
  field_faithful := realMinMax_field_faithful

def taste_gate : ChapterTasteGate RealMinMaxUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realMinMaxChapterTasteGate

theorem RealMinMaxUp_single_carrier_alignment :
    (∀ h : BHist, realMinMaxDecodeBHist (realMinMaxEncodeBHist h) = h) ∧
      (∀ x : RealMinMaxUp, realMinMaxFromEventFlow (realMinMaxToEventFlow x) = some x) ∧
      (∀ x y : RealMinMaxUp,
        realMinMaxToEventFlow x = realMinMaxToEventFlow y → x = y) ∧
      realMinMaxEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨realMinMaxDecode_encode,
      realMinMax_round_trip,
      (fun _ _ heq => realMinMaxToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealMinMaxUp
