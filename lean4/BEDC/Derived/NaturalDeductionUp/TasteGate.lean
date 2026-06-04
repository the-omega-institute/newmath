import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NaturalDeductionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NaturalDeductionUp : Type where
  | mk (A R S Q B T H K P N : BHist) : NaturalDeductionUp
  deriving DecidableEq

def naturalDeductionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: naturalDeductionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: naturalDeductionEncodeBHist h

def naturalDeductionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (naturalDeductionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (naturalDeductionDecodeBHist tail)

private theorem naturalDeductionDecode_encode_bhist :
    ∀ h : BHist, naturalDeductionDecodeBHist (naturalDeductionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def naturalDeductionFields : NaturalDeductionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NaturalDeductionUp.mk A R S Q B T H K P N => [A, R, S, Q, B, T, H, K, P, N]

def naturalDeductionToEventFlow : NaturalDeductionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (naturalDeductionFields x).map naturalDeductionEncodeBHist

private def naturalDeductionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => naturalDeductionEventAt index rest

def naturalDeductionFromEventFlow (ef : EventFlow) : Option NaturalDeductionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NaturalDeductionUp.mk
      (naturalDeductionDecodeBHist (naturalDeductionEventAt 0 ef))
      (naturalDeductionDecodeBHist (naturalDeductionEventAt 1 ef))
      (naturalDeductionDecodeBHist (naturalDeductionEventAt 2 ef))
      (naturalDeductionDecodeBHist (naturalDeductionEventAt 3 ef))
      (naturalDeductionDecodeBHist (naturalDeductionEventAt 4 ef))
      (naturalDeductionDecodeBHist (naturalDeductionEventAt 5 ef))
      (naturalDeductionDecodeBHist (naturalDeductionEventAt 6 ef))
      (naturalDeductionDecodeBHist (naturalDeductionEventAt 7 ef))
      (naturalDeductionDecodeBHist (naturalDeductionEventAt 8 ef))
      (naturalDeductionDecodeBHist (naturalDeductionEventAt 9 ef)))

private theorem naturalDeduction_round_trip (x : NaturalDeductionUp) :
    naturalDeductionFromEventFlow (naturalDeductionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A R S Q B T H K P N =>
      change
        some
          (NaturalDeductionUp.mk
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist A))
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist R))
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist S))
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist Q))
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist B))
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist T))
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist H))
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist K))
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist P))
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist N))) =
          some (NaturalDeductionUp.mk A R S Q B T H K P N)
      rw [naturalDeductionDecode_encode_bhist A, naturalDeductionDecode_encode_bhist R,
        naturalDeductionDecode_encode_bhist S, naturalDeductionDecode_encode_bhist Q,
        naturalDeductionDecode_encode_bhist B, naturalDeductionDecode_encode_bhist T,
        naturalDeductionDecode_encode_bhist H, naturalDeductionDecode_encode_bhist K,
        naturalDeductionDecode_encode_bhist P, naturalDeductionDecode_encode_bhist N]

private theorem naturalDeductionToEventFlow_injective {x y : NaturalDeductionUp} :
    naturalDeductionToEventFlow x = naturalDeductionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      naturalDeductionFromEventFlow (naturalDeductionToEventFlow x) =
        naturalDeductionFromEventFlow (naturalDeductionToEventFlow y) :=
    congrArg naturalDeductionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (naturalDeduction_round_trip x).symm
      (Eq.trans hread (naturalDeduction_round_trip y)))

instance naturalDeductionBHistCarrier : BHistCarrier NaturalDeductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := naturalDeductionToEventFlow
  fromEventFlow := naturalDeductionFromEventFlow

instance naturalDeductionChapterTasteGate : ChapterTasteGate NaturalDeductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change naturalDeductionFromEventFlow (naturalDeductionToEventFlow x) = some x
    exact naturalDeduction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (naturalDeductionToEventFlow_injective heq)

def NaturalDeductionCarrier (A R S Q B T H K P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  UnaryHistory A ∧ UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory Q ∧
    UnaryHistory B ∧ UnaryHistory T ∧ UnaryHistory H ∧ UnaryHistory K ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont A R S ∧ Cont S Q K ∧ hsame T H

end BEDC.Derived.NaturalDeductionUp
