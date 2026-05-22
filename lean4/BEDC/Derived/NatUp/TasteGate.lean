import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NatUp : Type where
  | mk (carrier successor induction name : BHist) : NatUp
  deriving DecidableEq

def natUpEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: natUpEncodeBHist h
  | BHist.e1 h => BMark.b1 :: natUpEncodeBHist h

def natUpDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (natUpDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (natUpDecodeBHist tail)

private theorem NatUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, natUpDecodeBHist (natUpEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def natUpFields : NatUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NatUp.mk carrier successor induction name => [carrier, successor, induction, name]

def natUpToEventFlow : NatUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (natUpFields x).map natUpEncodeBHist

private def natUpEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => natUpEventAtDefault index rest

def natUpFromEventFlow (ef : EventFlow) : Option NatUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NatUp.mk
      (natUpDecodeBHist (natUpEventAtDefault 0 ef))
      (natUpDecodeBHist (natUpEventAtDefault 1 ef))
      (natUpDecodeBHist (natUpEventAtDefault 2 ef))
      (natUpDecodeBHist (natUpEventAtDefault 3 ef)))

private theorem natUp_mk_congr
    {carrier carrier' successor successor' induction induction' name name' : BHist}
    (hCarrier : carrier' = carrier) (hSuccessor : successor' = successor)
    (hInduction : induction' = induction) (hName : name' = name) :
    NatUp.mk carrier' successor' induction' name' =
      NatUp.mk carrier successor induction name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hCarrier
  cases hSuccessor
  cases hInduction
  cases hName
  rfl

private theorem NatUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : NatUp, natUpFromEventFlow (natUpToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk carrier successor induction name =>
      exact congrArg some
        (natUp_mk_congr
          (NatUpTasteGate_single_carrier_alignment_decode carrier)
          (NatUpTasteGate_single_carrier_alignment_decode successor)
          (NatUpTasteGate_single_carrier_alignment_decode induction)
          (NatUpTasteGate_single_carrier_alignment_decode name))

private theorem NatUpToEventFlow_injective {x y : NatUp} :
    natUpToEventFlow x = natUpToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      natUpFromEventFlow (natUpToEventFlow x) =
        natUpFromEventFlow (natUpToEventFlow y) :=
    congrArg natUpFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NatUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NatUpTasteGate_single_carrier_alignment_round_trip y)))

instance natUpBHistCarrier : BHistCarrier NatUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := natUpToEventFlow
  fromEventFlow := natUpFromEventFlow

instance natUpChapterTasteGate : ChapterTasteGate NatUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change natUpFromEventFlow (natUpToEventFlow x) = some x
    exact NatUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NatUpToEventFlow_injective heq)

instance natUpFieldFaithful : FieldFaithful NatUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := natUpFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk carrier₁ successor₁ induction₁ name₁ =>
        cases y with
        | mk carrier₂ successor₂ induction₂ name₂ =>
            injection h with hCarrier rest₁
            injection rest₁ with hSuccessor rest₂
            injection rest₂ with hInduction rest₃
            injection rest₃ with hName _
            cases hCarrier
            cases hSuccessor
            cases hInduction
            cases hName
            rfl

instance natUpNontrivial : Nontrivial NatUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NatUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NatUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty, by
        intro h
        injection h with hCarrier _ _ _
        cases hCarrier⟩

def taste_gate : ChapterTasteGate NatUp :=
  -- BEDC touchpoint anchor: BHist BMark
  natUpChapterTasteGate

theorem NatUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, natUpDecodeBHist (natUpEncodeBHist h) = h) ∧
      (∀ x : NatUp, natUpFromEventFlow (natUpToEventFlow x) = some x) ∧
        (∀ x y : NatUp, natUpToEventFlow x = natUpToEventFlow y → x = y) ∧
          natUpEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨NatUpTasteGate_single_carrier_alignment_decode,
      NatUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => NatUpToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.NatUp
