import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformLimitTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformLimitTheoremUp : Type where
  | mk (F L W R E X Y H C P N : BHist) : UniformLimitTheoremUp
  deriving DecidableEq

def uniformLimitTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformLimitTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformLimitTheoremEncodeBHist h

def uniformLimitTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformLimitTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformLimitTheoremDecodeBHist tail)

private theorem UniformLimitTheoremTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      uniformLimitTheoremDecodeBHist (uniformLimitTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def uniformLimitTheoremFields : UniformLimitTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformLimitTheoremUp.mk F L W R E X Y H C P N => [F, L, W, R, E, X, Y, H, C, P, N]

def uniformLimitTheoremToEventFlow : UniformLimitTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map uniformLimitTheoremEncodeBHist (uniformLimitTheoremFields x)

private def uniformLimitTheoremEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformLimitTheoremEventAtDefault index rest

def uniformLimitTheoremFromEventFlow (ef : EventFlow) : Option UniformLimitTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformLimitTheoremUp.mk
      (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEventAtDefault 0 ef))
      (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEventAtDefault 1 ef))
      (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEventAtDefault 2 ef))
      (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEventAtDefault 3 ef))
      (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEventAtDefault 4 ef))
      (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEventAtDefault 5 ef))
      (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEventAtDefault 6 ef))
      (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEventAtDefault 7 ef))
      (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEventAtDefault 8 ef))
      (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEventAtDefault 9 ef))
      (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEventAtDefault 10 ef)))

private theorem UniformLimitTheoremTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformLimitTheoremUp,
      uniformLimitTheoremFromEventFlow (uniformLimitTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F L W R E X Y H C P N =>
      change
        some
          (UniformLimitTheoremUp.mk
            (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEncodeBHist F))
            (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEncodeBHist L))
            (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEncodeBHist W))
            (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEncodeBHist R))
            (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEncodeBHist E))
            (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEncodeBHist X))
            (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEncodeBHist Y))
            (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEncodeBHist H))
            (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEncodeBHist C))
            (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEncodeBHist P))
            (uniformLimitTheoremDecodeBHist (uniformLimitTheoremEncodeBHist N))) =
          some (UniformLimitTheoremUp.mk F L W R E X Y H C P N)
      rw [UniformLimitTheoremTasteGate_single_carrier_alignment_decode F,
        UniformLimitTheoremTasteGate_single_carrier_alignment_decode L,
        UniformLimitTheoremTasteGate_single_carrier_alignment_decode W,
        UniformLimitTheoremTasteGate_single_carrier_alignment_decode R,
        UniformLimitTheoremTasteGate_single_carrier_alignment_decode E,
        UniformLimitTheoremTasteGate_single_carrier_alignment_decode X,
        UniformLimitTheoremTasteGate_single_carrier_alignment_decode Y,
        UniformLimitTheoremTasteGate_single_carrier_alignment_decode H,
        UniformLimitTheoremTasteGate_single_carrier_alignment_decode C,
        UniformLimitTheoremTasteGate_single_carrier_alignment_decode P,
        UniformLimitTheoremTasteGate_single_carrier_alignment_decode N]

private theorem UniformLimitTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformLimitTheoremUp} :
    uniformLimitTheoremToEventFlow x = uniformLimitTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformLimitTheoremFromEventFlow (uniformLimitTheoremToEventFlow x) =
        uniformLimitTheoremFromEventFlow (uniformLimitTheoremToEventFlow y) :=
    congrArg uniformLimitTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformLimitTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformLimitTheoremTasteGate_single_carrier_alignment_round_trip y)))

private theorem UniformLimitTheoremTasteGate_single_carrier_alignment_fields :
    ∀ x y : UniformLimitTheoremUp, uniformLimitTheoremFields x = uniformLimitTheoremFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 L1 W1 R1 E1 X1 Y1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 L2 W2 R2 E2 X2 Y2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance uniformLimitTheoremBHistCarrier : BHistCarrier UniformLimitTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformLimitTheoremToEventFlow
  fromEventFlow := uniformLimitTheoremFromEventFlow

instance uniformLimitTheoremChapterTasteGate : ChapterTasteGate UniformLimitTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformLimitTheoremFromEventFlow (uniformLimitTheoremToEventFlow x) = some x
    exact UniformLimitTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformLimitTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance uniformLimitTheoremFieldFaithful : FieldFaithful UniformLimitTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformLimitTheoremFields
  field_faithful := UniformLimitTheoremTasteGate_single_carrier_alignment_fields

instance uniformLimitTheoremNontrivial : BEDC.Meta.TasteGate.Nontrivial UniformLimitTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformLimitTheoremUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformLimitTheoremUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformLimitTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformLimitTheoremChapterTasteGate

theorem UniformLimitTheoremTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UniformLimitTheoremUp) ∧
      Nonempty (FieldFaithful UniformLimitTheoremUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial UniformLimitTheoremUp) ∧
          (∀ h : BHist, uniformLimitTheoremDecodeBHist
            (uniformLimitTheoremEncodeBHist h) = h) ∧
            (∀ x : UniformLimitTheoremUp,
              uniformLimitTheoremFromEventFlow (uniformLimitTheoremToEventFlow x) = some x) ∧
              uniformLimitTheoremEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨uniformLimitTheoremChapterTasteGate⟩,
      ⟨uniformLimitTheoremFieldFaithful⟩,
      ⟨uniformLimitTheoremNontrivial⟩,
      UniformLimitTheoremTasteGate_single_carrier_alignment_decode,
      UniformLimitTheoremTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.UniformLimitTheoremUp
