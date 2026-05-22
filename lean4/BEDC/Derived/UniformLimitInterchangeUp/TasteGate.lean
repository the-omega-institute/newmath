import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformLimitInterchangeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformLimitInterchangeUp : Type where
  | mk (F L M R S T H C P N : BHist) : UniformLimitInterchangeUp
  deriving DecidableEq

def uniformLimitInterchangeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformLimitInterchangeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformLimitInterchangeEncodeBHist h

def uniformLimitInterchangeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformLimitInterchangeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformLimitInterchangeDecodeBHist tail)

private theorem uniformLimitInterchangeDecode_encode_bhist :
    ∀ h : BHist,
      uniformLimitInterchangeDecodeBHist
          (uniformLimitInterchangeEncodeBHist h) =
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

def uniformLimitInterchangeFields : UniformLimitInterchangeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformLimitInterchangeUp.mk F L M R S T H C P N => [F, L, M, R, S, T, H, C, P, N]

def uniformLimitInterchangeToEventFlow : UniformLimitInterchangeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformLimitInterchangeFields x).map uniformLimitInterchangeEncodeBHist

private def uniformLimitInterchangeRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => uniformLimitInterchangeRawAt n rest

private def uniformLimitInterchangeLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => uniformLimitInterchangeLengthEq n rest

def uniformLimitInterchangeFromEventFlow :
    EventFlow → Option UniformLimitInterchangeUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match uniformLimitInterchangeLengthEq 10 flow with
      | true =>
          some
            (UniformLimitInterchangeUp.mk
              (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeRawAt 0 flow))
              (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeRawAt 1 flow))
              (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeRawAt 2 flow))
              (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeRawAt 3 flow))
              (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeRawAt 4 flow))
              (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeRawAt 5 flow))
              (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeRawAt 6 flow))
              (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeRawAt 7 flow))
              (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeRawAt 8 flow))
              (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeRawAt 9 flow)))
      | false => none

private theorem uniformLimitInterchange_round_trip :
    ∀ x : UniformLimitInterchangeUp,
      uniformLimitInterchangeFromEventFlow
          (uniformLimitInterchangeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F L M R S T H C P N =>
      change
        some
          (UniformLimitInterchangeUp.mk
            (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEncodeBHist F))
            (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEncodeBHist L))
            (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEncodeBHist M))
            (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEncodeBHist R))
            (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEncodeBHist S))
            (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEncodeBHist T))
            (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEncodeBHist H))
            (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEncodeBHist C))
            (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEncodeBHist P))
            (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEncodeBHist N))) =
          some (UniformLimitInterchangeUp.mk F L M R S T H C P N)
      rw [uniformLimitInterchangeDecode_encode_bhist F,
        uniformLimitInterchangeDecode_encode_bhist L,
        uniformLimitInterchangeDecode_encode_bhist M,
        uniformLimitInterchangeDecode_encode_bhist R,
        uniformLimitInterchangeDecode_encode_bhist S,
        uniformLimitInterchangeDecode_encode_bhist T,
        uniformLimitInterchangeDecode_encode_bhist H,
        uniformLimitInterchangeDecode_encode_bhist C,
        uniformLimitInterchangeDecode_encode_bhist P,
        uniformLimitInterchangeDecode_encode_bhist N]

private theorem uniformLimitInterchangeToEventFlow_injective
    {x y : UniformLimitInterchangeUp} :
    uniformLimitInterchangeToEventFlow x =
        uniformLimitInterchangeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformLimitInterchangeFromEventFlow
          (uniformLimitInterchangeToEventFlow x) =
        uniformLimitInterchangeFromEventFlow
          (uniformLimitInterchangeToEventFlow y) :=
    congrArg uniformLimitInterchangeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformLimitInterchange_round_trip x).symm
      (Eq.trans hread (uniformLimitInterchange_round_trip y)))

private theorem uniformLimitInterchange_field_faithful :
    ∀ x y : UniformLimitInterchangeUp,
      uniformLimitInterchangeFields x = uniformLimitInterchangeFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 L1 M1 R1 S1 T1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 L2 M2 R2 S2 T2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance uniformLimitInterchangeBHistCarrier :
    BHistCarrier UniformLimitInterchangeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformLimitInterchangeToEventFlow
  fromEventFlow := uniformLimitInterchangeFromEventFlow

instance uniformLimitInterchangeChapterTasteGate :
    ChapterTasteGate UniformLimitInterchangeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformLimitInterchangeFromEventFlow
          (uniformLimitInterchangeToEventFlow x) =
        some x
    exact uniformLimitInterchange_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformLimitInterchangeToEventFlow_injective heq)

instance uniformLimitInterchangeFieldFaithful :
    FieldFaithful UniformLimitInterchangeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformLimitInterchangeFields
  field_faithful := uniformLimitInterchange_field_faithful

instance uniformLimitInterchangeNontrivial :
    Nontrivial UniformLimitInterchangeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformLimitInterchangeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformLimitInterchangeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformLimitInterchangeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformLimitInterchangeChapterTasteGate

theorem UniformLimitInterchangeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UniformLimitInterchangeUp) ∧
      Nonempty (FieldFaithful UniformLimitInterchangeUp) ∧
      Nonempty (Nontrivial UniformLimitInterchangeUp) ∧
      (∀ h : BHist,
        uniformLimitInterchangeDecodeBHist
            (uniformLimitInterchangeEncodeBHist h) =
          h) ∧
      (∀ x : UniformLimitInterchangeUp,
        uniformLimitInterchangeFromEventFlow
            (uniformLimitInterchangeToEventFlow x) =
          some x) ∧
      (∀ x y : UniformLimitInterchangeUp,
        uniformLimitInterchangeToEventFlow x =
            uniformLimitInterchangeToEventFlow y ->
          x = y) ∧
      uniformLimitInterchangeEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨Nonempty.intro uniformLimitInterchangeChapterTasteGate,
      Nonempty.intro uniformLimitInterchangeFieldFaithful,
      Nonempty.intro uniformLimitInterchangeNontrivial,
      uniformLimitInterchangeDecode_encode_bhist,
      uniformLimitInterchange_round_trip,
      (fun _ _ heq => uniformLimitInterchangeToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformLimitInterchangeUp.TasteGate
