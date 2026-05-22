import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformLimitContinuousUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformLimitContinuousUp : Type where
  | mk (F U M W R E H C P N : BHist) : UniformLimitContinuousUp
  deriving DecidableEq

def uniformLimitContinuousEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformLimitContinuousEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformLimitContinuousEncodeBHist h

def uniformLimitContinuousDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformLimitContinuousDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformLimitContinuousDecodeBHist tail)

private theorem uniformLimitContinuousDecode_encode_bhist :
    ∀ h : BHist,
      uniformLimitContinuousDecodeBHist
          (uniformLimitContinuousEncodeBHist h) =
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

def uniformLimitContinuousFields : UniformLimitContinuousUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformLimitContinuousUp.mk F U M W R E H C P N => [F, U, M, W, R, E, H, C, P, N]

def uniformLimitContinuousToEventFlow : UniformLimitContinuousUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformLimitContinuousFields x).map uniformLimitContinuousEncodeBHist

private def uniformLimitContinuousRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => uniformLimitContinuousRawAt n rest

private def uniformLimitContinuousLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => uniformLimitContinuousLengthEq n rest

def uniformLimitContinuousFromEventFlow :
    EventFlow → Option UniformLimitContinuousUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match uniformLimitContinuousLengthEq 10 flow with
      | true =>
          some
            (UniformLimitContinuousUp.mk
              (uniformLimitContinuousDecodeBHist (uniformLimitContinuousRawAt 0 flow))
              (uniformLimitContinuousDecodeBHist (uniformLimitContinuousRawAt 1 flow))
              (uniformLimitContinuousDecodeBHist (uniformLimitContinuousRawAt 2 flow))
              (uniformLimitContinuousDecodeBHist (uniformLimitContinuousRawAt 3 flow))
              (uniformLimitContinuousDecodeBHist (uniformLimitContinuousRawAt 4 flow))
              (uniformLimitContinuousDecodeBHist (uniformLimitContinuousRawAt 5 flow))
              (uniformLimitContinuousDecodeBHist (uniformLimitContinuousRawAt 6 flow))
              (uniformLimitContinuousDecodeBHist (uniformLimitContinuousRawAt 7 flow))
              (uniformLimitContinuousDecodeBHist (uniformLimitContinuousRawAt 8 flow))
              (uniformLimitContinuousDecodeBHist (uniformLimitContinuousRawAt 9 flow)))
      | false => none

private theorem uniformLimitContinuous_round_trip :
    ∀ x : UniformLimitContinuousUp,
      uniformLimitContinuousFromEventFlow
          (uniformLimitContinuousToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F U M W R E H C P N =>
      change
        some
          (UniformLimitContinuousUp.mk
            (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEncodeBHist F))
            (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEncodeBHist U))
            (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEncodeBHist M))
            (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEncodeBHist W))
            (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEncodeBHist R))
            (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEncodeBHist E))
            (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEncodeBHist H))
            (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEncodeBHist C))
            (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEncodeBHist P))
            (uniformLimitContinuousDecodeBHist (uniformLimitContinuousEncodeBHist N))) =
          some (UniformLimitContinuousUp.mk F U M W R E H C P N)
      rw [uniformLimitContinuousDecode_encode_bhist F,
        uniformLimitContinuousDecode_encode_bhist U,
        uniformLimitContinuousDecode_encode_bhist M,
        uniformLimitContinuousDecode_encode_bhist W,
        uniformLimitContinuousDecode_encode_bhist R,
        uniformLimitContinuousDecode_encode_bhist E,
        uniformLimitContinuousDecode_encode_bhist H,
        uniformLimitContinuousDecode_encode_bhist C,
        uniformLimitContinuousDecode_encode_bhist P,
        uniformLimitContinuousDecode_encode_bhist N]

private theorem uniformLimitContinuousToEventFlow_injective
    {x y : UniformLimitContinuousUp} :
    uniformLimitContinuousToEventFlow x =
        uniformLimitContinuousToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformLimitContinuousFromEventFlow
          (uniformLimitContinuousToEventFlow x) =
        uniformLimitContinuousFromEventFlow
          (uniformLimitContinuousToEventFlow y) :=
    congrArg uniformLimitContinuousFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformLimitContinuous_round_trip x).symm
      (Eq.trans hread (uniformLimitContinuous_round_trip y)))

private theorem uniformLimitContinuous_field_faithful :
    ∀ x y : UniformLimitContinuousUp,
      uniformLimitContinuousFields x = uniformLimitContinuousFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 U1 M1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 U2 M2 W2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance uniformLimitContinuousBHistCarrier :
    BHistCarrier UniformLimitContinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformLimitContinuousToEventFlow
  fromEventFlow := uniformLimitContinuousFromEventFlow

instance uniformLimitContinuousChapterTasteGate :
    ChapterTasteGate UniformLimitContinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformLimitContinuousFromEventFlow
          (uniformLimitContinuousToEventFlow x) =
        some x
    exact uniformLimitContinuous_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformLimitContinuousToEventFlow_injective heq)

instance uniformLimitContinuousFieldFaithful :
    FieldFaithful UniformLimitContinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformLimitContinuousFields
  field_faithful := uniformLimitContinuous_field_faithful

instance uniformLimitContinuousNontrivial :
    Nontrivial UniformLimitContinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformLimitContinuousUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformLimitContinuousUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformLimitContinuousUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformLimitContinuousChapterTasteGate

theorem UniformLimitContinuousTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UniformLimitContinuousUp) ∧
      Nonempty (FieldFaithful UniformLimitContinuousUp) ∧
      Nonempty (Nontrivial UniformLimitContinuousUp) ∧
      (∀ h : BHist,
        uniformLimitContinuousDecodeBHist
            (uniformLimitContinuousEncodeBHist h) =
          h) ∧
      (∀ x : UniformLimitContinuousUp,
        uniformLimitContinuousFromEventFlow
            (uniformLimitContinuousToEventFlow x) =
          some x) ∧
      (∀ x y : UniformLimitContinuousUp,
        uniformLimitContinuousToEventFlow x =
            uniformLimitContinuousToEventFlow y ->
          x = y) ∧
      uniformLimitContinuousEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨Nonempty.intro uniformLimitContinuousChapterTasteGate,
      Nonempty.intro uniformLimitContinuousFieldFaithful,
      Nonempty.intro uniformLimitContinuousNontrivial,
      uniformLimitContinuousDecode_encode_bhist,
      uniformLimitContinuous_round_trip,
      (fun _ _ heq => uniformLimitContinuousToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformLimitContinuousUp.TasteGate
