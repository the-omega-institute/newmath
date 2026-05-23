import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformEntourageRegularNameUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformEntourageRegularNameUp : Type where
  | mk (U F W R Q T H C P N : BHist) : UniformEntourageRegularNameUp
  deriving DecidableEq

def uniformEntourageRegularNameEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformEntourageRegularNameEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformEntourageRegularNameEncodeBHist h

def uniformEntourageRegularNameDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformEntourageRegularNameDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformEntourageRegularNameDecodeBHist tail)

private theorem UniformEntourageRegularNameTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      uniformEntourageRegularNameDecodeBHist
        (uniformEntourageRegularNameEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformEntourageRegularNameFields : UniformEntourageRegularNameUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformEntourageRegularNameUp.mk U F W R Q T H C P N => [U, F, W, R, Q, T, H, C, P, N]

def uniformEntourageRegularNameToEventFlow : UniformEntourageRegularNameUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (uniformEntourageRegularNameFields x).map uniformEntourageRegularNameEncodeBHist

private def uniformEntourageRegularNameEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformEntourageRegularNameEventAtDefault index rest

def uniformEntourageRegularNameFromEventFlow
    (ef : EventFlow) : Option UniformEntourageRegularNameUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformEntourageRegularNameUp.mk
      (uniformEntourageRegularNameDecodeBHist
        (uniformEntourageRegularNameEventAtDefault 0 ef))
      (uniformEntourageRegularNameDecodeBHist
        (uniformEntourageRegularNameEventAtDefault 1 ef))
      (uniformEntourageRegularNameDecodeBHist
        (uniformEntourageRegularNameEventAtDefault 2 ef))
      (uniformEntourageRegularNameDecodeBHist
        (uniformEntourageRegularNameEventAtDefault 3 ef))
      (uniformEntourageRegularNameDecodeBHist
        (uniformEntourageRegularNameEventAtDefault 4 ef))
      (uniformEntourageRegularNameDecodeBHist
        (uniformEntourageRegularNameEventAtDefault 5 ef))
      (uniformEntourageRegularNameDecodeBHist
        (uniformEntourageRegularNameEventAtDefault 6 ef))
      (uniformEntourageRegularNameDecodeBHist
        (uniformEntourageRegularNameEventAtDefault 7 ef))
      (uniformEntourageRegularNameDecodeBHist
        (uniformEntourageRegularNameEventAtDefault 8 ef))
      (uniformEntourageRegularNameDecodeBHist
        (uniformEntourageRegularNameEventAtDefault 9 ef)))

private theorem UniformEntourageRegularNameTasteGate_single_carrier_alignment_round_trip :
    forall x : UniformEntourageRegularNameUp,
      uniformEntourageRegularNameFromEventFlow
        (uniformEntourageRegularNameToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk U F W R Q T H C P N =>
      change
        some
          (UniformEntourageRegularNameUp.mk
            (uniformEntourageRegularNameDecodeBHist
              (uniformEntourageRegularNameEncodeBHist U))
            (uniformEntourageRegularNameDecodeBHist
              (uniformEntourageRegularNameEncodeBHist F))
            (uniformEntourageRegularNameDecodeBHist
              (uniformEntourageRegularNameEncodeBHist W))
            (uniformEntourageRegularNameDecodeBHist
              (uniformEntourageRegularNameEncodeBHist R))
            (uniformEntourageRegularNameDecodeBHist
              (uniformEntourageRegularNameEncodeBHist Q))
            (uniformEntourageRegularNameDecodeBHist
              (uniformEntourageRegularNameEncodeBHist T))
            (uniformEntourageRegularNameDecodeBHist
              (uniformEntourageRegularNameEncodeBHist H))
            (uniformEntourageRegularNameDecodeBHist
              (uniformEntourageRegularNameEncodeBHist C))
            (uniformEntourageRegularNameDecodeBHist
              (uniformEntourageRegularNameEncodeBHist P))
            (uniformEntourageRegularNameDecodeBHist
              (uniformEntourageRegularNameEncodeBHist N))) =
          some (UniformEntourageRegularNameUp.mk U F W R Q T H C P N)
      rw [UniformEntourageRegularNameTasteGate_single_carrier_alignment_decode U,
        UniformEntourageRegularNameTasteGate_single_carrier_alignment_decode F,
        UniformEntourageRegularNameTasteGate_single_carrier_alignment_decode W,
        UniformEntourageRegularNameTasteGate_single_carrier_alignment_decode R,
        UniformEntourageRegularNameTasteGate_single_carrier_alignment_decode Q,
        UniformEntourageRegularNameTasteGate_single_carrier_alignment_decode T,
        UniformEntourageRegularNameTasteGate_single_carrier_alignment_decode H,
        UniformEntourageRegularNameTasteGate_single_carrier_alignment_decode C,
        UniformEntourageRegularNameTasteGate_single_carrier_alignment_decode P,
        UniformEntourageRegularNameTasteGate_single_carrier_alignment_decode N]

private theorem UniformEntourageRegularNameTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformEntourageRegularNameUp} :
    uniformEntourageRegularNameToEventFlow x =
      uniformEntourageRegularNameToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformEntourageRegularNameFromEventFlow (uniformEntourageRegularNameToEventFlow x) =
        uniformEntourageRegularNameFromEventFlow (uniformEntourageRegularNameToEventFlow y) :=
    congrArg uniformEntourageRegularNameFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformEntourageRegularNameTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformEntourageRegularNameTasteGate_single_carrier_alignment_round_trip y)))

private theorem UniformEntourageRegularNameTasteGate_single_carrier_alignment_fields :
    forall x y : UniformEntourageRegularNameUp,
      uniformEntourageRegularNameFields x = uniformEntourageRegularNameFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U1 F1 W1 R1 Q1 T1 H1 C1 P1 N1 =>
      cases y with
      | mk U2 F2 W2 R2 Q2 T2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance uniformEntourageRegularNameBHistCarrier :
    BHistCarrier UniformEntourageRegularNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformEntourageRegularNameToEventFlow
  fromEventFlow := uniformEntourageRegularNameFromEventFlow

instance uniformEntourageRegularNameChapterTasteGate :
    ChapterTasteGate UniformEntourageRegularNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformEntourageRegularNameFromEventFlow
        (uniformEntourageRegularNameToEventFlow x) = some x
    exact UniformEntourageRegularNameTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (UniformEntourageRegularNameTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance uniformEntourageRegularNameFieldFaithful :
    FieldFaithful UniformEntourageRegularNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformEntourageRegularNameFields
  field_faithful := UniformEntourageRegularNameTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate UniformEntourageRegularNameUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformEntourageRegularNameChapterTasteGate

theorem UniformEntourageRegularNameTasteGate_single_carrier_alignment :
    (forall h : BHist,
      uniformEntourageRegularNameDecodeBHist
        (uniformEntourageRegularNameEncodeBHist h) = h) /\
      (forall x : UniformEntourageRegularNameUp,
        uniformEntourageRegularNameFromEventFlow
          (uniformEntourageRegularNameToEventFlow x) = some x) /\
        (forall x y : UniformEntourageRegularNameUp,
          uniformEntourageRegularNameToEventFlow x =
            uniformEntourageRegularNameToEventFlow y -> x = y) /\
          uniformEntourageRegularNameEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨UniformEntourageRegularNameTasteGate_single_carrier_alignment_decode,
      UniformEntourageRegularNameTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        UniformEntourageRegularNameTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformEntourageRegularNameUp
