import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LimitUp : Type where
  | mk (stream readback dyadic realSeal transport continuation history provenance name : BHist) :
      LimitUp
  deriving DecidableEq

def limitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: limitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: limitEncodeBHist h

def limitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (limitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (limitDecodeBHist tail)

private theorem limitDecodeEncodeBHist :
    ∀ h : BHist, limitDecodeBHist (limitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem LimitTasteGate_single_carrier_alignment_decode_aux :
    ∀ h : BHist, limitDecodeBHist (limitEncodeBHist h) = h :=
  limitDecodeEncodeBHist

def limitFields : LimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LimitUp.mk stream readback dyadic realSeal transport continuation history provenance name =>
      [stream, readback, dyadic, realSeal, transport, continuation, history, provenance, name]

def limitToEventFlow : LimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (limitFields x).map limitEncodeBHist

def limitFromEventFlow : EventFlow → Option LimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | stream :: readback :: dyadic :: realSeal :: transport :: continuation :: history ::
      provenance :: name :: [] =>
      some
        (LimitUp.mk
          (limitDecodeBHist stream)
          (limitDecodeBHist readback)
          (limitDecodeBHist dyadic)
          (limitDecodeBHist realSeal)
          (limitDecodeBHist transport)
          (limitDecodeBHist continuation)
          (limitDecodeBHist history)
          (limitDecodeBHist provenance)
          (limitDecodeBHist name))
  | _ => none

private theorem limit_round_trip :
    ∀ x : LimitUp, limitFromEventFlow (limitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk stream readback dyadic realSeal transport continuation history provenance name =>
      simp only [limitToEventFlow, limitFields, limitFromEventFlow, List.map_cons,
        List.map_nil, limitDecodeEncodeBHist]

private theorem limitToEventFlow_injective {x y : LimitUp} :
    limitToEventFlow x = limitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      limitFromEventFlow (limitToEventFlow x) =
        limitFromEventFlow (limitToEventFlow y) :=
    congrArg limitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (limit_round_trip x).symm (Eq.trans hread (limit_round_trip y)))

private theorem limit_field_faithful :
    ∀ x y : LimitUp, limitFields x = limitFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk stream₁ readback₁ dyadic₁ realSeal₁ transport₁ continuation₁ history₁
      provenance₁ name₁ =>
      cases y with
      | mk stream₂ readback₂ dyadic₂ realSeal₂ transport₂ continuation₂ history₂
          provenance₂ name₂ =>
          injection hfields with hstream tail0
          injection tail0 with hreadback tail1
          injection tail1 with hdyadic tail2
          injection tail2 with hrealSeal tail3
          injection tail3 with htransport tail4
          injection tail4 with hcontinuation tail5
          injection tail5 with hhistory tail6
          injection tail6 with hprovenance tail7
          injection tail7 with hname _
          subst hstream
          subst hreadback
          subst hdyadic
          subst hrealSeal
          subst htransport
          subst hcontinuation
          subst hhistory
          subst hprovenance
          subst hname
          rfl

private theorem LimitTasteGate_single_carrier_alignment_round_trip_aux :
    ∀ x : LimitUp, limitFromEventFlow (limitToEventFlow x) = some x :=
  limit_round_trip

private theorem LimitTasteGate_single_carrier_alignment_injective_aux
    {x y : LimitUp} :
    limitToEventFlow x = limitToEventFlow y → x = y :=
  limitToEventFlow_injective

private theorem LimitTasteGate_single_carrier_alignment_fields_aux :
    ∀ x y : LimitUp, limitFields x = limitFields y → x = y :=
  limit_field_faithful

instance limitBHistCarrier : BHistCarrier LimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := limitToEventFlow
  fromEventFlow := limitFromEventFlow

instance limitChapterTasteGate : ChapterTasteGate LimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change limitFromEventFlow (limitToEventFlow x) = some x
    exact limit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (limitToEventFlow_injective heq)

instance limitFieldFaithful : FieldFaithful LimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := limitFields
  field_faithful := limit_field_faithful

instance limitNontrivial : Nontrivial LimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LimitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LimitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  limitChapterTasteGate

theorem LimitUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, limitDecodeBHist (limitEncodeBHist h) = h) ∧
      (∀ stream readback dyadic realSeal transport continuation history provenance name : BHist,
        limitFields
            (LimitUp.mk stream readback dyadic realSeal transport continuation history provenance
              name) =
          [stream, readback, dyadic, realSeal, transport, continuation, history, provenance,
            name]) ∧
        limitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · constructor
    · intro stream readback dyadic realSeal transport continuation history provenance name
      rfl
    · rfl

theorem LimitTasteGate_single_carrier_alignment :
    (∀ h : BHist, limitDecodeBHist (limitEncodeBHist h) = h) ∧
      (∀ x : LimitUp, limitFromEventFlow (limitToEventFlow x) = some x) ∧
      (∀ x y : LimitUp, limitToEventFlow x = limitToEventFlow y → x = y) ∧
      limitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact LimitTasteGate_single_carrier_alignment_decode_aux
  · constructor
    · exact LimitTasteGate_single_carrier_alignment_round_trip_aux
    · constructor
      · intro x y heq
        exact LimitTasteGate_single_carrier_alignment_injective_aux heq
      · rfl

end BEDC.Derived.LimitUp
