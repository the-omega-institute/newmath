import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DominatedConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DominatedConvergenceUp : Type where
  | mk (M I F G L R E T H C P N : BHist) : DominatedConvergenceUp
  deriving DecidableEq

def dominatedConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dominatedConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dominatedConvergenceEncodeBHist h

def dominatedConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dominatedConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dominatedConvergenceDecodeBHist tail)

private theorem dominatedConvergence_decode_encode_bhist :
    ∀ h : BHist,
      dominatedConvergenceDecodeBHist (dominatedConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dominatedConvergenceToEventFlow : DominatedConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DominatedConvergenceUp.mk M I F G L R E T H C P N =>
      [dominatedConvergenceEncodeBHist M,
        dominatedConvergenceEncodeBHist I,
        dominatedConvergenceEncodeBHist F,
        dominatedConvergenceEncodeBHist G,
        dominatedConvergenceEncodeBHist L,
        dominatedConvergenceEncodeBHist R,
        dominatedConvergenceEncodeBHist E,
        dominatedConvergenceEncodeBHist T,
        dominatedConvergenceEncodeBHist H,
        dominatedConvergenceEncodeBHist C,
        dominatedConvergenceEncodeBHist P,
        dominatedConvergenceEncodeBHist N]

private def dominatedConvergenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dominatedConvergenceEventAtDefault index rest

def dominatedConvergenceFromEventFlow
    (ef : EventFlow) : Option DominatedConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DominatedConvergenceUp.mk
      (dominatedConvergenceDecodeBHist (dominatedConvergenceEventAtDefault 0 ef))
      (dominatedConvergenceDecodeBHist (dominatedConvergenceEventAtDefault 1 ef))
      (dominatedConvergenceDecodeBHist (dominatedConvergenceEventAtDefault 2 ef))
      (dominatedConvergenceDecodeBHist (dominatedConvergenceEventAtDefault 3 ef))
      (dominatedConvergenceDecodeBHist (dominatedConvergenceEventAtDefault 4 ef))
      (dominatedConvergenceDecodeBHist (dominatedConvergenceEventAtDefault 5 ef))
      (dominatedConvergenceDecodeBHist (dominatedConvergenceEventAtDefault 6 ef))
      (dominatedConvergenceDecodeBHist (dominatedConvergenceEventAtDefault 7 ef))
      (dominatedConvergenceDecodeBHist (dominatedConvergenceEventAtDefault 8 ef))
      (dominatedConvergenceDecodeBHist (dominatedConvergenceEventAtDefault 9 ef))
      (dominatedConvergenceDecodeBHist (dominatedConvergenceEventAtDefault 10 ef))
      (dominatedConvergenceDecodeBHist (dominatedConvergenceEventAtDefault 11 ef)))

private theorem dominatedConvergence_round_trip :
    ∀ x : DominatedConvergenceUp,
      dominatedConvergenceFromEventFlow (dominatedConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M I F G L R E T H C P N =>
      change
        some
            (DominatedConvergenceUp.mk
              (dominatedConvergenceDecodeBHist (dominatedConvergenceEncodeBHist M))
              (dominatedConvergenceDecodeBHist (dominatedConvergenceEncodeBHist I))
              (dominatedConvergenceDecodeBHist (dominatedConvergenceEncodeBHist F))
              (dominatedConvergenceDecodeBHist (dominatedConvergenceEncodeBHist G))
              (dominatedConvergenceDecodeBHist (dominatedConvergenceEncodeBHist L))
              (dominatedConvergenceDecodeBHist (dominatedConvergenceEncodeBHist R))
              (dominatedConvergenceDecodeBHist (dominatedConvergenceEncodeBHist E))
              (dominatedConvergenceDecodeBHist (dominatedConvergenceEncodeBHist T))
              (dominatedConvergenceDecodeBHist (dominatedConvergenceEncodeBHist H))
              (dominatedConvergenceDecodeBHist (dominatedConvergenceEncodeBHist C))
              (dominatedConvergenceDecodeBHist (dominatedConvergenceEncodeBHist P))
              (dominatedConvergenceDecodeBHist (dominatedConvergenceEncodeBHist N))) =
          some (DominatedConvergenceUp.mk M I F G L R E T H C P N)
      rw [dominatedConvergence_decode_encode_bhist M,
        dominatedConvergence_decode_encode_bhist I,
        dominatedConvergence_decode_encode_bhist F,
        dominatedConvergence_decode_encode_bhist G,
        dominatedConvergence_decode_encode_bhist L,
        dominatedConvergence_decode_encode_bhist R,
        dominatedConvergence_decode_encode_bhist E,
        dominatedConvergence_decode_encode_bhist T,
        dominatedConvergence_decode_encode_bhist H,
        dominatedConvergence_decode_encode_bhist C,
        dominatedConvergence_decode_encode_bhist P,
        dominatedConvergence_decode_encode_bhist N]

private theorem dominatedConvergenceToEventFlow_injective
    {x y : DominatedConvergenceUp} :
    dominatedConvergenceToEventFlow x = dominatedConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dominatedConvergenceFromEventFlow (dominatedConvergenceToEventFlow x) =
        dominatedConvergenceFromEventFlow (dominatedConvergenceToEventFlow y) :=
    congrArg dominatedConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dominatedConvergence_round_trip x).symm
      (Eq.trans hread (dominatedConvergence_round_trip y)))

def dominatedConvergenceFields : DominatedConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DominatedConvergenceUp.mk M I F G L R E T H C P N => [M, I, F, G, L, R, E, T, H, C, P, N]

private theorem dominatedConvergence_fields_faithful :
    ∀ x y : DominatedConvergenceUp,
      dominatedConvergenceFields x = dominatedConvergenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk M I F G L R E T H C P N =>
      cases y with
      | mk M' I' F' G' L' R' E' T' H' C' P' N' =>
          simp only [dominatedConvergenceFields] at h
          cases h
          rfl

instance dominatedConvergenceBHistCarrier : BHistCarrier DominatedConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dominatedConvergenceToEventFlow
  fromEventFlow := dominatedConvergenceFromEventFlow

instance dominatedConvergenceChapterTasteGate : ChapterTasteGate DominatedConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dominatedConvergenceFromEventFlow (dominatedConvergenceToEventFlow x) = some x
    exact dominatedConvergence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dominatedConvergenceToEventFlow_injective heq)

instance dominatedConvergenceFieldFaithful : FieldFaithful DominatedConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dominatedConvergenceFields
  field_faithful := dominatedConvergence_fields_faithful

instance dominatedConvergenceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DominatedConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DominatedConvergenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DominatedConvergenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DominatedConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dominatedConvergenceChapterTasteGate

theorem DominatedConvergenceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DominatedConvergenceUp) ∧
      Nonempty (FieldFaithful DominatedConvergenceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial DominatedConvergenceUp) ∧
          (∀ h : BHist,
            dominatedConvergenceDecodeBHist (dominatedConvergenceEncodeBHist h) = h) ∧
            (∀ x : DominatedConvergenceUp,
              dominatedConvergenceFromEventFlow (dominatedConvergenceToEventFlow x) =
                some x) ∧
              (∀ x y : DominatedConvergenceUp,
                dominatedConvergenceToEventFlow x = dominatedConvergenceToEventFlow y →
                  x = y) ∧
                dominatedConvergenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨dominatedConvergenceChapterTasteGate⟩,
      ⟨dominatedConvergenceFieldFaithful⟩,
      ⟨dominatedConvergenceNontrivial⟩,
      dominatedConvergence_decode_encode_bhist,
      dominatedConvergence_round_trip,
      (fun _ _ heq => dominatedConvergenceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DominatedConvergenceUp
