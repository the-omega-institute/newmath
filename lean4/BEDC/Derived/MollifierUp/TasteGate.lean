import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MollifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MollifierUp : Type where
  | mk (S R N P C H L : BHist) : MollifierUp
  deriving DecidableEq

def mollifierEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mollifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mollifierEncodeBHist h

def mollifierDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mollifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mollifierDecodeBHist tail)

private theorem MollifierTasteGate_single_carrier_alignment_decode :
    forall h : BHist, mollifierDecodeBHist (mollifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def mollifierFields : MollifierUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MollifierUp.mk S R N P C H L => [S, R, N, P, C, H, L]

def mollifierToEventFlow : MollifierUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (mollifierFields x).map mollifierEncodeBHist

private def mollifierEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => mollifierEventAtDefault index rest

def mollifierFromEventFlow (ef : EventFlow) : Option MollifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MollifierUp.mk
      (mollifierDecodeBHist (mollifierEventAtDefault 0 ef))
      (mollifierDecodeBHist (mollifierEventAtDefault 1 ef))
      (mollifierDecodeBHist (mollifierEventAtDefault 2 ef))
      (mollifierDecodeBHist (mollifierEventAtDefault 3 ef))
      (mollifierDecodeBHist (mollifierEventAtDefault 4 ef))
      (mollifierDecodeBHist (mollifierEventAtDefault 5 ef))
      (mollifierDecodeBHist (mollifierEventAtDefault 6 ef)))

private theorem MollifierTasteGate_single_carrier_alignment_round_trip :
    forall x : MollifierUp, mollifierFromEventFlow (mollifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk S R N P C H L =>
      change
        some
          (MollifierUp.mk
            (mollifierDecodeBHist (mollifierEncodeBHist S))
            (mollifierDecodeBHist (mollifierEncodeBHist R))
            (mollifierDecodeBHist (mollifierEncodeBHist N))
            (mollifierDecodeBHist (mollifierEncodeBHist P))
            (mollifierDecodeBHist (mollifierEncodeBHist C))
            (mollifierDecodeBHist (mollifierEncodeBHist H))
            (mollifierDecodeBHist (mollifierEncodeBHist L))) =
          some (MollifierUp.mk S R N P C H L)
      rw [MollifierTasteGate_single_carrier_alignment_decode S,
        MollifierTasteGate_single_carrier_alignment_decode R,
        MollifierTasteGate_single_carrier_alignment_decode N,
        MollifierTasteGate_single_carrier_alignment_decode P,
        MollifierTasteGate_single_carrier_alignment_decode C,
        MollifierTasteGate_single_carrier_alignment_decode H,
        MollifierTasteGate_single_carrier_alignment_decode L]

private theorem MollifierTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MollifierUp} :
    mollifierToEventFlow x = mollifierToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mollifierFromEventFlow (mollifierToEventFlow x) =
        mollifierFromEventFlow (mollifierToEventFlow y) :=
    congrArg mollifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MollifierTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MollifierTasteGate_single_carrier_alignment_round_trip y)))

private theorem MollifierTasteGate_single_carrier_alignment_fields :
    forall x y : MollifierUp, mollifierFields x = mollifierFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 R1 N1 P1 C1 H1 L1 =>
      cases y with
      | mk S2 R2 N2 P2 C2 H2 L2 =>
          cases hfields
          rfl

instance mollifierBHistCarrier : BHistCarrier MollifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mollifierToEventFlow
  fromEventFlow := mollifierFromEventFlow

instance mollifierChapterTasteGate : ChapterTasteGate MollifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change mollifierFromEventFlow (mollifierToEventFlow x) = some x
    exact MollifierTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MollifierTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance mollifierFieldFaithful : FieldFaithful MollifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := mollifierFields
  field_faithful := MollifierTasteGate_single_carrier_alignment_fields

instance mollifierNontrivial : Nontrivial MollifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MollifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      MollifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MollifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  mollifierChapterTasteGate

theorem MollifierTasteGate_single_carrier_alignment :
    (forall h : BHist, mollifierDecodeBHist (mollifierEncodeBHist h) = h) ∧
      (forall x : MollifierUp, mollifierFromEventFlow (mollifierToEventFlow x) = some x) ∧
        (forall x y : MollifierUp, mollifierToEventFlow x = mollifierToEventFlow y -> x = y) ∧
          mollifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨MollifierTasteGate_single_carrier_alignment_decode,
      MollifierTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => MollifierTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MollifierUp
