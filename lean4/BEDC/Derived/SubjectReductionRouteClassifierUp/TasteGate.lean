import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubjectReductionRouteClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubjectReductionRouteClassifierUp : Type where
  | mk (B A L P K I U H C Q N : BHist) : SubjectReductionRouteClassifierUp
  deriving DecidableEq

def subjectReductionRouteClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subjectReductionRouteClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subjectReductionRouteClassifierEncodeBHist h

def subjectReductionRouteClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subjectReductionRouteClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subjectReductionRouteClassifierDecodeBHist tail)

private theorem SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      subjectReductionRouteClassifierDecodeBHist
        (subjectReductionRouteClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def subjectReductionRouteClassifierFields :
    SubjectReductionRouteClassifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SubjectReductionRouteClassifierUp.mk B A L P K I U H C Q N =>
      [B, A, L, P, K, I, U, H, C, Q, N]

def subjectReductionRouteClassifierToEventFlow :
    SubjectReductionRouteClassifierUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (subjectReductionRouteClassifierFields x).map
    subjectReductionRouteClassifierEncodeBHist

def subjectReductionRouteClassifierEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => subjectReductionRouteClassifierEventAtDefault index rest

def subjectReductionRouteClassifierFromEventFlow
    (ef : EventFlow) : Option SubjectReductionRouteClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SubjectReductionRouteClassifierUp.mk
      (subjectReductionRouteClassifierDecodeBHist
        (subjectReductionRouteClassifierEventAtDefault 0 ef))
      (subjectReductionRouteClassifierDecodeBHist
        (subjectReductionRouteClassifierEventAtDefault 1 ef))
      (subjectReductionRouteClassifierDecodeBHist
        (subjectReductionRouteClassifierEventAtDefault 2 ef))
      (subjectReductionRouteClassifierDecodeBHist
        (subjectReductionRouteClassifierEventAtDefault 3 ef))
      (subjectReductionRouteClassifierDecodeBHist
        (subjectReductionRouteClassifierEventAtDefault 4 ef))
      (subjectReductionRouteClassifierDecodeBHist
        (subjectReductionRouteClassifierEventAtDefault 5 ef))
      (subjectReductionRouteClassifierDecodeBHist
        (subjectReductionRouteClassifierEventAtDefault 6 ef))
      (subjectReductionRouteClassifierDecodeBHist
        (subjectReductionRouteClassifierEventAtDefault 7 ef))
      (subjectReductionRouteClassifierDecodeBHist
        (subjectReductionRouteClassifierEventAtDefault 8 ef))
      (subjectReductionRouteClassifierDecodeBHist
        (subjectReductionRouteClassifierEventAtDefault 9 ef))
      (subjectReductionRouteClassifierDecodeBHist
        (subjectReductionRouteClassifierEventAtDefault 10 ef)))

private theorem SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SubjectReductionRouteClassifierUp,
      subjectReductionRouteClassifierFromEventFlow
        (subjectReductionRouteClassifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk B A L P K I U H C Q N =>
      change
        some
          (SubjectReductionRouteClassifierUp.mk
            (subjectReductionRouteClassifierDecodeBHist
              (subjectReductionRouteClassifierEncodeBHist B))
            (subjectReductionRouteClassifierDecodeBHist
              (subjectReductionRouteClassifierEncodeBHist A))
            (subjectReductionRouteClassifierDecodeBHist
              (subjectReductionRouteClassifierEncodeBHist L))
            (subjectReductionRouteClassifierDecodeBHist
              (subjectReductionRouteClassifierEncodeBHist P))
            (subjectReductionRouteClassifierDecodeBHist
              (subjectReductionRouteClassifierEncodeBHist K))
            (subjectReductionRouteClassifierDecodeBHist
              (subjectReductionRouteClassifierEncodeBHist I))
            (subjectReductionRouteClassifierDecodeBHist
              (subjectReductionRouteClassifierEncodeBHist U))
            (subjectReductionRouteClassifierDecodeBHist
              (subjectReductionRouteClassifierEncodeBHist H))
            (subjectReductionRouteClassifierDecodeBHist
              (subjectReductionRouteClassifierEncodeBHist C))
            (subjectReductionRouteClassifierDecodeBHist
              (subjectReductionRouteClassifierEncodeBHist Q))
            (subjectReductionRouteClassifierDecodeBHist
              (subjectReductionRouteClassifierEncodeBHist N))) =
          some (SubjectReductionRouteClassifierUp.mk B A L P K I U H C Q N)
      rw [SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_decode B,
        SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_decode A,
        SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_decode L,
        SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_decode P,
        SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_decode K,
        SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_decode I,
        SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_decode U,
        SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_decode H,
        SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_decode C,
        SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_decode Q,
        SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_decode N]

private theorem SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SubjectReductionRouteClassifierUp} :
    subjectReductionRouteClassifierToEventFlow x =
      subjectReductionRouteClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subjectReductionRouteClassifierFromEventFlow
          (subjectReductionRouteClassifierToEventFlow x) =
        subjectReductionRouteClassifierFromEventFlow
          (subjectReductionRouteClassifierToEventFlow y) :=
    congrArg subjectReductionRouteClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_round_trip y)))

private theorem SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_fields :
    ∀ x y : SubjectReductionRouteClassifierUp,
      subjectReductionRouteClassifierFields x = subjectReductionRouteClassifierFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 A1 L1 P1 K1 I1 U1 H1 C1 Q1 N1 =>
      cases y with
      | mk B2 A2 L2 P2 K2 I2 U2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance subjectReductionRouteClassifierBHistCarrier :
    BHistCarrier SubjectReductionRouteClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subjectReductionRouteClassifierToEventFlow
  fromEventFlow := subjectReductionRouteClassifierFromEventFlow

instance subjectReductionRouteClassifierChapterTasteGate :
    ChapterTasteGate SubjectReductionRouteClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      subjectReductionRouteClassifierFromEventFlow
        (subjectReductionRouteClassifierToEventFlow x) = some x
    exact SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance subjectReductionRouteClassifierFieldFaithful :
    FieldFaithful SubjectReductionRouteClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := subjectReductionRouteClassifierFields
  field_faithful := SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_fields

instance subjectReductionRouteClassifierNontrivial :
    Nontrivial SubjectReductionRouteClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SubjectReductionRouteClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SubjectReductionRouteClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SubjectReductionRouteClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  subjectReductionRouteClassifierChapterTasteGate

theorem SubjectReductionRouteClassifierTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SubjectReductionRouteClassifierUp) ∧
      Nonempty (FieldFaithful SubjectReductionRouteClassifierUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial SubjectReductionRouteClassifierUp) ∧
          (∀ h : BHist,
            subjectReductionRouteClassifierDecodeBHist
              (subjectReductionRouteClassifierEncodeBHist h) = h) ∧
            (∀ x : SubjectReductionRouteClassifierUp,
              subjectReductionRouteClassifierFromEventFlow
                (subjectReductionRouteClassifierToEventFlow x) = some x) ∧
              (∀ x y : SubjectReductionRouteClassifierUp,
                subjectReductionRouteClassifierToEventFlow x =
                  subjectReductionRouteClassifierToEventFlow y → x = y) ∧
                subjectReductionRouteClassifierEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨subjectReductionRouteClassifierChapterTasteGate⟩,
      ⟨subjectReductionRouteClassifierFieldFaithful⟩,
      ⟨subjectReductionRouteClassifierNontrivial⟩,
      SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_decode,
      SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        SubjectReductionRouteClassifierTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SubjectReductionRouteClassifierUp
