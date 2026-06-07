import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntervalCoverRefinementTreeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntervalCoverRefinementTreeUp : Type where
  | mk (I D R M L E W Q A H C P N : BHist) : IntervalCoverRefinementTreeUp
  deriving DecidableEq

def intervalCoverRefinementTreeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: intervalCoverRefinementTreeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: intervalCoverRefinementTreeEncodeBHist h

def intervalCoverRefinementTreeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (intervalCoverRefinementTreeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (intervalCoverRefinementTreeDecodeBHist tail)

private theorem IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      intervalCoverRefinementTreeDecodeBHist (intervalCoverRefinementTreeEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def intervalCoverRefinementTreeFields : IntervalCoverRefinementTreeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IntervalCoverRefinementTreeUp.mk I D R M L E W Q A H C P N =>
      [I, D, R, M, L, E, W, Q, A, H, C, P, N]

def intervalCoverRefinementTreeToEventFlow :
    IntervalCoverRefinementTreeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map intervalCoverRefinementTreeEncodeBHist (intervalCoverRefinementTreeFields x)

private def intervalCoverRefinementTreeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      intervalCoverRefinementTreeEventAtDefault index rest

def intervalCoverRefinementTreeFromEventFlow
    (ef : EventFlow) : Option IntervalCoverRefinementTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (IntervalCoverRefinementTreeUp.mk
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 0 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 1 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 2 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 3 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 4 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 5 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 6 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 7 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 8 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 9 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 10 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 11 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 12 ef)))

private theorem IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : IntervalCoverRefinementTreeUp,
      intervalCoverRefinementTreeFromEventFlow
        (intervalCoverRefinementTreeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D R M L E W Q A H C P N =>
      change
        some
          (IntervalCoverRefinementTreeUp.mk
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist I))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist D))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist R))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist M))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist L))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist E))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist W))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist Q))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist A))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist H))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist C))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist P))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist N))) =
          some (IntervalCoverRefinementTreeUp.mk I D R M L E W Q A H C P N)
      rw [IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_decode I,
        IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_decode D,
        IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_decode R,
        IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_decode M,
        IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_decode L,
        IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_decode E,
        IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_decode W,
        IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_decode Q,
        IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_decode A,
        IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_decode H,
        IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_decode C,
        IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_decode P,
        IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_decode N]

private theorem intervalCoverRefinementTreeToEventFlow_injective
    {x y : IntervalCoverRefinementTreeUp} :
    intervalCoverRefinementTreeToEventFlow x =
      intervalCoverRefinementTreeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      intervalCoverRefinementTreeFromEventFlow (intervalCoverRefinementTreeToEventFlow x) =
        intervalCoverRefinementTreeFromEventFlow (intervalCoverRefinementTreeToEventFlow y) :=
    congrArg intervalCoverRefinementTreeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_round_trip y)))

private theorem intervalCoverRefinementTree_field_faithful :
    ∀ x y : IntervalCoverRefinementTreeUp,
      intervalCoverRefinementTreeFields x = intervalCoverRefinementTreeFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk I₁ D₁ R₁ M₁ L₁ E₁ W₁ Q₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ D₂ R₂ M₂ L₂ E₂ W₂ Q₂ A₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance intervalCoverRefinementTreeBHistCarrier :
    BHistCarrier IntervalCoverRefinementTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := intervalCoverRefinementTreeToEventFlow
  fromEventFlow := intervalCoverRefinementTreeFromEventFlow

instance intervalCoverRefinementTreeChapterTasteGate :
    ChapterTasteGate IntervalCoverRefinementTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      intervalCoverRefinementTreeFromEventFlow
        (intervalCoverRefinementTreeToEventFlow x) =
        some x
    exact IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (intervalCoverRefinementTreeToEventFlow_injective heq)

instance intervalCoverRefinementTreeFieldFaithful :
    FieldFaithful IntervalCoverRefinementTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := intervalCoverRefinementTreeFields
  field_faithful := intervalCoverRefinementTree_field_faithful

instance intervalCoverRefinementTreeNontrivial :
    Nontrivial IntervalCoverRefinementTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨IntervalCoverRefinementTreeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      IntervalCoverRefinementTreeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate IntervalCoverRefinementTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  intervalCoverRefinementTreeChapterTasteGate

theorem IntervalCoverRefinementTreeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      intervalCoverRefinementTreeDecodeBHist (intervalCoverRefinementTreeEncodeBHist h) = h) ∧
      (∀ x : IntervalCoverRefinementTreeUp,
        intervalCoverRefinementTreeFromEventFlow (intervalCoverRefinementTreeToEventFlow x) =
          some x) ∧
        (∀ x y : IntervalCoverRefinementTreeUp,
          intervalCoverRefinementTreeToEventFlow x = intervalCoverRefinementTreeToEventFlow y →
            x = y) ∧
          intervalCoverRefinementTreeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark Empty
  exact
    ⟨IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_decode,
      IntervalCoverRefinementTreeTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => intervalCoverRefinementTreeToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.IntervalCoverRefinementTreeUp.TasteGate
