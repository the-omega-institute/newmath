import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteBranchingCauchyTreeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteBranchingCauchyTreeUp : Type where
  | mk (K B F S R D E O H C P N : BHist) : FiniteBranchingCauchyTreeUp
  deriving DecidableEq

def finiteBranchingCauchyTreeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteBranchingCauchyTreeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteBranchingCauchyTreeEncodeBHist h

def finiteBranchingCauchyTreeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteBranchingCauchyTreeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteBranchingCauchyTreeDecodeBHist tail)

private theorem finiteBranchingCauchyTree_decode_encode_bhist :
    ∀ h : BHist,
      finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteBranchingCauchyTreeToEventFlow :
    FiniteBranchingCauchyTreeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteBranchingCauchyTreeUp.mk K B F S R D E O H C P N =>
      [finiteBranchingCauchyTreeEncodeBHist K,
        finiteBranchingCauchyTreeEncodeBHist B,
        finiteBranchingCauchyTreeEncodeBHist F,
        finiteBranchingCauchyTreeEncodeBHist S,
        finiteBranchingCauchyTreeEncodeBHist R,
        finiteBranchingCauchyTreeEncodeBHist D,
        finiteBranchingCauchyTreeEncodeBHist E,
        finiteBranchingCauchyTreeEncodeBHist O,
        finiteBranchingCauchyTreeEncodeBHist H,
        finiteBranchingCauchyTreeEncodeBHist C,
        finiteBranchingCauchyTreeEncodeBHist P,
        finiteBranchingCauchyTreeEncodeBHist N]

private def finiteBranchingCauchyTreeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      finiteBranchingCauchyTreeEventAtDefault index rest

def finiteBranchingCauchyTreeFromEventFlow
    (ef : EventFlow) : Option FiniteBranchingCauchyTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteBranchingCauchyTreeUp.mk
      (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEventAtDefault 0 ef))
      (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEventAtDefault 1 ef))
      (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEventAtDefault 2 ef))
      (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEventAtDefault 3 ef))
      (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEventAtDefault 4 ef))
      (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEventAtDefault 5 ef))
      (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEventAtDefault 6 ef))
      (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEventAtDefault 7 ef))
      (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEventAtDefault 8 ef))
      (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEventAtDefault 9 ef))
      (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEventAtDefault 10 ef))
      (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEventAtDefault 11 ef)))

private theorem finiteBranchingCauchyTree_round_trip :
    ∀ x : FiniteBranchingCauchyTreeUp,
      finiteBranchingCauchyTreeFromEventFlow (finiteBranchingCauchyTreeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K B F S R D E O H C P N =>
      change
        some
            (FiniteBranchingCauchyTreeUp.mk
              (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEncodeBHist K))
              (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEncodeBHist B))
              (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEncodeBHist F))
              (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEncodeBHist S))
              (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEncodeBHist R))
              (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEncodeBHist D))
              (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEncodeBHist E))
              (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEncodeBHist O))
              (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEncodeBHist H))
              (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEncodeBHist C))
              (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEncodeBHist P))
              (finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEncodeBHist N))) =
          some (FiniteBranchingCauchyTreeUp.mk K B F S R D E O H C P N)
      rw [finiteBranchingCauchyTree_decode_encode_bhist K,
        finiteBranchingCauchyTree_decode_encode_bhist B,
        finiteBranchingCauchyTree_decode_encode_bhist F,
        finiteBranchingCauchyTree_decode_encode_bhist S,
        finiteBranchingCauchyTree_decode_encode_bhist R,
        finiteBranchingCauchyTree_decode_encode_bhist D,
        finiteBranchingCauchyTree_decode_encode_bhist E,
        finiteBranchingCauchyTree_decode_encode_bhist O,
        finiteBranchingCauchyTree_decode_encode_bhist H,
        finiteBranchingCauchyTree_decode_encode_bhist C,
        finiteBranchingCauchyTree_decode_encode_bhist P,
        finiteBranchingCauchyTree_decode_encode_bhist N]

private theorem finiteBranchingCauchyTreeToEventFlow_injective
    {x y : FiniteBranchingCauchyTreeUp} :
    finiteBranchingCauchyTreeToEventFlow x = finiteBranchingCauchyTreeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteBranchingCauchyTreeFromEventFlow (finiteBranchingCauchyTreeToEventFlow x) =
        finiteBranchingCauchyTreeFromEventFlow (finiteBranchingCauchyTreeToEventFlow y) :=
    congrArg finiteBranchingCauchyTreeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteBranchingCauchyTree_round_trip x).symm
      (Eq.trans hread (finiteBranchingCauchyTree_round_trip y)))

def finiteBranchingCauchyTreeFields :
    FiniteBranchingCauchyTreeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteBranchingCauchyTreeUp.mk K B F S R D E O H C P N =>
      [K, B, F, S, R, D, E, O, H, C, P, N]

private theorem finiteBranchingCauchyTree_fields_faithful :
    ∀ x y : FiniteBranchingCauchyTreeUp,
      finiteBranchingCauchyTreeFields x = finiteBranchingCauchyTreeFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk K B F S R D E O H C P N =>
      cases y with
      | mk K' B' F' S' R' D' E' O' H' C' P' N' =>
          simp only [finiteBranchingCauchyTreeFields] at h
          cases h
          rfl

instance finiteBranchingCauchyTreeBHistCarrier :
    BHistCarrier FiniteBranchingCauchyTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteBranchingCauchyTreeToEventFlow
  fromEventFlow := finiteBranchingCauchyTreeFromEventFlow

instance finiteBranchingCauchyTreeChapterTasteGate :
    ChapterTasteGate FiniteBranchingCauchyTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteBranchingCauchyTreeFromEventFlow (finiteBranchingCauchyTreeToEventFlow x) =
      some x
    exact finiteBranchingCauchyTree_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteBranchingCauchyTreeToEventFlow_injective heq)

instance finiteBranchingCauchyTreeFieldFaithful :
    FieldFaithful FiniteBranchingCauchyTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteBranchingCauchyTreeFields
  field_faithful := finiteBranchingCauchyTree_fields_faithful

instance finiteBranchingCauchyTreeNontrivial :
    Nontrivial FiniteBranchingCauchyTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteBranchingCauchyTreeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      FiniteBranchingCauchyTreeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteBranchingCauchyTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteBranchingCauchyTreeChapterTasteGate

theorem FiniteBranchingCauchyTreeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteBranchingCauchyTreeUp) ∧
      Nonempty (FieldFaithful FiniteBranchingCauchyTreeUp) ∧
        Nonempty (Nontrivial FiniteBranchingCauchyTreeUp) ∧
          (∀ h : BHist,
            finiteBranchingCauchyTreeDecodeBHist (finiteBranchingCauchyTreeEncodeBHist h) =
              h) ∧
            (∀ x : FiniteBranchingCauchyTreeUp,
              finiteBranchingCauchyTreeFromEventFlow (finiteBranchingCauchyTreeToEventFlow x) =
                some x) ∧
              finiteBranchingCauchyTreeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨finiteBranchingCauchyTreeChapterTasteGate⟩,
      ⟨finiteBranchingCauchyTreeFieldFaithful⟩,
      ⟨finiteBranchingCauchyTreeNontrivial⟩,
      finiteBranchingCauchyTree_decode_encode_bhist,
      finiteBranchingCauchyTree_round_trip,
      rfl⟩

end BEDC.Derived.FiniteBranchingCauchyTreeUp
