import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedNormalConsistencyMainUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Closed-normal consistency main-result packet over nine displayed BEDC rows. -/
inductive ClosedNormalConsistencyMainUp : Type where
  | mk : (T L B F R H C P N : BHist) → ClosedNormalConsistencyMainUp
  deriving DecidableEq

def closedNormalConsistencyMainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedNormalConsistencyMainEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedNormalConsistencyMainEncodeBHist h

def closedNormalConsistencyMainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedNormalConsistencyMainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedNormalConsistencyMainDecodeBHist tail)

private theorem ClosedNormalConsistencyMainUp_decode_encode :
    ∀ h : BHist,
      closedNormalConsistencyMainDecodeBHist
          (closedNormalConsistencyMainEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedNormalConsistencyMainFields : ClosedNormalConsistencyMainUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedNormalConsistencyMainUp.mk T L B F R H C P N => [T, L, B, F, R, H, C, P, N]

def closedNormalConsistencyMainToEventFlow :
    ClosedNormalConsistencyMainUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (closedNormalConsistencyMainFields x).map
    closedNormalConsistencyMainEncodeBHist

private def closedNormalConsistencyMainEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedNormalConsistencyMainEventAtDefault index rest

def closedNormalConsistencyMainFromEventFlow
    (ef : EventFlow) : Option ClosedNormalConsistencyMainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedNormalConsistencyMainUp.mk
      (closedNormalConsistencyMainDecodeBHist
        (closedNormalConsistencyMainEventAtDefault 0 ef))
      (closedNormalConsistencyMainDecodeBHist
        (closedNormalConsistencyMainEventAtDefault 1 ef))
      (closedNormalConsistencyMainDecodeBHist
        (closedNormalConsistencyMainEventAtDefault 2 ef))
      (closedNormalConsistencyMainDecodeBHist
        (closedNormalConsistencyMainEventAtDefault 3 ef))
      (closedNormalConsistencyMainDecodeBHist
        (closedNormalConsistencyMainEventAtDefault 4 ef))
      (closedNormalConsistencyMainDecodeBHist
        (closedNormalConsistencyMainEventAtDefault 5 ef))
      (closedNormalConsistencyMainDecodeBHist
        (closedNormalConsistencyMainEventAtDefault 6 ef))
      (closedNormalConsistencyMainDecodeBHist
        (closedNormalConsistencyMainEventAtDefault 7 ef))
      (closedNormalConsistencyMainDecodeBHist
        (closedNormalConsistencyMainEventAtDefault 8 ef)))

private theorem ClosedNormalConsistencyMainUp_round_trip :
    ∀ x : ClosedNormalConsistencyMainUp,
      closedNormalConsistencyMainFromEventFlow
          (closedNormalConsistencyMainToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T L B F R H C P N =>
      change
        some
            (ClosedNormalConsistencyMainUp.mk
              (closedNormalConsistencyMainDecodeBHist
                (closedNormalConsistencyMainEncodeBHist T))
              (closedNormalConsistencyMainDecodeBHist
                (closedNormalConsistencyMainEncodeBHist L))
              (closedNormalConsistencyMainDecodeBHist
                (closedNormalConsistencyMainEncodeBHist B))
              (closedNormalConsistencyMainDecodeBHist
                (closedNormalConsistencyMainEncodeBHist F))
              (closedNormalConsistencyMainDecodeBHist
                (closedNormalConsistencyMainEncodeBHist R))
              (closedNormalConsistencyMainDecodeBHist
                (closedNormalConsistencyMainEncodeBHist H))
              (closedNormalConsistencyMainDecodeBHist
                (closedNormalConsistencyMainEncodeBHist C))
              (closedNormalConsistencyMainDecodeBHist
                (closedNormalConsistencyMainEncodeBHist P))
              (closedNormalConsistencyMainDecodeBHist
                (closedNormalConsistencyMainEncodeBHist N))) =
          some (ClosedNormalConsistencyMainUp.mk T L B F R H C P N)
      rw [ClosedNormalConsistencyMainUp_decode_encode T,
        ClosedNormalConsistencyMainUp_decode_encode L,
        ClosedNormalConsistencyMainUp_decode_encode B,
        ClosedNormalConsistencyMainUp_decode_encode F,
        ClosedNormalConsistencyMainUp_decode_encode R,
        ClosedNormalConsistencyMainUp_decode_encode H,
        ClosedNormalConsistencyMainUp_decode_encode C,
        ClosedNormalConsistencyMainUp_decode_encode P,
        ClosedNormalConsistencyMainUp_decode_encode N]

private theorem ClosedNormalConsistencyMainUp_toEventFlow_injective
    {x y : ClosedNormalConsistencyMainUp} :
    closedNormalConsistencyMainToEventFlow x =
        closedNormalConsistencyMainToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedNormalConsistencyMainFromEventFlow
          (closedNormalConsistencyMainToEventFlow x) =
        closedNormalConsistencyMainFromEventFlow
          (closedNormalConsistencyMainToEventFlow y) :=
    congrArg closedNormalConsistencyMainFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ClosedNormalConsistencyMainUp_round_trip x).symm
      (Eq.trans hread (ClosedNormalConsistencyMainUp_round_trip y)))

private theorem ClosedNormalConsistencyMainUp_fields_faithful :
    ∀ x y : ClosedNormalConsistencyMainUp,
      closedNormalConsistencyMainFields x = closedNormalConsistencyMainFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T L B F R H C P N =>
      cases y with
      | mk T' L' B' F' R' H' C' P' N' =>
          cases hfields
          rfl

instance closedNormalConsistencyMainBHistCarrier :
    BHistCarrier ClosedNormalConsistencyMainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedNormalConsistencyMainToEventFlow
  fromEventFlow := closedNormalConsistencyMainFromEventFlow

instance closedNormalConsistencyMainChapterTasteGate :
    ChapterTasteGate ClosedNormalConsistencyMainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedNormalConsistencyMainFromEventFlow
          (closedNormalConsistencyMainToEventFlow x) =
        some x
    exact ClosedNormalConsistencyMainUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClosedNormalConsistencyMainUp_toEventFlow_injective heq)

instance closedNormalConsistencyMainFieldFaithful :
    FieldFaithful ClosedNormalConsistencyMainUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedNormalConsistencyMainFields
  field_faithful := ClosedNormalConsistencyMainUp_fields_faithful

instance closedNormalConsistencyMainNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ClosedNormalConsistencyMainUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedNormalConsistencyMainUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedNormalConsistencyMainUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ClosedNormalConsistencyMainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedNormalConsistencyMainChapterTasteGate

end BEDC.Derived.ClosedNormalConsistencyMainUp
