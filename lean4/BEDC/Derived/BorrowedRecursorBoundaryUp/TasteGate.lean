import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BorrowedRecursorBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BorrowedRecursorBoundaryUp : Type where
  | mk :
      (recursor ancestry socket failure transport replay provenance localName : BHist) →
        BorrowedRecursorBoundaryUp
  deriving DecidableEq

def borrowedRecursorBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: borrowedRecursorBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: borrowedRecursorBoundaryEncodeBHist h

def borrowedRecursorBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (borrowedRecursorBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (borrowedRecursorBoundaryDecodeBHist tail)

private theorem borrowedRecursorBoundary_decode_encode_bhist :
    ∀ h : BHist,
      borrowedRecursorBoundaryDecodeBHist
        (borrowedRecursorBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def borrowedRecursorBoundaryFields :
    BorrowedRecursorBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BorrowedRecursorBoundaryUp.mk recursor ancestry socket failure transport replay
      provenance localName =>
      [recursor, ancestry, socket, failure, transport, replay, provenance, localName]

def borrowedRecursorBoundaryToEventFlow :
    BorrowedRecursorBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (borrowedRecursorBoundaryFields x).map borrowedRecursorBoundaryEncodeBHist

def borrowedRecursorBoundaryFromEventFlow :
    EventFlow → Option BorrowedRecursorBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _a :: [] => none
  | _a :: _b :: [] => none
  | _a :: _b :: _c :: [] => none
  | _a :: _b :: _c :: _d :: [] => none
  | _a :: _b :: _c :: _d :: _e :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: [] => none
  | recursor :: ancestry :: socket :: failure :: transport :: replay :: provenance ::
      localName :: [] =>
      some
        (BorrowedRecursorBoundaryUp.mk
          (borrowedRecursorBoundaryDecodeBHist recursor)
          (borrowedRecursorBoundaryDecodeBHist ancestry)
          (borrowedRecursorBoundaryDecodeBHist socket)
          (borrowedRecursorBoundaryDecodeBHist failure)
          (borrowedRecursorBoundaryDecodeBHist transport)
          (borrowedRecursorBoundaryDecodeBHist replay)
          (borrowedRecursorBoundaryDecodeBHist provenance)
          (borrowedRecursorBoundaryDecodeBHist localName))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _rest => none

private theorem borrowedRecursorBoundary_round_trip :
    ∀ x : BorrowedRecursorBoundaryUp,
      borrowedRecursorBoundaryFromEventFlow
        (borrowedRecursorBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk recursor ancestry socket failure transport replay provenance localName =>
      change
        some
          (BorrowedRecursorBoundaryUp.mk
            (borrowedRecursorBoundaryDecodeBHist
              (borrowedRecursorBoundaryEncodeBHist recursor))
            (borrowedRecursorBoundaryDecodeBHist
              (borrowedRecursorBoundaryEncodeBHist ancestry))
            (borrowedRecursorBoundaryDecodeBHist
              (borrowedRecursorBoundaryEncodeBHist socket))
            (borrowedRecursorBoundaryDecodeBHist
              (borrowedRecursorBoundaryEncodeBHist failure))
            (borrowedRecursorBoundaryDecodeBHist
              (borrowedRecursorBoundaryEncodeBHist transport))
            (borrowedRecursorBoundaryDecodeBHist
              (borrowedRecursorBoundaryEncodeBHist replay))
            (borrowedRecursorBoundaryDecodeBHist
              (borrowedRecursorBoundaryEncodeBHist provenance))
            (borrowedRecursorBoundaryDecodeBHist
              (borrowedRecursorBoundaryEncodeBHist localName))) =
          some
            (BorrowedRecursorBoundaryUp.mk recursor ancestry socket failure transport replay
              provenance localName)
      rw [borrowedRecursorBoundary_decode_encode_bhist recursor,
        borrowedRecursorBoundary_decode_encode_bhist ancestry,
        borrowedRecursorBoundary_decode_encode_bhist socket,
        borrowedRecursorBoundary_decode_encode_bhist failure,
        borrowedRecursorBoundary_decode_encode_bhist transport,
        borrowedRecursorBoundary_decode_encode_bhist replay,
        borrowedRecursorBoundary_decode_encode_bhist provenance,
        borrowedRecursorBoundary_decode_encode_bhist localName]

private theorem borrowedRecursorBoundaryToEventFlow_injective
    {x y : BorrowedRecursorBoundaryUp} :
    borrowedRecursorBoundaryToEventFlow x =
      borrowedRecursorBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      borrowedRecursorBoundaryFromEventFlow
          (borrowedRecursorBoundaryToEventFlow x) =
        borrowedRecursorBoundaryFromEventFlow
          (borrowedRecursorBoundaryToEventFlow y) :=
    congrArg borrowedRecursorBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (borrowedRecursorBoundary_round_trip x).symm
      (Eq.trans hread (borrowedRecursorBoundary_round_trip y)))

private theorem borrowedRecursorBoundary_fields_faithful :
    ∀ x y : BorrowedRecursorBoundaryUp,
      borrowedRecursorBoundaryFields x = borrowedRecursorBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk recursor ancestry socket failure transport replay provenance localName =>
      cases y with
      | mk recursor' ancestry' socket' failure' transport' replay' provenance'
          localName' =>
          cases hfields
          rfl

instance borrowedRecursorBoundaryBHistCarrier :
    BHistCarrier BorrowedRecursorBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := borrowedRecursorBoundaryToEventFlow
  fromEventFlow := borrowedRecursorBoundaryFromEventFlow

instance borrowedRecursorBoundaryChapterTasteGate :
    ChapterTasteGate BorrowedRecursorBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      borrowedRecursorBoundaryFromEventFlow
        (borrowedRecursorBoundaryToEventFlow x) = some x
    exact borrowedRecursorBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (borrowedRecursorBoundaryToEventFlow_injective heq)

instance borrowedRecursorBoundaryFieldFaithful :
    FieldFaithful BorrowedRecursorBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := borrowedRecursorBoundaryFields
  field_faithful := borrowedRecursorBoundary_fields_faithful

instance borrowedRecursorBoundaryNontrivial :
    Nontrivial BorrowedRecursorBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BorrowedRecursorBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BorrowedRecursorBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BorrowedRecursorBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  borrowedRecursorBoundaryChapterTasteGate

end BEDC.Derived.BorrowedRecursorBoundaryUp
