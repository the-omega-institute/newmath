import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TotallyBoundedLocatedSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TotallyBoundedLocatedSetUp : Type where
  | mk (X A B Q R E T H C P N : BHist) : TotallyBoundedLocatedSetUp
  deriving DecidableEq

def totallyBoundedLocatedSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: totallyBoundedLocatedSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: totallyBoundedLocatedSetEncodeBHist h

def totallyBoundedLocatedSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (totallyBoundedLocatedSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (totallyBoundedLocatedSetDecodeBHist tail)

private theorem totallyBoundedLocatedSetDecode_encode_bhist :
    ∀ h : BHist,
      totallyBoundedLocatedSetDecodeBHist
        (totallyBoundedLocatedSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def totallyBoundedLocatedSetFields :
    TotallyBoundedLocatedSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TotallyBoundedLocatedSetUp.mk X A B Q R E T H C P N =>
      [X, A, B, Q, R, E, T, H, C, P, N]

def totallyBoundedLocatedSetToEventFlow :
    TotallyBoundedLocatedSetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (totallyBoundedLocatedSetFields x).map totallyBoundedLocatedSetEncodeBHist

def totallyBoundedLocatedSetFromEventFlow :
    EventFlow → Option TotallyBoundedLocatedSetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _X :: [] => none
  | _X :: _A :: [] => none
  | _X :: _A :: _B :: [] => none
  | _X :: _A :: _B :: _Q :: [] => none
  | _X :: _A :: _B :: _Q :: _R :: [] => none
  | _X :: _A :: _B :: _Q :: _R :: _E :: [] => none
  | _X :: _A :: _B :: _Q :: _R :: _E :: _T :: [] => none
  | _X :: _A :: _B :: _Q :: _R :: _E :: _T :: _H :: [] => none
  | _X :: _A :: _B :: _Q :: _R :: _E :: _T :: _H :: _C :: [] => none
  | _X :: _A :: _B :: _Q :: _R :: _E :: _T :: _H :: _C :: _P :: [] => none
  | X :: A :: B :: Q :: R :: E :: T :: H :: C :: P :: N :: [] =>
      some
        (TotallyBoundedLocatedSetUp.mk
          (totallyBoundedLocatedSetDecodeBHist X)
          (totallyBoundedLocatedSetDecodeBHist A)
          (totallyBoundedLocatedSetDecodeBHist B)
          (totallyBoundedLocatedSetDecodeBHist Q)
          (totallyBoundedLocatedSetDecodeBHist R)
          (totallyBoundedLocatedSetDecodeBHist E)
          (totallyBoundedLocatedSetDecodeBHist T)
          (totallyBoundedLocatedSetDecodeBHist H)
          (totallyBoundedLocatedSetDecodeBHist C)
          (totallyBoundedLocatedSetDecodeBHist P)
          (totallyBoundedLocatedSetDecodeBHist N))
  | _X :: _A :: _B :: _Q :: _R :: _E :: _T :: _H :: _C :: _P :: _N ::
      _extra :: _rest => none

private theorem totallyBoundedLocatedSet_round_trip :
    ∀ x : TotallyBoundedLocatedSetUp,
      totallyBoundedLocatedSetFromEventFlow
        (totallyBoundedLocatedSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X A B Q R E T H C P N =>
      change
        some
            (TotallyBoundedLocatedSetUp.mk
              (totallyBoundedLocatedSetDecodeBHist
                (totallyBoundedLocatedSetEncodeBHist X))
              (totallyBoundedLocatedSetDecodeBHist
                (totallyBoundedLocatedSetEncodeBHist A))
              (totallyBoundedLocatedSetDecodeBHist
                (totallyBoundedLocatedSetEncodeBHist B))
              (totallyBoundedLocatedSetDecodeBHist
                (totallyBoundedLocatedSetEncodeBHist Q))
              (totallyBoundedLocatedSetDecodeBHist
                (totallyBoundedLocatedSetEncodeBHist R))
              (totallyBoundedLocatedSetDecodeBHist
                (totallyBoundedLocatedSetEncodeBHist E))
              (totallyBoundedLocatedSetDecodeBHist
                (totallyBoundedLocatedSetEncodeBHist T))
              (totallyBoundedLocatedSetDecodeBHist
                (totallyBoundedLocatedSetEncodeBHist H))
              (totallyBoundedLocatedSetDecodeBHist
                (totallyBoundedLocatedSetEncodeBHist C))
              (totallyBoundedLocatedSetDecodeBHist
                (totallyBoundedLocatedSetEncodeBHist P))
              (totallyBoundedLocatedSetDecodeBHist
                (totallyBoundedLocatedSetEncodeBHist N))) =
          some (TotallyBoundedLocatedSetUp.mk X A B Q R E T H C P N)
      rw [totallyBoundedLocatedSetDecode_encode_bhist X,
        totallyBoundedLocatedSetDecode_encode_bhist A,
        totallyBoundedLocatedSetDecode_encode_bhist B,
        totallyBoundedLocatedSetDecode_encode_bhist Q,
        totallyBoundedLocatedSetDecode_encode_bhist R,
        totallyBoundedLocatedSetDecode_encode_bhist E,
        totallyBoundedLocatedSetDecode_encode_bhist T,
        totallyBoundedLocatedSetDecode_encode_bhist H,
        totallyBoundedLocatedSetDecode_encode_bhist C,
        totallyBoundedLocatedSetDecode_encode_bhist P,
        totallyBoundedLocatedSetDecode_encode_bhist N]

private theorem totallyBoundedLocatedSetToEventFlow_injective
    {x y : TotallyBoundedLocatedSetUp} :
    totallyBoundedLocatedSetToEventFlow x =
      totallyBoundedLocatedSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      totallyBoundedLocatedSetFromEventFlow
          (totallyBoundedLocatedSetToEventFlow x) =
        totallyBoundedLocatedSetFromEventFlow
          (totallyBoundedLocatedSetToEventFlow y) :=
    congrArg totallyBoundedLocatedSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (totallyBoundedLocatedSet_round_trip x).symm
      (Eq.trans hread (totallyBoundedLocatedSet_round_trip y)))

private theorem totallyBoundedLocatedSet_field_faithful :
    ∀ x y : TotallyBoundedLocatedSetUp,
      totallyBoundedLocatedSetFields x = totallyBoundedLocatedSetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X A B Q R E T H C P N =>
      cases y with
      | mk X' A' B' Q' R' E' T' H' C' P' N' =>
          cases hfields
          rfl

instance totallyBoundedLocatedSetBHistCarrier :
    BHistCarrier TotallyBoundedLocatedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := totallyBoundedLocatedSetToEventFlow
  fromEventFlow := totallyBoundedLocatedSetFromEventFlow

instance totallyBoundedLocatedSetChapterTasteGate :
    ChapterTasteGate TotallyBoundedLocatedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      totallyBoundedLocatedSetFromEventFlow
        (totallyBoundedLocatedSetToEventFlow x) = some x
    exact totallyBoundedLocatedSet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (totallyBoundedLocatedSetToEventFlow_injective heq)

instance totallyBoundedLocatedSetFieldFaithful :
    FieldFaithful TotallyBoundedLocatedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := totallyBoundedLocatedSetFields
  field_faithful := totallyBoundedLocatedSet_field_faithful

instance totallyBoundedLocatedSetNontrivial :
    BEDC.Meta.TasteGate.Nontrivial TotallyBoundedLocatedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TotallyBoundedLocatedSetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      TotallyBoundedLocatedSetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TotallyBoundedLocatedSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  totallyBoundedLocatedSetChapterTasteGate

theorem TotallyBoundedLocatedSetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      totallyBoundedLocatedSetDecodeBHist
        (totallyBoundedLocatedSetEncodeBHist h) = h) ∧
      (∀ x : TotallyBoundedLocatedSetUp,
        totallyBoundedLocatedSetFromEventFlow
          (totallyBoundedLocatedSetToEventFlow x) = some x) ∧
        (∀ x y : TotallyBoundedLocatedSetUp,
          totallyBoundedLocatedSetToEventFlow x =
            totallyBoundedLocatedSetToEventFlow y → x = y) ∧
          totallyBoundedLocatedSetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨totallyBoundedLocatedSetDecode_encode_bhist,
      totallyBoundedLocatedSet_round_trip,
      (fun _ _ heq => totallyBoundedLocatedSetToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.TotallyBoundedLocatedSetUp
