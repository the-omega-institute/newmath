import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactLebesgueNumberLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactLebesgueNumberLedgerUp : Type where
  | mk (K F M C R D Q U H T P N : BHist) : CompactLebesgueNumberLedgerUp
  deriving DecidableEq

def compactLebesgueNumberLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactLebesgueNumberLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactLebesgueNumberLedgerEncodeBHist h

def compactLebesgueNumberLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactLebesgueNumberLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactLebesgueNumberLedgerDecodeBHist tail)

private theorem compactLebesgueNumberLedgerDecode_encode_bhist :
    ∀ h : BHist,
      compactLebesgueNumberLedgerDecodeBHist
        (compactLebesgueNumberLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactLebesgueNumberLedgerFields :
    CompactLebesgueNumberLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactLebesgueNumberLedgerUp.mk K F M C R D Q U H T P N =>
      [K, F, M, C, R, D, Q, U, H, T, P, N]

def compactLebesgueNumberLedgerToEventFlow :
    CompactLebesgueNumberLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactLebesgueNumberLedgerFields x).map compactLebesgueNumberLedgerEncodeBHist

def compactLebesgueNumberLedgerFromEventFlow :
    EventFlow → Option CompactLebesgueNumberLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _K :: [] => none
  | _K :: _F :: [] => none
  | _K :: _F :: _M :: [] => none
  | _K :: _F :: _M :: _C :: [] => none
  | _K :: _F :: _M :: _C :: _R :: [] => none
  | _K :: _F :: _M :: _C :: _R :: _D :: [] => none
  | _K :: _F :: _M :: _C :: _R :: _D :: _Q :: [] => none
  | _K :: _F :: _M :: _C :: _R :: _D :: _Q :: _U :: [] => none
  | _K :: _F :: _M :: _C :: _R :: _D :: _Q :: _U :: _H :: [] => none
  | _K :: _F :: _M :: _C :: _R :: _D :: _Q :: _U :: _H :: _T :: [] => none
  | _K :: _F :: _M :: _C :: _R :: _D :: _Q :: _U :: _H :: _T :: _P :: [] => none
  | K :: F :: M :: C :: R :: D :: Q :: U :: H :: T :: P :: N :: [] =>
      some
        (CompactLebesgueNumberLedgerUp.mk
          (compactLebesgueNumberLedgerDecodeBHist K)
          (compactLebesgueNumberLedgerDecodeBHist F)
          (compactLebesgueNumberLedgerDecodeBHist M)
          (compactLebesgueNumberLedgerDecodeBHist C)
          (compactLebesgueNumberLedgerDecodeBHist R)
          (compactLebesgueNumberLedgerDecodeBHist D)
          (compactLebesgueNumberLedgerDecodeBHist Q)
          (compactLebesgueNumberLedgerDecodeBHist U)
          (compactLebesgueNumberLedgerDecodeBHist H)
          (compactLebesgueNumberLedgerDecodeBHist T)
          (compactLebesgueNumberLedgerDecodeBHist P)
          (compactLebesgueNumberLedgerDecodeBHist N))
  | _K :: _F :: _M :: _C :: _R :: _D :: _Q :: _U :: _H :: _T :: _P :: _N ::
      _extra :: _rest => none

private theorem compactLebesgueNumberLedger_round_trip :
    ∀ x : CompactLebesgueNumberLedgerUp,
      compactLebesgueNumberLedgerFromEventFlow
        (compactLebesgueNumberLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F M C R D Q U H T P N =>
      change
        some
            (CompactLebesgueNumberLedgerUp.mk
              (compactLebesgueNumberLedgerDecodeBHist
                (compactLebesgueNumberLedgerEncodeBHist K))
              (compactLebesgueNumberLedgerDecodeBHist
                (compactLebesgueNumberLedgerEncodeBHist F))
              (compactLebesgueNumberLedgerDecodeBHist
                (compactLebesgueNumberLedgerEncodeBHist M))
              (compactLebesgueNumberLedgerDecodeBHist
                (compactLebesgueNumberLedgerEncodeBHist C))
              (compactLebesgueNumberLedgerDecodeBHist
                (compactLebesgueNumberLedgerEncodeBHist R))
              (compactLebesgueNumberLedgerDecodeBHist
                (compactLebesgueNumberLedgerEncodeBHist D))
              (compactLebesgueNumberLedgerDecodeBHist
                (compactLebesgueNumberLedgerEncodeBHist Q))
              (compactLebesgueNumberLedgerDecodeBHist
                (compactLebesgueNumberLedgerEncodeBHist U))
              (compactLebesgueNumberLedgerDecodeBHist
                (compactLebesgueNumberLedgerEncodeBHist H))
              (compactLebesgueNumberLedgerDecodeBHist
                (compactLebesgueNumberLedgerEncodeBHist T))
              (compactLebesgueNumberLedgerDecodeBHist
                (compactLebesgueNumberLedgerEncodeBHist P))
              (compactLebesgueNumberLedgerDecodeBHist
                (compactLebesgueNumberLedgerEncodeBHist N))) =
          some (CompactLebesgueNumberLedgerUp.mk K F M C R D Q U H T P N)
      rw [compactLebesgueNumberLedgerDecode_encode_bhist K,
        compactLebesgueNumberLedgerDecode_encode_bhist F,
        compactLebesgueNumberLedgerDecode_encode_bhist M,
        compactLebesgueNumberLedgerDecode_encode_bhist C,
        compactLebesgueNumberLedgerDecode_encode_bhist R,
        compactLebesgueNumberLedgerDecode_encode_bhist D,
        compactLebesgueNumberLedgerDecode_encode_bhist Q,
        compactLebesgueNumberLedgerDecode_encode_bhist U,
        compactLebesgueNumberLedgerDecode_encode_bhist H,
        compactLebesgueNumberLedgerDecode_encode_bhist T,
        compactLebesgueNumberLedgerDecode_encode_bhist P,
        compactLebesgueNumberLedgerDecode_encode_bhist N]

private theorem compactLebesgueNumberLedgerToEventFlow_injective
    {x y : CompactLebesgueNumberLedgerUp} :
    compactLebesgueNumberLedgerToEventFlow x =
      compactLebesgueNumberLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactLebesgueNumberLedgerFromEventFlow
          (compactLebesgueNumberLedgerToEventFlow x) =
        compactLebesgueNumberLedgerFromEventFlow
          (compactLebesgueNumberLedgerToEventFlow y) :=
    congrArg compactLebesgueNumberLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactLebesgueNumberLedger_round_trip x).symm
      (Eq.trans hread (compactLebesgueNumberLedger_round_trip y)))

private theorem compactLebesgueNumberLedger_field_faithful :
    ∀ x y : CompactLebesgueNumberLedgerUp,
      compactLebesgueNumberLedgerFields x = compactLebesgueNumberLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K F M C R D Q U H T P N =>
      cases y with
      | mk K' F' M' C' R' D' Q' U' H' T' P' N' =>
          cases hfields
          rfl

instance compactLebesgueNumberLedgerBHistCarrier :
    BHistCarrier CompactLebesgueNumberLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactLebesgueNumberLedgerToEventFlow
  fromEventFlow := compactLebesgueNumberLedgerFromEventFlow

instance compactLebesgueNumberLedgerChapterTasteGate :
    ChapterTasteGate CompactLebesgueNumberLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactLebesgueNumberLedgerFromEventFlow
        (compactLebesgueNumberLedgerToEventFlow x) = some x
    exact compactLebesgueNumberLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactLebesgueNumberLedgerToEventFlow_injective heq)

instance compactLebesgueNumberLedgerFieldFaithful :
    FieldFaithful CompactLebesgueNumberLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactLebesgueNumberLedgerFields
  field_faithful := compactLebesgueNumberLedger_field_faithful

instance compactLebesgueNumberLedgerNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CompactLebesgueNumberLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactLebesgueNumberLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      CompactLebesgueNumberLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompactLebesgueNumberLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactLebesgueNumberLedgerChapterTasteGate

theorem CompactLebesgueNumberLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactLebesgueNumberLedgerDecodeBHist
        (compactLebesgueNumberLedgerEncodeBHist h) = h) ∧
      (∀ x : CompactLebesgueNumberLedgerUp,
        compactLebesgueNumberLedgerFromEventFlow
          (compactLebesgueNumberLedgerToEventFlow x) = some x) ∧
        (∀ x y : CompactLebesgueNumberLedgerUp,
          compactLebesgueNumberLedgerToEventFlow x =
            compactLebesgueNumberLedgerToEventFlow y → x = y) ∧
          compactLebesgueNumberLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨compactLebesgueNumberLedgerDecode_encode_bhist,
      compactLebesgueNumberLedger_round_trip,
      (fun _ _ heq => compactLebesgueNumberLedgerToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactLebesgueNumberLedgerUp
