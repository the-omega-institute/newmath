import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactLebesgueNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactLebesgueNumberUp : Type where
  | mk (K B C R F U H Q P N : BHist) : CompactLebesgueNumberUp
  deriving DecidableEq

def compactLebesgueNumberEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactLebesgueNumberEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactLebesgueNumberEncodeBHist h

def compactLebesgueNumberDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactLebesgueNumberDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactLebesgueNumberDecodeBHist tail)

private theorem compactLebesgueNumberDecode_encode_bhist :
    forall h : BHist,
      compactLebesgueNumberDecodeBHist (compactLebesgueNumberEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactLebesgueNumberFields : CompactLebesgueNumberUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactLebesgueNumberUp.mk K B C R F U H Q P N =>
      [K, B, C, R, F, U, H, Q, P, N]

def compactLebesgueNumberToEventFlow : CompactLebesgueNumberUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactLebesgueNumberFields x).map compactLebesgueNumberEncodeBHist

def compactLebesgueNumberFromEventFlow : EventFlow -> Option CompactLebesgueNumberUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _K :: [] => none
  | _K :: _B :: [] => none
  | _K :: _B :: _C :: [] => none
  | _K :: _B :: _C :: _R :: [] => none
  | _K :: _B :: _C :: _R :: _F :: [] => none
  | _K :: _B :: _C :: _R :: _F :: _U :: [] => none
  | _K :: _B :: _C :: _R :: _F :: _U :: _H :: [] => none
  | _K :: _B :: _C :: _R :: _F :: _U :: _H :: _Q :: [] => none
  | _K :: _B :: _C :: _R :: _F :: _U :: _H :: _Q :: _P :: [] => none
  | K :: B :: C :: R :: F :: U :: H :: Q :: P :: N :: [] =>
      some
        (CompactLebesgueNumberUp.mk
          (compactLebesgueNumberDecodeBHist K)
          (compactLebesgueNumberDecodeBHist B)
          (compactLebesgueNumberDecodeBHist C)
          (compactLebesgueNumberDecodeBHist R)
          (compactLebesgueNumberDecodeBHist F)
          (compactLebesgueNumberDecodeBHist U)
          (compactLebesgueNumberDecodeBHist H)
          (compactLebesgueNumberDecodeBHist Q)
          (compactLebesgueNumberDecodeBHist P)
          (compactLebesgueNumberDecodeBHist N))
  | _K :: _B :: _C :: _R :: _F :: _U :: _H :: _Q :: _P :: _N :: _extra ::
      _rest => none

private theorem compactLebesgueNumber_round_trip :
    forall x : CompactLebesgueNumberUp,
      compactLebesgueNumberFromEventFlow
        (compactLebesgueNumberToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K B C R F U H Q P N =>
      change
        some
            (CompactLebesgueNumberUp.mk
              (compactLebesgueNumberDecodeBHist
                (compactLebesgueNumberEncodeBHist K))
              (compactLebesgueNumberDecodeBHist
                (compactLebesgueNumberEncodeBHist B))
              (compactLebesgueNumberDecodeBHist
                (compactLebesgueNumberEncodeBHist C))
              (compactLebesgueNumberDecodeBHist
                (compactLebesgueNumberEncodeBHist R))
              (compactLebesgueNumberDecodeBHist
                (compactLebesgueNumberEncodeBHist F))
              (compactLebesgueNumberDecodeBHist
                (compactLebesgueNumberEncodeBHist U))
              (compactLebesgueNumberDecodeBHist
                (compactLebesgueNumberEncodeBHist H))
              (compactLebesgueNumberDecodeBHist
                (compactLebesgueNumberEncodeBHist Q))
              (compactLebesgueNumberDecodeBHist
                (compactLebesgueNumberEncodeBHist P))
              (compactLebesgueNumberDecodeBHist
                (compactLebesgueNumberEncodeBHist N))) =
          some (CompactLebesgueNumberUp.mk K B C R F U H Q P N)
      rw [compactLebesgueNumberDecode_encode_bhist K,
        compactLebesgueNumberDecode_encode_bhist B,
        compactLebesgueNumberDecode_encode_bhist C,
        compactLebesgueNumberDecode_encode_bhist R,
        compactLebesgueNumberDecode_encode_bhist F,
        compactLebesgueNumberDecode_encode_bhist U,
        compactLebesgueNumberDecode_encode_bhist H,
        compactLebesgueNumberDecode_encode_bhist Q,
        compactLebesgueNumberDecode_encode_bhist P,
        compactLebesgueNumberDecode_encode_bhist N]

private theorem compactLebesgueNumberToEventFlow_injective
    {x y : CompactLebesgueNumberUp} :
    compactLebesgueNumberToEventFlow x = compactLebesgueNumberToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactLebesgueNumberFromEventFlow (compactLebesgueNumberToEventFlow x) =
        compactLebesgueNumberFromEventFlow (compactLebesgueNumberToEventFlow y) :=
    congrArg compactLebesgueNumberFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactLebesgueNumber_round_trip x).symm
      (Eq.trans hread (compactLebesgueNumber_round_trip y)))

instance compactLebesgueNumberBHistCarrier : BHistCarrier CompactLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactLebesgueNumberToEventFlow
  fromEventFlow := compactLebesgueNumberFromEventFlow

instance compactLebesgueNumberChapterTasteGate :
    ChapterTasteGate CompactLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactLebesgueNumberFromEventFlow
        (compactLebesgueNumberToEventFlow x) = some x
    exact compactLebesgueNumber_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactLebesgueNumberToEventFlow_injective heq)

instance compactLebesgueNumberNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CompactLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactLebesgueNumberUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactLebesgueNumberUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompactLebesgueNumberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactLebesgueNumberChapterTasteGate

theorem CompactLebesgueNumberTasteGate_single_carrier_alignment :
    (forall h : BHist,
      compactLebesgueNumberDecodeBHist (compactLebesgueNumberEncodeBHist h) = h) ∧
      (forall x : CompactLebesgueNumberUp,
        compactLebesgueNumberFromEventFlow
          (compactLebesgueNumberToEventFlow x) = some x) ∧
        (forall x y : CompactLebesgueNumberUp,
          compactLebesgueNumberToEventFlow x =
            compactLebesgueNumberToEventFlow y -> x = y) ∧
          compactLebesgueNumberEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨compactLebesgueNumberDecode_encode_bhist,
      compactLebesgueNumber_round_trip,
      (fun _ _ heq => compactLebesgueNumberToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactLebesgueNumberUp
