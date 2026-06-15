import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SpreadSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SpreadSpaceUp : Type where
  | mk (B L Q W R E H C P N : BHist) : SpreadSpaceUp
  deriving DecidableEq

def spreadSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: spreadSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: spreadSpaceEncodeBHist h

def spreadSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (spreadSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (spreadSpaceDecodeBHist tail)

private theorem spreadSpaceDecode_encode_bhist :
    ∀ h : BHist, spreadSpaceDecodeBHist (spreadSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def spreadSpaceFields : SpreadSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SpreadSpaceUp.mk B L Q W R E H C P N => [B, L, Q, W, R, E, H, C, P, N]

def spreadSpaceToEventFlow : SpreadSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (spreadSpaceFields x).map spreadSpaceEncodeBHist

def spreadSpaceFromEventFlow : EventFlow → Option SpreadSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _B :: [] => none
  | _B :: _L :: [] => none
  | _B :: _L :: _Q :: [] => none
  | _B :: _L :: _Q :: _W :: [] => none
  | _B :: _L :: _Q :: _W :: _R :: [] => none
  | _B :: _L :: _Q :: _W :: _R :: _E :: [] => none
  | _B :: _L :: _Q :: _W :: _R :: _E :: _H :: [] => none
  | _B :: _L :: _Q :: _W :: _R :: _E :: _H :: _C :: [] => none
  | _B :: _L :: _Q :: _W :: _R :: _E :: _H :: _C :: _P :: [] => none
  | B :: L :: Q :: W :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (SpreadSpaceUp.mk
          (spreadSpaceDecodeBHist B)
          (spreadSpaceDecodeBHist L)
          (spreadSpaceDecodeBHist Q)
          (spreadSpaceDecodeBHist W)
          (spreadSpaceDecodeBHist R)
          (spreadSpaceDecodeBHist E)
          (spreadSpaceDecodeBHist H)
          (spreadSpaceDecodeBHist C)
          (spreadSpaceDecodeBHist P)
          (spreadSpaceDecodeBHist N))
  | _B :: _L :: _Q :: _W :: _R :: _E :: _H :: _C :: _P :: _N :: _extra :: _rest => none

private theorem spreadSpace_round_trip :
    ∀ x : SpreadSpaceUp, spreadSpaceFromEventFlow (spreadSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B L Q W R E H C P N =>
      change
        some
            (SpreadSpaceUp.mk
              (spreadSpaceDecodeBHist (spreadSpaceEncodeBHist B))
              (spreadSpaceDecodeBHist (spreadSpaceEncodeBHist L))
              (spreadSpaceDecodeBHist (spreadSpaceEncodeBHist Q))
              (spreadSpaceDecodeBHist (spreadSpaceEncodeBHist W))
              (spreadSpaceDecodeBHist (spreadSpaceEncodeBHist R))
              (spreadSpaceDecodeBHist (spreadSpaceEncodeBHist E))
              (spreadSpaceDecodeBHist (spreadSpaceEncodeBHist H))
              (spreadSpaceDecodeBHist (spreadSpaceEncodeBHist C))
              (spreadSpaceDecodeBHist (spreadSpaceEncodeBHist P))
              (spreadSpaceDecodeBHist (spreadSpaceEncodeBHist N))) =
          some (SpreadSpaceUp.mk B L Q W R E H C P N)
      rw [spreadSpaceDecode_encode_bhist B, spreadSpaceDecode_encode_bhist L,
        spreadSpaceDecode_encode_bhist Q, spreadSpaceDecode_encode_bhist W,
        spreadSpaceDecode_encode_bhist R, spreadSpaceDecode_encode_bhist E,
        spreadSpaceDecode_encode_bhist H, spreadSpaceDecode_encode_bhist C,
        spreadSpaceDecode_encode_bhist P, spreadSpaceDecode_encode_bhist N]

private theorem spreadSpaceToEventFlow_injective {x y : SpreadSpaceUp} :
    spreadSpaceToEventFlow x = spreadSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      spreadSpaceFromEventFlow (spreadSpaceToEventFlow x) =
        spreadSpaceFromEventFlow (spreadSpaceToEventFlow y) :=
    congrArg spreadSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (spreadSpace_round_trip x).symm
      (Eq.trans hread (spreadSpace_round_trip y)))

private theorem spreadSpace_fields_faithful :
    ∀ x y : SpreadSpaceUp, spreadSpaceFields x = spreadSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B L Q W R E H C P N =>
      cases y with
      | mk B' L' Q' W' R' E' H' C' P' N' =>
          cases hfields
          rfl

instance spreadSpaceBHistCarrier : BHistCarrier SpreadSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := spreadSpaceToEventFlow
  fromEventFlow := spreadSpaceFromEventFlow

instance spreadSpaceChapterTasteGate : ChapterTasteGate SpreadSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change spreadSpaceFromEventFlow (spreadSpaceToEventFlow x) = some x
    exact spreadSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (spreadSpaceToEventFlow_injective heq)

instance spreadSpaceFieldFaithful : FieldFaithful SpreadSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := spreadSpaceFields
  field_faithful := spreadSpace_fields_faithful

instance spreadSpaceNontrivial : Nontrivial SpreadSpaceUp where
  witness_pair :=
    ⟨SpreadSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SpreadSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def spreadSpaceTasteGate : ChapterTasteGate SpreadSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  spreadSpaceChapterTasteGate

theorem SpreadSpaceTasteGate_single_carrier_alignment :
    (forall h : BHist, spreadSpaceDecodeBHist (spreadSpaceEncodeBHist h) = h) ∧
      (forall x : SpreadSpaceUp,
        spreadSpaceFromEventFlow (spreadSpaceToEventFlow x) = some x) ∧
        (forall x y : SpreadSpaceUp,
          spreadSpaceToEventFlow x = spreadSpaceToEventFlow y -> x = y) ∧
          spreadSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨spreadSpaceDecode_encode_bhist,
      spreadSpace_round_trip,
      (fun _ _ heq => spreadSpaceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SpreadSpaceUp
