import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopSpaceUp : Type where
  | mk (X M L W R E H C P N : BHist) : BishopSpaceUp
  deriving DecidableEq

def bishopSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopSpaceEncodeBHist h

def bishopSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopSpaceDecodeBHist tail)

private theorem bishopSpaceDecodeEncode :
    ∀ h : BHist, bishopSpaceDecodeBHist (bishopSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopSpaceFields : BishopSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopSpaceUp.mk X M L W R E H C P N => [X, M, L, W, R, E, H, C, P, N]

def bishopSpaceToEventFlow : BishopSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopSpaceFields x).map bishopSpaceEncodeBHist

def bishopSpaceFromEventFlow : EventFlow → Option BishopSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | L :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (BishopSpaceUp.mk
                                                  (bishopSpaceDecodeBHist X)
                                                  (bishopSpaceDecodeBHist M)
                                                  (bishopSpaceDecodeBHist L)
                                                  (bishopSpaceDecodeBHist W)
                                                  (bishopSpaceDecodeBHist R)
                                                  (bishopSpaceDecodeBHist E)
                                                  (bishopSpaceDecodeBHist H)
                                                  (bishopSpaceDecodeBHist C)
                                                  (bishopSpaceDecodeBHist P)
                                                  (bishopSpaceDecodeBHist N))
                                          | _ :: _ => none

private theorem bishopSpace_round_trip :
    ∀ x : BishopSpaceUp, bishopSpaceFromEventFlow (bishopSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X M L W R E H C P N =>
      change
        some
          (BishopSpaceUp.mk
            (bishopSpaceDecodeBHist (bishopSpaceEncodeBHist X))
            (bishopSpaceDecodeBHist (bishopSpaceEncodeBHist M))
            (bishopSpaceDecodeBHist (bishopSpaceEncodeBHist L))
            (bishopSpaceDecodeBHist (bishopSpaceEncodeBHist W))
            (bishopSpaceDecodeBHist (bishopSpaceEncodeBHist R))
            (bishopSpaceDecodeBHist (bishopSpaceEncodeBHist E))
            (bishopSpaceDecodeBHist (bishopSpaceEncodeBHist H))
            (bishopSpaceDecodeBHist (bishopSpaceEncodeBHist C))
            (bishopSpaceDecodeBHist (bishopSpaceEncodeBHist P))
            (bishopSpaceDecodeBHist (bishopSpaceEncodeBHist N))) =
          some (BishopSpaceUp.mk X M L W R E H C P N)
      rw [bishopSpaceDecodeEncode X, bishopSpaceDecodeEncode M, bishopSpaceDecodeEncode L,
        bishopSpaceDecodeEncode W, bishopSpaceDecodeEncode R, bishopSpaceDecodeEncode E,
        bishopSpaceDecodeEncode H, bishopSpaceDecodeEncode C, bishopSpaceDecodeEncode P,
        bishopSpaceDecodeEncode N]

private theorem bishopSpaceToEventFlow_injective {x y : BishopSpaceUp} :
    bishopSpaceToEventFlow x = bishopSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopSpaceFromEventFlow (bishopSpaceToEventFlow x) =
        bishopSpaceFromEventFlow (bishopSpaceToEventFlow y) :=
    congrArg bishopSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopSpace_round_trip x).symm
      (Eq.trans hread (bishopSpace_round_trip y)))

private theorem bishopSpace_fields_faithful :
    ∀ x y : BishopSpaceUp, bishopSpaceFields x = bishopSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ M₁ L₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ M₂ L₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance bishopSpaceBHistCarrier : BHistCarrier BishopSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopSpaceToEventFlow
  fromEventFlow := bishopSpaceFromEventFlow

instance bishopSpaceChapterTasteGate : ChapterTasteGate BishopSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopSpaceFromEventFlow (bishopSpaceToEventFlow x) = some x
    exact bishopSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopSpaceToEventFlow_injective heq)

instance bishopSpaceFieldFaithful : FieldFaithful BishopSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopSpaceFields
  field_faithful := bishopSpace_fields_faithful

instance bishopSpaceNontrivial : Nontrivial BishopSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BishopSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopSpaceDecodeBHist (bishopSpaceEncodeBHist h) = h) ∧
      (∀ x : BishopSpaceUp, bishopSpaceFromEventFlow (bishopSpaceToEventFlow x) = some x) ∧
      (∀ x y : BishopSpaceUp, bishopSpaceToEventFlow x = bishopSpaceToEventFlow y → x = y) ∧
      bishopSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨bishopSpaceDecodeEncode,
      bishopSpace_round_trip,
      fun _ _ heq => bishopSpaceToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.BishopSpaceUp
