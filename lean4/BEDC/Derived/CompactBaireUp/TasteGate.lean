import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactBaireUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactBaireUp : Type where
  | mk : (X B D C S R T H P N : BHist) -> CompactBaireUp
  deriving DecidableEq

def compactBaireEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactBaireEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactBaireEncodeBHist h

def compactBaireDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactBaireDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactBaireDecodeBHist tail)

private theorem compactBaire_decode_encode_bhist :
    forall h : BHist, compactBaireDecodeBHist (compactBaireEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactBaireFields : CompactBaireUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactBaireUp.mk X B D C S R T H P N => [X, B, D, C, S, R, T, H, P, N]

def compactBaireToEventFlow : CompactBaireUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactBaireFields x).map compactBaireEncodeBHist

def compactBaireFromEventFlow : EventFlow -> Option CompactBaireUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: restX =>
      match restX with
      | B :: restB =>
          match restB with
          | D :: restD =>
              match restD with
              | C :: restC =>
                  match restC with
                  | S :: restS =>
                      match restS with
                      | R :: restR =>
                          match restR with
                          | T :: restT =>
                              match restT with
                              | H :: restH =>
                                  match restH with
                                  | P :: restP =>
                                      match restP with
                                      | N :: restN =>
                                          match restN with
                                          | [] =>
                                              some
                                                (CompactBaireUp.mk
                                                  (compactBaireDecodeBHist X)
                                                  (compactBaireDecodeBHist B)
                                                  (compactBaireDecodeBHist D)
                                                  (compactBaireDecodeBHist C)
                                                  (compactBaireDecodeBHist S)
                                                  (compactBaireDecodeBHist R)
                                                  (compactBaireDecodeBHist T)
                                                  (compactBaireDecodeBHist H)
                                                  (compactBaireDecodeBHist P)
                                                  (compactBaireDecodeBHist N))
                                          | _ :: _ => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem compactBaire_round_trip :
    forall x : CompactBaireUp,
      compactBaireFromEventFlow (compactBaireToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X B D C S R T H P N =>
      change
        some
          (CompactBaireUp.mk
            (compactBaireDecodeBHist (compactBaireEncodeBHist X))
            (compactBaireDecodeBHist (compactBaireEncodeBHist B))
            (compactBaireDecodeBHist (compactBaireEncodeBHist D))
            (compactBaireDecodeBHist (compactBaireEncodeBHist C))
            (compactBaireDecodeBHist (compactBaireEncodeBHist S))
            (compactBaireDecodeBHist (compactBaireEncodeBHist R))
            (compactBaireDecodeBHist (compactBaireEncodeBHist T))
            (compactBaireDecodeBHist (compactBaireEncodeBHist H))
            (compactBaireDecodeBHist (compactBaireEncodeBHist P))
            (compactBaireDecodeBHist (compactBaireEncodeBHist N))) =
          some (CompactBaireUp.mk X B D C S R T H P N)
      rw [compactBaire_decode_encode_bhist X, compactBaire_decode_encode_bhist B,
        compactBaire_decode_encode_bhist D, compactBaire_decode_encode_bhist C,
        compactBaire_decode_encode_bhist S, compactBaire_decode_encode_bhist R,
        compactBaire_decode_encode_bhist T, compactBaire_decode_encode_bhist H,
        compactBaire_decode_encode_bhist P, compactBaire_decode_encode_bhist N]

private theorem compactBaireToEventFlow_injective {x y : CompactBaireUp} :
    compactBaireToEventFlow x = compactBaireToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactBaireFromEventFlow (compactBaireToEventFlow x) =
        compactBaireFromEventFlow (compactBaireToEventFlow y) :=
    congrArg compactBaireFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactBaire_round_trip x).symm
      (Eq.trans hread (compactBaire_round_trip y)))

private theorem compactBaire_field_faithful :
    forall x y : CompactBaireUp, compactBaireFields x = compactBaireFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X B D C S R T H P N =>
      cases y with
      | mk X' B' D' C' S' R' T' H' P' N' =>
          cases hfields
          rfl

instance compactBaireBHistCarrier : BHistCarrier CompactBaireUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactBaireToEventFlow
  fromEventFlow := compactBaireFromEventFlow

instance compactBaireChapterTasteGate : ChapterTasteGate CompactBaireUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactBaireFromEventFlow (compactBaireToEventFlow x) = some x
    exact compactBaire_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactBaireToEventFlow_injective heq)

instance compactBaireFieldFaithful : FieldFaithful CompactBaireUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactBaireFields
  field_faithful := compactBaire_field_faithful

def taste_gate : ChapterTasteGate CompactBaireUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactBaireChapterTasteGate

theorem CompactBaireTasteGate_single_carrier_alignment :
    (forall h : BHist, compactBaireDecodeBHist (compactBaireEncodeBHist h) = h) ∧
      (forall x : CompactBaireUp,
        compactBaireFromEventFlow (compactBaireToEventFlow x) = some x) ∧
        (forall x y : CompactBaireUp,
          compactBaireToEventFlow x = compactBaireToEventFlow y -> x = y) ∧
          compactBaireEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨compactBaire_decode_encode_bhist, compactBaire_round_trip,
      (fun _ _ heq => compactBaireToEventFlow_injective heq), rfl⟩

end BEDC.Derived.CompactBaireUp
