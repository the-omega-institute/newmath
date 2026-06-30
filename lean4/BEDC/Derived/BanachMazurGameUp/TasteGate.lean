import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BanachMazurGameUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BanachMazurGameUp : Type where
  | mk (P B K M L S R E H C Q N : BHist) : BanachMazurGameUp
  deriving DecidableEq

def banachMazurGameEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: banachMazurGameEncodeBHist h
  | BHist.e1 h => BMark.b1 :: banachMazurGameEncodeBHist h

def banachMazurGameDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (banachMazurGameDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (banachMazurGameDecodeBHist tail)

private theorem BanachMazurGameTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, banachMazurGameDecodeBHist (banachMazurGameEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def banachMazurGameFields : BanachMazurGameUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BanachMazurGameUp.mk P B K M L S R E H C Q N => [P, B, K, M, L, S, R, E, H, C, Q, N]

def banachMazurGameToEventFlow : BanachMazurGameUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (banachMazurGameFields x).map banachMazurGameEncodeBHist

def banachMazurGameFromEventFlow : EventFlow → Option BanachMazurGameUp
  -- BEDC touchpoint anchor: BHist BMark
  | P :: restP =>
      match restP with
      | B :: restB =>
          match restB with
          | K :: restK =>
              match restK with
              | M :: restM =>
                  match restM with
                  | L :: restL =>
                      match restL with
                      | S :: restS =>
                          match restS with
                          | R :: restR =>
                              match restR with
                              | E :: restE =>
                                  match restE with
                                  | H :: restH =>
                                      match restH with
                                      | C :: restC =>
                                          match restC with
                                          | Q :: restQ =>
                                              match restQ with
                                              | N :: restN =>
                                                  match restN with
                                                  | [] =>
                                                      some
                                                        (BanachMazurGameUp.mk
                                                          (banachMazurGameDecodeBHist P)
                                                          (banachMazurGameDecodeBHist B)
                                                          (banachMazurGameDecodeBHist K)
                                                          (banachMazurGameDecodeBHist M)
                                                          (banachMazurGameDecodeBHist L)
                                                          (banachMazurGameDecodeBHist S)
                                                          (banachMazurGameDecodeBHist R)
                                                          (banachMazurGameDecodeBHist E)
                                                          (banachMazurGameDecodeBHist H)
                                                          (banachMazurGameDecodeBHist C)
                                                          (banachMazurGameDecodeBHist Q)
                                                          (banachMazurGameDecodeBHist N))
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
      | [] => none
  | [] => none

private theorem BanachMazurGameTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BanachMazurGameUp,
      banachMazurGameFromEventFlow (banachMazurGameToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P B K M L S R E H C Q N =>
      change
        some
            (BanachMazurGameUp.mk
              (banachMazurGameDecodeBHist (banachMazurGameEncodeBHist P))
              (banachMazurGameDecodeBHist (banachMazurGameEncodeBHist B))
              (banachMazurGameDecodeBHist (banachMazurGameEncodeBHist K))
              (banachMazurGameDecodeBHist (banachMazurGameEncodeBHist M))
              (banachMazurGameDecodeBHist (banachMazurGameEncodeBHist L))
              (banachMazurGameDecodeBHist (banachMazurGameEncodeBHist S))
              (banachMazurGameDecodeBHist (banachMazurGameEncodeBHist R))
              (banachMazurGameDecodeBHist (banachMazurGameEncodeBHist E))
              (banachMazurGameDecodeBHist (banachMazurGameEncodeBHist H))
              (banachMazurGameDecodeBHist (banachMazurGameEncodeBHist C))
              (banachMazurGameDecodeBHist (banachMazurGameEncodeBHist Q))
              (banachMazurGameDecodeBHist (banachMazurGameEncodeBHist N))) =
          some (BanachMazurGameUp.mk P B K M L S R E H C Q N)
      rw [BanachMazurGameTasteGate_single_carrier_alignment_decode P,
        BanachMazurGameTasteGate_single_carrier_alignment_decode B,
        BanachMazurGameTasteGate_single_carrier_alignment_decode K,
        BanachMazurGameTasteGate_single_carrier_alignment_decode M,
        BanachMazurGameTasteGate_single_carrier_alignment_decode L,
        BanachMazurGameTasteGate_single_carrier_alignment_decode S,
        BanachMazurGameTasteGate_single_carrier_alignment_decode R,
        BanachMazurGameTasteGate_single_carrier_alignment_decode E,
        BanachMazurGameTasteGate_single_carrier_alignment_decode H,
        BanachMazurGameTasteGate_single_carrier_alignment_decode C,
        BanachMazurGameTasteGate_single_carrier_alignment_decode Q,
        BanachMazurGameTasteGate_single_carrier_alignment_decode N]

private theorem banachMazurGameToEventFlow_injective {x y : BanachMazurGameUp} :
    banachMazurGameToEventFlow x = banachMazurGameToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      banachMazurGameFromEventFlow (banachMazurGameToEventFlow x) =
        banachMazurGameFromEventFlow (banachMazurGameToEventFlow y) :=
    congrArg banachMazurGameFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BanachMazurGameTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BanachMazurGameTasteGate_single_carrier_alignment_round_trip y)))

private theorem banachMazurGame_field_faithful :
    ∀ x y : BanachMazurGameUp, banachMazurGameFields x = banachMazurGameFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P B K M L S R E H C Q N =>
      cases y with
      | mk P' B' K' M' L' S' R' E' H' C' Q' N' =>
          cases hfields
          rfl

instance banachMazurGameBHistCarrier : BHistCarrier BanachMazurGameUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := banachMazurGameToEventFlow
  fromEventFlow := banachMazurGameFromEventFlow

instance banachMazurGameChapterTasteGate : ChapterTasteGate BanachMazurGameUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change banachMazurGameFromEventFlow (banachMazurGameToEventFlow x) = some x
    exact BanachMazurGameTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (banachMazurGameToEventFlow_injective heq)

instance banachMazurGameFieldFaithful : FieldFaithful BanachMazurGameUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := banachMazurGameFields
  field_faithful := banachMazurGame_field_faithful

instance banachMazurGameNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BanachMazurGameUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BanachMazurGameUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      BanachMazurGameUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BanachMazurGameUp :=
  -- BEDC touchpoint anchor: BHist BMark
  banachMazurGameChapterTasteGate

theorem BanachMazurGameTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BanachMazurGameUp) ∧
      Nonempty (FieldFaithful BanachMazurGameUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial BanachMazurGameUp) ∧
      (∀ h : BHist, banachMazurGameDecodeBHist (banachMazurGameEncodeBHist h) = h) ∧
      (∀ x : BanachMazurGameUp,
        banachMazurGameFromEventFlow (banachMazurGameToEventFlow x) = some x) ∧
      banachMazurGameEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨banachMazurGameChapterTasteGate⟩
  constructor
  · exact ⟨banachMazurGameFieldFaithful⟩
  constructor
  · exact ⟨banachMazurGameNontrivial⟩
  constructor
  · exact BanachMazurGameTasteGate_single_carrier_alignment_decode
  constructor
  · exact BanachMazurGameTasteGate_single_carrier_alignment_round_trip
  · rfl

end TasteGate
end BEDC.Derived.BanachMazurGameUp
