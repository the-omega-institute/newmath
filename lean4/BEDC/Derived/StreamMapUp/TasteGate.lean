import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StreamMapUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StreamMapUp : Type where
  | mk (S T F W Q D R H C P N : BHist) : StreamMapUp
  deriving DecidableEq

def streamMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: streamMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: streamMapEncodeBHist h

def streamMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (streamMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (streamMapDecodeBHist tail)

private theorem StreamMapTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, streamMapDecodeBHist (streamMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def streamMapFields : StreamMapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StreamMapUp.mk S T F W Q D R H C P N => [S, T, F, W, Q, D, R, H, C, P, N]

def streamMapToEventFlow : StreamMapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (streamMapFields x).map streamMapEncodeBHist

def streamMapFromEventFlow : EventFlow → Option StreamMapUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | T :: restT =>
          match restT with
          | F :: restF =>
              match restF with
              | W :: restW =>
                  match restW with
                  | Q :: restQ =>
                      match restQ with
                      | D :: restD =>
                          match restD with
                          | R :: restR =>
                              match restR with
                              | H :: restH =>
                                  match restH with
                                  | C :: restC =>
                                      match restC with
                                      | P :: restP =>
                                          match restP with
                                          | N :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (StreamMapUp.mk
                                                      (streamMapDecodeBHist S)
                                                      (streamMapDecodeBHist T)
                                                      (streamMapDecodeBHist F)
                                                      (streamMapDecodeBHist W)
                                                      (streamMapDecodeBHist Q)
                                                      (streamMapDecodeBHist D)
                                                      (streamMapDecodeBHist R)
                                                      (streamMapDecodeBHist H)
                                                      (streamMapDecodeBHist C)
                                                      (streamMapDecodeBHist P)
                                                      (streamMapDecodeBHist N))
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

private theorem streamMap_mk_congr
    {S S' T T' F F' W W' Q Q' D D' R R' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hT : T' = T) (hF : F' = F) (hW : W' = W)
    (hQ : Q' = Q) (hD : D' = D) (hR : R' = R) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    StreamMapUp.mk S' T' F' W' Q' D' R' H' C' P' N' =
      StreamMapUp.mk S T F W Q D R H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hT
  cases hF
  cases hW
  cases hQ
  cases hD
  cases hR
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem StreamMapTasteGate_single_carrier_alignment_round_trip :
    ∀ x : StreamMapUp, streamMapFromEventFlow (streamMapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T F W Q D R H C P N =>
      exact
        congrArg some
          (streamMap_mk_congr
            (StreamMapTasteGate_single_carrier_alignment_decode S)
            (StreamMapTasteGate_single_carrier_alignment_decode T)
            (StreamMapTasteGate_single_carrier_alignment_decode F)
            (StreamMapTasteGate_single_carrier_alignment_decode W)
            (StreamMapTasteGate_single_carrier_alignment_decode Q)
            (StreamMapTasteGate_single_carrier_alignment_decode D)
            (StreamMapTasteGate_single_carrier_alignment_decode R)
            (StreamMapTasteGate_single_carrier_alignment_decode H)
            (StreamMapTasteGate_single_carrier_alignment_decode C)
            (StreamMapTasteGate_single_carrier_alignment_decode P)
            (StreamMapTasteGate_single_carrier_alignment_decode N))

private theorem streamMapToEventFlow_injective {x y : StreamMapUp} :
    streamMapToEventFlow x = streamMapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      streamMapFromEventFlow (streamMapToEventFlow x) =
        streamMapFromEventFlow (streamMapToEventFlow y) :=
    congrArg streamMapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (StreamMapTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (StreamMapTasteGate_single_carrier_alignment_round_trip y)))

private theorem streamMap_field_faithful :
    ∀ x y : StreamMapUp, streamMapFields x = streamMapFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x
  cases y
  cases hfields
  rfl

instance streamMapBHistCarrier : BHistCarrier StreamMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := streamMapToEventFlow
  fromEventFlow := streamMapFromEventFlow

instance streamMapChapterTasteGate : ChapterTasteGate StreamMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change streamMapFromEventFlow (streamMapToEventFlow x) = some x
    exact StreamMapTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (streamMapToEventFlow_injective heq)

instance streamMapFieldFaithful : FieldFaithful StreamMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := streamMapFields
  field_faithful := streamMap_field_faithful

instance streamMapNontrivial : BEDC.Meta.TasteGate.Nontrivial StreamMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StreamMapUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StreamMapUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate StreamMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  streamMapChapterTasteGate

theorem StreamMapTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate StreamMapUp) ∧
      Nonempty (FieldFaithful StreamMapUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial StreamMapUp) ∧
      (∀ h : BHist, streamMapDecodeBHist (streamMapEncodeBHist h) = h) ∧
      (∀ x : StreamMapUp, streamMapFromEventFlow (streamMapToEventFlow x) = some x) ∧
      (∀ x y : StreamMapUp, streamMapToEventFlow x = streamMapToEventFlow y -> x = y) ∧
      streamMapEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨streamMapChapterTasteGate⟩
  constructor
  · exact ⟨streamMapFieldFaithful⟩
  constructor
  · exact ⟨streamMapNontrivial⟩
  constructor
  · exact StreamMapTasteGate_single_carrier_alignment_decode
  constructor
  · exact StreamMapTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact streamMapToEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.StreamMapUp
