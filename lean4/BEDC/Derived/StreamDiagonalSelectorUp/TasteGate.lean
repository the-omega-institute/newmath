import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StreamDiagonalSelectorUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StreamDiagonalSelectorUp : Type where
  | mk (S mu W R DH H C P N : BHist) : StreamDiagonalSelectorUp
  deriving DecidableEq

def streamDiagonalSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: streamDiagonalSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: streamDiagonalSelectorEncodeBHist h

def streamDiagonalSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (streamDiagonalSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (streamDiagonalSelectorDecodeBHist tail)

private theorem StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def streamDiagonalSelectorFields : StreamDiagonalSelectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StreamDiagonalSelectorUp.mk S mu W R DH H C P N => [S, mu, W, R, DH, H, C, P, N]

def streamDiagonalSelectorToEventFlow : StreamDiagonalSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (streamDiagonalSelectorFields x).map streamDiagonalSelectorEncodeBHist

def streamDiagonalSelectorFromEventFlow : EventFlow → Option StreamDiagonalSelectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | mu :: restMu =>
          match restMu with
          | W :: restW =>
              match restW with
              | R :: restR =>
                  match restR with
                  | DH :: restDH =>
                      match restDH with
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
                                            (StreamDiagonalSelectorUp.mk
                                              (streamDiagonalSelectorDecodeBHist S)
                                              (streamDiagonalSelectorDecodeBHist mu)
                                              (streamDiagonalSelectorDecodeBHist W)
                                              (streamDiagonalSelectorDecodeBHist R)
                                              (streamDiagonalSelectorDecodeBHist DH)
                                              (streamDiagonalSelectorDecodeBHist H)
                                              (streamDiagonalSelectorDecodeBHist C)
                                              (streamDiagonalSelectorDecodeBHist P)
                                              (streamDiagonalSelectorDecodeBHist N))
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

private theorem streamDiagonalSelector_mk_congr
    {S S' mu mu' W W' R R' DH DH' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hmu : mu' = mu) (hW : W' = W) (hR : R' = R)
    (hDH : DH' = DH) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    StreamDiagonalSelectorUp.mk S' mu' W' R' DH' H' C' P' N' =
      StreamDiagonalSelectorUp.mk S mu W R DH H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hmu
  cases hW
  cases hR
  cases hDH
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem StreamDiagonalSelectorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : StreamDiagonalSelectorUp,
      streamDiagonalSelectorFromEventFlow (streamDiagonalSelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S mu W R DH H C P N =>
      exact
        congrArg some
          (streamDiagonalSelector_mk_congr
            (StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode S)
            (StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode mu)
            (StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode W)
            (StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode R)
            (StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode DH)
            (StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode H)
            (StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode C)
            (StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode P)
            (StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode N))

private theorem streamDiagonalSelectorToEventFlow_injective
    {x y : StreamDiagonalSelectorUp} :
    streamDiagonalSelectorToEventFlow x = streamDiagonalSelectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      streamDiagonalSelectorFromEventFlow (streamDiagonalSelectorToEventFlow x) =
        streamDiagonalSelectorFromEventFlow (streamDiagonalSelectorToEventFlow y) :=
    congrArg streamDiagonalSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (StreamDiagonalSelectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (StreamDiagonalSelectorTasteGate_single_carrier_alignment_round_trip y)))

private theorem streamDiagonalSelector_field_faithful :
    ∀ x y : StreamDiagonalSelectorUp,
      streamDiagonalSelectorFields x = streamDiagonalSelectorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S mu W R DH H C P N =>
      cases y with
      | mk S' mu' W' R' DH' H' C' P' N' =>
          cases hfields
          rfl

instance streamDiagonalSelectorBHistCarrier : BHistCarrier StreamDiagonalSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := streamDiagonalSelectorToEventFlow
  fromEventFlow := streamDiagonalSelectorFromEventFlow

instance streamDiagonalSelectorChapterTasteGate :
    ChapterTasteGate StreamDiagonalSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change streamDiagonalSelectorFromEventFlow (streamDiagonalSelectorToEventFlow x) = some x
    exact StreamDiagonalSelectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (streamDiagonalSelectorToEventFlow_injective heq)

instance streamDiagonalSelectorFieldFaithful : FieldFaithful StreamDiagonalSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := streamDiagonalSelectorFields
  field_faithful := streamDiagonalSelector_field_faithful

instance streamDiagonalSelectorNontrivial :
    BEDC.Meta.TasteGate.Nontrivial StreamDiagonalSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StreamDiagonalSelectorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StreamDiagonalSelectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate StreamDiagonalSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  streamDiagonalSelectorChapterTasteGate

theorem StreamDiagonalSelectorTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate StreamDiagonalSelectorUp) ∧
      Nonempty (FieldFaithful StreamDiagonalSelectorUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial StreamDiagonalSelectorUp) ∧
      (∀ h : BHist,
        streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEncodeBHist h) = h) ∧
      (∀ x : StreamDiagonalSelectorUp,
        streamDiagonalSelectorFromEventFlow (streamDiagonalSelectorToEventFlow x) = some x) ∧
      (∀ x y : StreamDiagonalSelectorUp,
        streamDiagonalSelectorToEventFlow x = streamDiagonalSelectorToEventFlow y → x = y) ∧
      streamDiagonalSelectorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨streamDiagonalSelectorChapterTasteGate⟩
  constructor
  · exact ⟨streamDiagonalSelectorFieldFaithful⟩
  constructor
  · exact ⟨streamDiagonalSelectorNontrivial⟩
  constructor
  · exact StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode
  constructor
  · exact StreamDiagonalSelectorTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact streamDiagonalSelectorToEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.StreamDiagonalSelectorUp
