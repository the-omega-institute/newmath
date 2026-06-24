import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedInverseTheoremUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedInverseTheoremUp : Type where
  | mk (X Y T J O B G H C P N : BHist) : BoundedInverseTheoremUp
  deriving DecidableEq

def boundedInverseTheoremEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedInverseTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedInverseTheoremEncodeBHist h

def boundedInverseTheoremDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedInverseTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedInverseTheoremDecodeBHist tail)

private theorem BoundedInverseTheoremTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      boundedInverseTheoremDecodeBHist (boundedInverseTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedInverseTheoremToEventFlow : BoundedInverseTheoremUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedInverseTheoremUp.mk X Y T J O B G H C P N =>
      [[BMark.b0],
        boundedInverseTheoremEncodeBHist X,
        [BMark.b1, BMark.b0],
        boundedInverseTheoremEncodeBHist Y,
        [BMark.b1, BMark.b1, BMark.b0],
        boundedInverseTheoremEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedInverseTheoremEncodeBHist J,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedInverseTheoremEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedInverseTheoremEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedInverseTheoremEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        boundedInverseTheoremEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        boundedInverseTheoremEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        boundedInverseTheoremEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedInverseTheoremEncodeBHist N]

def boundedInverseTheoremFromEventFlow : EventFlow -> Option BoundedInverseTheoremUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagX :: restX =>
      match restX with
      | [] => none
      | X :: restYTag =>
          match restYTag with
          | [] => none
          | _tagY :: restY =>
              match restY with
              | [] => none
              | Y :: restTTag =>
                  match restTTag with
                  | [] => none
                  | _tagT :: restT =>
                      match restT with
                      | [] => none
                      | T :: restJTag =>
                          match restJTag with
                          | [] => none
                          | _tagJ :: restJ =>
                              match restJ with
                              | [] => none
                              | J :: restOTag =>
                                  match restOTag with
                                  | [] => none
                                  | _tagO :: restO =>
                                      match restO with
                                      | [] => none
                                      | O :: restBTag =>
                                          match restBTag with
                                          | [] => none
                                          | _tagB :: restB =>
                                              match restB with
                                              | [] => none
                                              | B :: restGTag =>
                                                  match restGTag with
                                                  | [] => none
                                                  | _tagG :: restG =>
                                                      match restG with
                                                      | [] => none
                                                      | G :: restHTag =>
                                                          match restHTag with
                                                          | [] => none
                                                          | _tagH :: restH =>
                                                              match restH with
                                                              | [] => none
                                                              | H :: restCTag =>
                                                                  match restCTag with
                                                                  | [] => none
                                                                  | _tagC :: restC =>
                                                                      match restC with
                                                                      | [] => none
                                                                      | C :: restPTag =>
                                                                          match restPTag with
                                                                          | [] => none
                                                                          | _tagP :: restP =>
                                                                              match restP with
                                                                              | [] => none
                                                                              | P :: restNTag =>
                                                                                  match restNTag with
                                                                                  | [] => none
                                                                                  | _tagN :: restN =>
                                                                                      match restN with
                                                                                      | [] => none
                                                                                      | N :: rest =>
                                                                                          match rest with
                                                                                          | [] =>
                                                                                              some
                                                                                                (BoundedInverseTheoremUp.mk
                                                                                                  (boundedInverseTheoremDecodeBHist X)
                                                                                                  (boundedInverseTheoremDecodeBHist Y)
                                                                                                  (boundedInverseTheoremDecodeBHist T)
                                                                                                  (boundedInverseTheoremDecodeBHist J)
                                                                                                  (boundedInverseTheoremDecodeBHist O)
                                                                                                  (boundedInverseTheoremDecodeBHist B)
                                                                                                  (boundedInverseTheoremDecodeBHist G)
                                                                                                  (boundedInverseTheoremDecodeBHist H)
                                                                                                  (boundedInverseTheoremDecodeBHist C)
                                                                                                  (boundedInverseTheoremDecodeBHist P)
                                                                                                  (boundedInverseTheoremDecodeBHist N))
                                                                                          | _ :: _ => none

private theorem BoundedInverseTheoremTasteGate_single_carrier_alignment_round_trip :
    forall x : BoundedInverseTheoremUp,
      boundedInverseTheoremFromEventFlow (boundedInverseTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y T J O B G H C P N =>
      change
        some
          (BoundedInverseTheoremUp.mk
            (boundedInverseTheoremDecodeBHist (boundedInverseTheoremEncodeBHist X))
            (boundedInverseTheoremDecodeBHist (boundedInverseTheoremEncodeBHist Y))
            (boundedInverseTheoremDecodeBHist (boundedInverseTheoremEncodeBHist T))
            (boundedInverseTheoremDecodeBHist (boundedInverseTheoremEncodeBHist J))
            (boundedInverseTheoremDecodeBHist (boundedInverseTheoremEncodeBHist O))
            (boundedInverseTheoremDecodeBHist (boundedInverseTheoremEncodeBHist B))
            (boundedInverseTheoremDecodeBHist (boundedInverseTheoremEncodeBHist G))
            (boundedInverseTheoremDecodeBHist (boundedInverseTheoremEncodeBHist H))
            (boundedInverseTheoremDecodeBHist (boundedInverseTheoremEncodeBHist C))
            (boundedInverseTheoremDecodeBHist (boundedInverseTheoremEncodeBHist P))
            (boundedInverseTheoremDecodeBHist (boundedInverseTheoremEncodeBHist N))) =
          some (BoundedInverseTheoremUp.mk X Y T J O B G H C P N)
      rw [BoundedInverseTheoremTasteGate_single_carrier_alignment_decode X,
        BoundedInverseTheoremTasteGate_single_carrier_alignment_decode Y,
        BoundedInverseTheoremTasteGate_single_carrier_alignment_decode T,
        BoundedInverseTheoremTasteGate_single_carrier_alignment_decode J,
        BoundedInverseTheoremTasteGate_single_carrier_alignment_decode O,
        BoundedInverseTheoremTasteGate_single_carrier_alignment_decode B,
        BoundedInverseTheoremTasteGate_single_carrier_alignment_decode G,
        BoundedInverseTheoremTasteGate_single_carrier_alignment_decode H,
        BoundedInverseTheoremTasteGate_single_carrier_alignment_decode C,
        BoundedInverseTheoremTasteGate_single_carrier_alignment_decode P,
        BoundedInverseTheoremTasteGate_single_carrier_alignment_decode N]

private theorem BoundedInverseTheoremTasteGate_single_carrier_alignment_injective
    {x y : BoundedInverseTheoremUp} :
    boundedInverseTheoremToEventFlow x = boundedInverseTheoremToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedInverseTheoremFromEventFlow (boundedInverseTheoremToEventFlow x) =
        boundedInverseTheoremFromEventFlow (boundedInverseTheoremToEventFlow y) :=
    congrArg boundedInverseTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BoundedInverseTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BoundedInverseTheoremTasteGate_single_carrier_alignment_round_trip y)))

private def boundedInverseTheoremFields : BoundedInverseTheoremUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedInverseTheoremUp.mk X Y T J O B G H C P N => [X, Y, T, J, O, B, G, H, C, P, N]

private theorem BoundedInverseTheoremTasteGate_single_carrier_alignment_fields :
    forall x y : BoundedInverseTheoremUp,
      boundedInverseTheoremFields x = boundedInverseTheoremFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 T1 J1 O1 B1 G1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 T2 J2 O2 B2 G2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance boundedInverseTheoremBHistCarrier : BHistCarrier BoundedInverseTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedInverseTheoremToEventFlow
  fromEventFlow := boundedInverseTheoremFromEventFlow

instance boundedInverseTheoremChapterTasteGate : ChapterTasteGate BoundedInverseTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedInverseTheoremFromEventFlow (boundedInverseTheoremToEventFlow x) = some x
    exact BoundedInverseTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BoundedInverseTheoremTasteGate_single_carrier_alignment_injective heq)

instance boundedInverseTheoremFieldFaithful : FieldFaithful BoundedInverseTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedInverseTheoremFields
  field_faithful := BoundedInverseTheoremTasteGate_single_carrier_alignment_fields

instance boundedInverseTheoremNontrivial : Nontrivial BoundedInverseTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedInverseTheoremUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedInverseTheoremUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BoundedInverseTheoremTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BoundedInverseTheoremUp) ∧
      Nonempty (FieldFaithful BoundedInverseTheoremUp) ∧
      Nonempty (Nontrivial BoundedInverseTheoremUp) ∧
      (∀ h : BHist, boundedInverseTheoremDecodeBHist (boundedInverseTheoremEncodeBHist h) = h) ∧
      (∀ x : BoundedInverseTheoremUp,
        boundedInverseTheoremFromEventFlow (boundedInverseTheoremToEventFlow x) = some x) ∧
      (∀ x y : BoundedInverseTheoremUp,
        boundedInverseTheoremToEventFlow x = boundedInverseTheoremToEventFlow y → x = y) ∧
      boundedInverseTheoremEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact ⟨boundedInverseTheoremChapterTasteGate⟩
  constructor
  · exact ⟨boundedInverseTheoremFieldFaithful⟩
  constructor
  · exact ⟨boundedInverseTheoremNontrivial⟩
  constructor
  · exact BoundedInverseTheoremTasteGate_single_carrier_alignment_decode
  constructor
  · exact BoundedInverseTheoremTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact BoundedInverseTheoremTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.BoundedInverseTheoremUp.TasteGate
