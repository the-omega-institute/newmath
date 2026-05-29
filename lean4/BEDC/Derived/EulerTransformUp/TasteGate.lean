import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EulerTransformUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EulerTransformUp : Type where
  | mk (S A D T B R H C P N : BHist) : EulerTransformUp
  deriving DecidableEq

def eulerTransformEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: eulerTransformEncodeBHist h
  | BHist.e1 h => BMark.b1 :: eulerTransformEncodeBHist h

def eulerTransformDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (eulerTransformDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (eulerTransformDecodeBHist tail)

private theorem EulerTransformTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, eulerTransformDecodeBHist (eulerTransformEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def eulerTransformFields : EulerTransformUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EulerTransformUp.mk S A D T B R H C P N => [S, A, D, T, B, R, H, C, P, N]

def eulerTransformToEventFlow : EulerTransformUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (eulerTransformFields x).map eulerTransformEncodeBHist

def eulerTransformFromEventFlow : EventFlow → Option EulerTransformUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | A :: restA =>
          match restA with
          | D :: restD =>
              match restD with
              | T :: restT =>
                  match restT with
                  | B :: restB =>
                      match restB with
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
                                                (EulerTransformUp.mk
                                                  (eulerTransformDecodeBHist S)
                                                  (eulerTransformDecodeBHist A)
                                                  (eulerTransformDecodeBHist D)
                                                  (eulerTransformDecodeBHist T)
                                                  (eulerTransformDecodeBHist B)
                                                  (eulerTransformDecodeBHist R)
                                                  (eulerTransformDecodeBHist H)
                                                  (eulerTransformDecodeBHist C)
                                                  (eulerTransformDecodeBHist P)
                                                  (eulerTransformDecodeBHist N))
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

private theorem EulerTransformTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EulerTransformUp,
      eulerTransformFromEventFlow (eulerTransformToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S A D T B R H C P N =>
      change
        some
          (EulerTransformUp.mk
            (eulerTransformDecodeBHist (eulerTransformEncodeBHist S))
            (eulerTransformDecodeBHist (eulerTransformEncodeBHist A))
            (eulerTransformDecodeBHist (eulerTransformEncodeBHist D))
            (eulerTransformDecodeBHist (eulerTransformEncodeBHist T))
            (eulerTransformDecodeBHist (eulerTransformEncodeBHist B))
            (eulerTransformDecodeBHist (eulerTransformEncodeBHist R))
            (eulerTransformDecodeBHist (eulerTransformEncodeBHist H))
            (eulerTransformDecodeBHist (eulerTransformEncodeBHist C))
            (eulerTransformDecodeBHist (eulerTransformEncodeBHist P))
            (eulerTransformDecodeBHist (eulerTransformEncodeBHist N))) =
          some (EulerTransformUp.mk S A D T B R H C P N)
      rw [EulerTransformTasteGate_single_carrier_alignment_decode_encode S,
        EulerTransformTasteGate_single_carrier_alignment_decode_encode A,
        EulerTransformTasteGate_single_carrier_alignment_decode_encode D,
        EulerTransformTasteGate_single_carrier_alignment_decode_encode T,
        EulerTransformTasteGate_single_carrier_alignment_decode_encode B,
        EulerTransformTasteGate_single_carrier_alignment_decode_encode R,
        EulerTransformTasteGate_single_carrier_alignment_decode_encode H,
        EulerTransformTasteGate_single_carrier_alignment_decode_encode C,
        EulerTransformTasteGate_single_carrier_alignment_decode_encode P,
        EulerTransformTasteGate_single_carrier_alignment_decode_encode N]

private theorem EulerTransformTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EulerTransformUp} :
    eulerTransformToEventFlow x = eulerTransformToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      eulerTransformFromEventFlow (eulerTransformToEventFlow x) =
        eulerTransformFromEventFlow (eulerTransformToEventFlow y) :=
    congrArg eulerTransformFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EulerTransformTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (EulerTransformTasteGate_single_carrier_alignment_round_trip y)))

private theorem EulerTransformTasteGate_single_carrier_alignment_fields :
    ∀ x y : EulerTransformUp, eulerTransformFields x = eulerTransformFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 A1 D1 T1 B1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 A2 D2 T2 B2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance eulerTransformBHistCarrier : BHistCarrier EulerTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := eulerTransformToEventFlow
  fromEventFlow := eulerTransformFromEventFlow

instance eulerTransformChapterTasteGate : ChapterTasteGate EulerTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change eulerTransformFromEventFlow (eulerTransformToEventFlow x) = some x
    exact EulerTransformTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EulerTransformTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance eulerTransformFieldFaithful : FieldFaithful EulerTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := eulerTransformFields
  field_faithful := EulerTransformTasteGate_single_carrier_alignment_fields

instance eulerTransformNontrivial : Nontrivial EulerTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EulerTransformUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EulerTransformUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EulerTransformUp :=
  -- BEDC touchpoint anchor: BHist BMark
  eulerTransformChapterTasteGate

theorem EulerTransformTasteGate_single_carrier_alignment :
    (∀ h : BHist, eulerTransformDecodeBHist (eulerTransformEncodeBHist h) = h) ∧
      eulerTransformFields
        (EulerTransformUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact ⟨EulerTransformTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.EulerTransformUp
