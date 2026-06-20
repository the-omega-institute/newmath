import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICSnCandidateInterfaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICSnCandidateInterfaceUp : Type where
  | mk (T K L B E F H C P N : BHist) : MetaCICSnCandidateInterfaceUp
  deriving DecidableEq

def metaCICSnCandidateInterfaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICSnCandidateInterfaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICSnCandidateInterfaceEncodeBHist h

def metaCICSnCandidateInterfaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICSnCandidateInterfaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICSnCandidateInterfaceDecodeBHist tail)

private theorem MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      metaCICSnCandidateInterfaceDecodeBHist
        (metaCICSnCandidateInterfaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICSnCandidateInterfaceFields : MetaCICSnCandidateInterfaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICSnCandidateInterfaceUp.mk T K L B E F H C P N =>
      [T, K, L, B, E, F, H, C, P, N]

def metaCICSnCandidateInterfaceToEventFlow :
    MetaCICSnCandidateInterfaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metaCICSnCandidateInterfaceFields x).map
      metaCICSnCandidateInterfaceEncodeBHist

def metaCICSnCandidateInterfaceFromEventFlow :
    EventFlow → Option MetaCICSnCandidateInterfaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | T :: rest0 =>
      match rest0 with
      | [] => none
      | K :: rest1 =>
          match rest1 with
          | [] => none
          | L :: rest2 =>
              match rest2 with
              | [] => none
              | B :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | F :: rest5 =>
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
                                                (MetaCICSnCandidateInterfaceUp.mk
                                                  (metaCICSnCandidateInterfaceDecodeBHist T)
                                                  (metaCICSnCandidateInterfaceDecodeBHist K)
                                                  (metaCICSnCandidateInterfaceDecodeBHist L)
                                                  (metaCICSnCandidateInterfaceDecodeBHist B)
                                                  (metaCICSnCandidateInterfaceDecodeBHist E)
                                                  (metaCICSnCandidateInterfaceDecodeBHist F)
                                                  (metaCICSnCandidateInterfaceDecodeBHist H)
                                                  (metaCICSnCandidateInterfaceDecodeBHist C)
                                                  (metaCICSnCandidateInterfaceDecodeBHist P)
                                                  (metaCICSnCandidateInterfaceDecodeBHist N))
                                          | _ :: _ => none

private theorem MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetaCICSnCandidateInterfaceUp,
      metaCICSnCandidateInterfaceFromEventFlow
        (metaCICSnCandidateInterfaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T K L B E F H C P N =>
      change
        some
          (MetaCICSnCandidateInterfaceUp.mk
            (metaCICSnCandidateInterfaceDecodeBHist
              (metaCICSnCandidateInterfaceEncodeBHist T))
            (metaCICSnCandidateInterfaceDecodeBHist
              (metaCICSnCandidateInterfaceEncodeBHist K))
            (metaCICSnCandidateInterfaceDecodeBHist
              (metaCICSnCandidateInterfaceEncodeBHist L))
            (metaCICSnCandidateInterfaceDecodeBHist
              (metaCICSnCandidateInterfaceEncodeBHist B))
            (metaCICSnCandidateInterfaceDecodeBHist
              (metaCICSnCandidateInterfaceEncodeBHist E))
            (metaCICSnCandidateInterfaceDecodeBHist
              (metaCICSnCandidateInterfaceEncodeBHist F))
            (metaCICSnCandidateInterfaceDecodeBHist
              (metaCICSnCandidateInterfaceEncodeBHist H))
            (metaCICSnCandidateInterfaceDecodeBHist
              (metaCICSnCandidateInterfaceEncodeBHist C))
            (metaCICSnCandidateInterfaceDecodeBHist
              (metaCICSnCandidateInterfaceEncodeBHist P))
            (metaCICSnCandidateInterfaceDecodeBHist
              (metaCICSnCandidateInterfaceEncodeBHist N))) =
          some (MetaCICSnCandidateInterfaceUp.mk T K L B E F H C P N)
      rw [MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_decode_encode T,
        MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_decode_encode K,
        MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_decode_encode L,
        MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_decode_encode B,
        MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_decode_encode E,
        MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_decode_encode F,
        MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_decode_encode H,
        MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_decode_encode C,
        MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_decode_encode P,
        MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetaCICSnCandidateInterfaceUp} :
    metaCICSnCandidateInterfaceToEventFlow x =
        metaCICSnCandidateInterfaceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICSnCandidateInterfaceFromEventFlow
          (metaCICSnCandidateInterfaceToEventFlow x) =
        metaCICSnCandidateInterfaceFromEventFlow
          (metaCICSnCandidateInterfaceToEventFlow y) :=
    congrArg metaCICSnCandidateInterfaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : MetaCICSnCandidateInterfaceUp,
      metaCICSnCandidateInterfaceFields x = metaCICSnCandidateInterfaceFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 K1 L1 B1 E1 F1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 K2 L2 B2 E2 F2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance metaCICSnCandidateInterfaceBHistCarrier :
    BHistCarrier MetaCICSnCandidateInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICSnCandidateInterfaceToEventFlow
  fromEventFlow := metaCICSnCandidateInterfaceFromEventFlow

instance metaCICSnCandidateInterfaceChapterTasteGate :
    ChapterTasteGate MetaCICSnCandidateInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICSnCandidateInterfaceFromEventFlow
        (metaCICSnCandidateInterfaceToEventFlow x) = some x
    exact MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance metaCICSnCandidateInterfaceFieldFaithful :
    FieldFaithful MetaCICSnCandidateInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICSnCandidateInterfaceFields
  field_faithful :=
    MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_field_faithful

instance metaCICSnCandidateInterfaceNontrivial :
    Nontrivial MetaCICSnCandidateInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICSnCandidateInterfaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICSnCandidateInterfaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICSnCandidateInterfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICSnCandidateInterfaceChapterTasteGate

theorem MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICSnCandidateInterfaceDecodeBHist
        (metaCICSnCandidateInterfaceEncodeBHist h) = h) ∧
      (∀ x : MetaCICSnCandidateInterfaceUp,
        metaCICSnCandidateInterfaceFromEventFlow
          (metaCICSnCandidateInterfaceToEventFlow x) = some x) ∧
        (∀ x y : MetaCICSnCandidateInterfaceUp,
          metaCICSnCandidateInterfaceToEventFlow x =
              metaCICSnCandidateInterfaceToEventFlow y →
            x = y) ∧
          metaCICSnCandidateInterfaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_decode_encode,
      MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        MetaCICSnCandidateInterfaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetaCICSnCandidateInterfaceUp
