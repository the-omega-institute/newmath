import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KleeneTreeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KleeneTreeUp : Type where
  | mk (T B L S O H C P N : BHist) : KleeneTreeUp
  deriving DecidableEq

def kleeneTreeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kleeneTreeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kleeneTreeEncodeBHist h

def kleeneTreeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kleeneTreeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kleeneTreeDecodeBHist tail)

private theorem KleeneTreeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, kleeneTreeDecodeBHist (kleeneTreeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kleeneTreeFields : KleeneTreeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KleeneTreeUp.mk T B L S O H C P N => [T, B, L, S, O, H, C, P, N]

def kleeneTreeToEventFlow : KleeneTreeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kleeneTreeFields x).map kleeneTreeEncodeBHist

def kleeneTreeFromEventFlow : EventFlow → Option KleeneTreeUp
  -- BEDC touchpoint anchor: BHist BMark
  | T :: restT =>
      match restT with
      | B :: restB =>
          match restB with
          | L :: restL =>
              match restL with
              | S :: restS =>
                  match restS with
                  | O :: restO =>
                      match restO with
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
                                            (KleeneTreeUp.mk
                                              (kleeneTreeDecodeBHist T)
                                              (kleeneTreeDecodeBHist B)
                                              (kleeneTreeDecodeBHist L)
                                              (kleeneTreeDecodeBHist S)
                                              (kleeneTreeDecodeBHist O)
                                              (kleeneTreeDecodeBHist H)
                                              (kleeneTreeDecodeBHist C)
                                              (kleeneTreeDecodeBHist P)
                                              (kleeneTreeDecodeBHist N))
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

private theorem KleeneTreeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : KleeneTreeUp, kleeneTreeFromEventFlow (kleeneTreeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T B L S O H C P N =>
      change
        some
          (KleeneTreeUp.mk
            (kleeneTreeDecodeBHist (kleeneTreeEncodeBHist T))
            (kleeneTreeDecodeBHist (kleeneTreeEncodeBHist B))
            (kleeneTreeDecodeBHist (kleeneTreeEncodeBHist L))
            (kleeneTreeDecodeBHist (kleeneTreeEncodeBHist S))
            (kleeneTreeDecodeBHist (kleeneTreeEncodeBHist O))
            (kleeneTreeDecodeBHist (kleeneTreeEncodeBHist H))
            (kleeneTreeDecodeBHist (kleeneTreeEncodeBHist C))
            (kleeneTreeDecodeBHist (kleeneTreeEncodeBHist P))
            (kleeneTreeDecodeBHist (kleeneTreeEncodeBHist N))) =
          some (KleeneTreeUp.mk T B L S O H C P N)
      rw [KleeneTreeTasteGate_single_carrier_alignment_decode_encode T,
        KleeneTreeTasteGate_single_carrier_alignment_decode_encode B,
        KleeneTreeTasteGate_single_carrier_alignment_decode_encode L,
        KleeneTreeTasteGate_single_carrier_alignment_decode_encode S,
        KleeneTreeTasteGate_single_carrier_alignment_decode_encode O,
        KleeneTreeTasteGate_single_carrier_alignment_decode_encode H,
        KleeneTreeTasteGate_single_carrier_alignment_decode_encode C,
        KleeneTreeTasteGate_single_carrier_alignment_decode_encode P,
        KleeneTreeTasteGate_single_carrier_alignment_decode_encode N]

private theorem KleeneTreeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KleeneTreeUp} :
    kleeneTreeToEventFlow x = kleeneTreeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kleeneTreeFromEventFlow (kleeneTreeToEventFlow x) =
        kleeneTreeFromEventFlow (kleeneTreeToEventFlow y) :=
    congrArg kleeneTreeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KleeneTreeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (KleeneTreeTasteGate_single_carrier_alignment_round_trip y)))

instance kleeneTreeBHistCarrier : BHistCarrier KleeneTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kleeneTreeToEventFlow
  fromEventFlow := kleeneTreeFromEventFlow

instance kleeneTreeChapterTasteGate : ChapterTasteGate KleeneTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kleeneTreeFromEventFlow (kleeneTreeToEventFlow x) = some x
    exact KleeneTreeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KleeneTreeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate KleeneTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kleeneTreeChapterTasteGate

theorem KleeneTreeTasteGate_single_carrier_alignment :
    (∀ h : BHist, kleeneTreeDecodeBHist (kleeneTreeEncodeBHist h) = h) ∧
      (∀ x : KleeneTreeUp, kleeneTreeFromEventFlow (kleeneTreeToEventFlow x) = some x) ∧
      (∀ x y : KleeneTreeUp,
        kleeneTreeToEventFlow x = kleeneTreeToEventFlow y → x = y) ∧
      kleeneTreeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact KleeneTreeTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact KleeneTreeTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact KleeneTreeTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.KleeneTreeUp
