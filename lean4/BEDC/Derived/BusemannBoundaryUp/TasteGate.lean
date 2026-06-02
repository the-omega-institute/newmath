import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BusemannBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BusemannBoundaryUp : Type where
  | mk (X o R D L H C P N : BHist) : BusemannBoundaryUp
  deriving DecidableEq

def busemannBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: busemannBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: busemannBoundaryEncodeBHist h

def busemannBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (busemannBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (busemannBoundaryDecodeBHist tail)

theorem BusemannBoundaryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

theorem BusemannBoundaryTasteGate_single_carrier_alignment_encode_injective
    {a b : BHist} :
    busemannBoundaryEncodeBHist a = busemannBoundaryEncodeBHist b → a = b := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  have hd :
      busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist a) =
        busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist b) :=
    congrArg busemannBoundaryDecodeBHist h
  exact Eq.trans
    (BusemannBoundaryTasteGate_single_carrier_alignment_decode_encode a).symm
    (Eq.trans hd (BusemannBoundaryTasteGate_single_carrier_alignment_decode_encode b))

def busemannBoundaryFields : BusemannBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BusemannBoundaryUp.mk X o R D L H C P N => [X, o, R, D, L, H, C, P, N]

def busemannBoundaryToEventFlow : BusemannBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (busemannBoundaryFields x).map busemannBoundaryEncodeBHist

def busemannBoundaryFromEventFlow : EventFlow → Option BusemannBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | o :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (BusemannBoundaryUp.mk
                                              (busemannBoundaryDecodeBHist X)
                                              (busemannBoundaryDecodeBHist o)
                                              (busemannBoundaryDecodeBHist R)
                                              (busemannBoundaryDecodeBHist D)
                                              (busemannBoundaryDecodeBHist L)
                                              (busemannBoundaryDecodeBHist H)
                                              (busemannBoundaryDecodeBHist C)
                                              (busemannBoundaryDecodeBHist P)
                                              (busemannBoundaryDecodeBHist N))
                                      | _ :: _ => none

theorem BusemannBoundaryTasteGate_single_carrier_alignment_round_trip
    (x : BusemannBoundaryUp) :
    busemannBoundaryFromEventFlow (busemannBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X o R D L H C P N =>
      change
        some
          (BusemannBoundaryUp.mk
            (busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist X))
            (busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist o))
            (busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist R))
            (busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist D))
            (busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist L))
            (busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist H))
            (busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist C))
            (busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist P))
            (busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist N))) =
          some (BusemannBoundaryUp.mk X o R D L H C P N)
      rw [BusemannBoundaryTasteGate_single_carrier_alignment_decode_encode X,
        BusemannBoundaryTasteGate_single_carrier_alignment_decode_encode o,
        BusemannBoundaryTasteGate_single_carrier_alignment_decode_encode R,
        BusemannBoundaryTasteGate_single_carrier_alignment_decode_encode D,
        BusemannBoundaryTasteGate_single_carrier_alignment_decode_encode L,
        BusemannBoundaryTasteGate_single_carrier_alignment_decode_encode H,
        BusemannBoundaryTasteGate_single_carrier_alignment_decode_encode C,
        BusemannBoundaryTasteGate_single_carrier_alignment_decode_encode P,
        BusemannBoundaryTasteGate_single_carrier_alignment_decode_encode N]

theorem BusemannBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BusemannBoundaryUp} :
    busemannBoundaryToEventFlow x = busemannBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk X₁ o₁ R₁ D₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ o₂ R₂ D₂ L₂ H₂ C₂ P₂ N₂ =>
          injection heq with hX tailX
          injection tailX with ho tailo
          injection tailo with hR tailR
          injection tailR with hD tailD
          injection tailD with hL tailL
          injection tailL with hH tailH
          injection tailH with hC tailC
          injection tailC with hP tailP
          injection tailP with hN _
          cases BusemannBoundaryTasteGate_single_carrier_alignment_encode_injective hX
          cases BusemannBoundaryTasteGate_single_carrier_alignment_encode_injective ho
          cases BusemannBoundaryTasteGate_single_carrier_alignment_encode_injective hR
          cases BusemannBoundaryTasteGate_single_carrier_alignment_encode_injective hD
          cases BusemannBoundaryTasteGate_single_carrier_alignment_encode_injective hL
          cases BusemannBoundaryTasteGate_single_carrier_alignment_encode_injective hH
          cases BusemannBoundaryTasteGate_single_carrier_alignment_encode_injective hC
          cases BusemannBoundaryTasteGate_single_carrier_alignment_encode_injective hP
          cases BusemannBoundaryTasteGate_single_carrier_alignment_encode_injective hN
          rfl

theorem BusemannBoundaryTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : BusemannBoundaryUp, busemannBoundaryFields x = busemannBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ o₁ R₁ D₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ o₂ R₂ D₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance busemannBoundaryBHistCarrier : BHistCarrier BusemannBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := busemannBoundaryToEventFlow
  fromEventFlow := busemannBoundaryFromEventFlow

instance busemannBoundaryChapterTasteGate : ChapterTasteGate BusemannBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change busemannBoundaryFromEventFlow (busemannBoundaryToEventFlow x) = some x
    exact BusemannBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BusemannBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance busemannBoundaryFieldFaithful : FieldFaithful BusemannBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := busemannBoundaryFields
  field_faithful := BusemannBoundaryTasteGate_single_carrier_alignment_field_faithful

instance busemannBoundaryNontrivial : Nontrivial BusemannBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BusemannBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BusemannBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BusemannBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  busemannBoundaryChapterTasteGate

theorem BusemannBoundaryTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier BusemannBoundaryUp) ∧
      Nonempty (ChapterTasteGate BusemannBoundaryUp) ∧
        Nonempty (FieldFaithful BusemannBoundaryUp) ∧
          Nonempty (Nontrivial BusemannBoundaryUp) ∧
            busemannBoundaryEncodeBHist BHist.Empty = ([] : RawEvent) ∧
              busemannBoundaryEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨busemannBoundaryBHistCarrier⟩, ⟨busemannBoundaryChapterTasteGate⟩,
      ⟨busemannBoundaryFieldFaithful⟩, ⟨busemannBoundaryNontrivial⟩, rfl, rfl⟩

end BEDC.Derived.BusemannBoundaryUp
