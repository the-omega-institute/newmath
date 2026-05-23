import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ExtendedRealLineUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ExtendedRealLineUp : Type where
  | mk (T R L U P B H C K N : BHist) : ExtendedRealLineUp
  deriving DecidableEq

def extendedRealLineEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: extendedRealLineEncodeBHist h
  | BHist.e1 h => BMark.b1 :: extendedRealLineEncodeBHist h

def extendedRealLineDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (extendedRealLineDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (extendedRealLineDecodeBHist tail)

private theorem extendedRealLineDecode_encode_bhist :
    ∀ h : BHist, extendedRealLineDecodeBHist (extendedRealLineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def extendedRealLineFields : ExtendedRealLineUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ExtendedRealLineUp.mk T R L U P B H C K N => [T, R, L, U, P, B, H, C, K, N]

def extendedRealLineToEventFlow : ExtendedRealLineUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (extendedRealLineFields x).map extendedRealLineEncodeBHist

def extendedRealLineFromEventFlow : EventFlow → Option ExtendedRealLineUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | T :: restR =>
      match restR with
      | [] => none
      | R :: restL =>
          match restL with
          | [] => none
          | L :: restU =>
              match restU with
              | [] => none
              | U :: restP =>
                  match restP with
                  | [] => none
                  | P :: restB =>
                      match restB with
                      | [] => none
                      | B :: restH =>
                          match restH with
                          | [] => none
                          | H :: restC =>
                              match restC with
                              | [] => none
                              | C :: restK =>
                                  match restK with
                                  | [] => none
                                  | K :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (ExtendedRealLineUp.mk
                                                  (extendedRealLineDecodeBHist T)
                                                  (extendedRealLineDecodeBHist R)
                                                  (extendedRealLineDecodeBHist L)
                                                  (extendedRealLineDecodeBHist U)
                                                  (extendedRealLineDecodeBHist P)
                                                  (extendedRealLineDecodeBHist B)
                                                  (extendedRealLineDecodeBHist H)
                                                  (extendedRealLineDecodeBHist C)
                                                  (extendedRealLineDecodeBHist K)
                                                  (extendedRealLineDecodeBHist N))
                                          | _ :: _ => none

private theorem extendedRealLine_round_trip :
    ∀ x : ExtendedRealLineUp,
      extendedRealLineFromEventFlow (extendedRealLineToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T R L U P B H C K N =>
      change
        some
          (ExtendedRealLineUp.mk
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist T))
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist R))
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist L))
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist U))
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist P))
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist B))
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist H))
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist C))
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist K))
            (extendedRealLineDecodeBHist (extendedRealLineEncodeBHist N))) =
          some (ExtendedRealLineUp.mk T R L U P B H C K N)
      rw [extendedRealLineDecode_encode_bhist T, extendedRealLineDecode_encode_bhist R,
        extendedRealLineDecode_encode_bhist L, extendedRealLineDecode_encode_bhist U,
        extendedRealLineDecode_encode_bhist P, extendedRealLineDecode_encode_bhist B,
        extendedRealLineDecode_encode_bhist H, extendedRealLineDecode_encode_bhist C,
        extendedRealLineDecode_encode_bhist K, extendedRealLineDecode_encode_bhist N]

private theorem extendedRealLineToEventFlow_injective {x y : ExtendedRealLineUp} :
    extendedRealLineToEventFlow x = extendedRealLineToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      extendedRealLineFromEventFlow (extendedRealLineToEventFlow x) =
        extendedRealLineFromEventFlow (extendedRealLineToEventFlow y) :=
    congrArg extendedRealLineFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (extendedRealLine_round_trip x).symm
      (Eq.trans hread (extendedRealLine_round_trip y)))

private theorem extendedRealLineFields_faithful :
    ∀ x y : ExtendedRealLineUp, extendedRealLineFields x = extendedRealLineFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk T1 R1 L1 U1 P1 B1 H1 C1 K1 N1 =>
      cases y with
      | mk T2 R2 L2 U2 P2 B2 H2 C2 K2 N2 =>
          cases h
          rfl

instance extendedRealLineBHistCarrier : BHistCarrier ExtendedRealLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := extendedRealLineToEventFlow
  fromEventFlow := extendedRealLineFromEventFlow

instance extendedRealLineChapterTasteGate : ChapterTasteGate ExtendedRealLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change extendedRealLineFromEventFlow (extendedRealLineToEventFlow x) = some x
    exact extendedRealLine_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (extendedRealLineToEventFlow_injective heq)

instance extendedRealLineFieldFaithful : FieldFaithful ExtendedRealLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := extendedRealLineFields
  field_faithful := extendedRealLineFields_faithful

instance extendedRealLineNontrivial : Nontrivial ExtendedRealLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ExtendedRealLineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ExtendedRealLineUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ExtendedRealLineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  extendedRealLineChapterTasteGate

theorem ExtendedRealLineTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ExtendedRealLineUp) ∧
      Nonempty (FieldFaithful ExtendedRealLineUp) ∧
        Nonempty (Nontrivial ExtendedRealLineUp) ∧
          (∀ h : BHist, extendedRealLineDecodeBHist (extendedRealLineEncodeBHist h) = h) ∧
            (∀ x : ExtendedRealLineUp,
              extendedRealLineFromEventFlow (extendedRealLineToEventFlow x) = some x) ∧
              extendedRealLineEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨extendedRealLineChapterTasteGate⟩, ⟨extendedRealLineFieldFaithful⟩,
      ⟨extendedRealLineNontrivial⟩,
      extendedRealLineDecode_encode_bhist,
      extendedRealLine_round_trip, rfl⟩

namespace TasteGate

theorem ExtendedRealLineTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ExtendedRealLineUp) ∧
      Nonempty (FieldFaithful ExtendedRealLineUp) ∧
        Nonempty (Nontrivial ExtendedRealLineUp) ∧
          (∀ h : BHist, extendedRealLineDecodeBHist (extendedRealLineEncodeBHist h) = h) ∧
            (∀ x : ExtendedRealLineUp,
              extendedRealLineFromEventFlow (extendedRealLineToEventFlow x) = some x) ∧
              (∀ x y : ExtendedRealLineUp,
                extendedRealLineToEventFlow x = extendedRealLineToEventFlow y → x = y) ∧
                extendedRealLineEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨extendedRealLineChapterTasteGate⟩
  · constructor
    · exact ⟨extendedRealLineFieldFaithful⟩
    · constructor
      · exact ⟨extendedRealLineNontrivial⟩
      · constructor
        · exact extendedRealLineDecode_encode_bhist
        · constructor
          · exact extendedRealLine_round_trip
          · constructor
            · intro x y heq
              exact extendedRealLineToEventFlow_injective heq
            · rfl

def taste_gate : ChapterTasteGate ExtendedRealLineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.ExtendedRealLineUp.taste_gate

end TasteGate

end BEDC.Derived.ExtendedRealLineUp
