import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MichaelLineUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MichaelLineUp : Type where
  | mk (R T D O S L H C P N : BHist) : MichaelLineUp
  deriving DecidableEq

def michaelLineEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: michaelLineEncodeBHist h
  | BHist.e1 h => BMark.b1 :: michaelLineEncodeBHist h

def michaelLineDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (michaelLineDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (michaelLineDecodeBHist tail)

private theorem michaelLineDecode_encode_bhist :
    ∀ h : BHist, michaelLineDecodeBHist (michaelLineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def michaelLineFields : MichaelLineUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MichaelLineUp.mk R T D O S L H C P N => [R, T, D, O, S, L, H, C, P, N]

def michaelLineToEventFlow : MichaelLineUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (michaelLineFields x).map michaelLineEncodeBHist

def michaelLineFromEventFlow : EventFlow → Option MichaelLineUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _R :: [] => none
  | _R :: _T :: [] => none
  | _R :: _T :: _D :: [] => none
  | _R :: _T :: _D :: _O :: [] => none
  | _R :: _T :: _D :: _O :: _S :: [] => none
  | _R :: _T :: _D :: _O :: _S :: _L :: [] => none
  | _R :: _T :: _D :: _O :: _S :: _L :: _H :: [] => none
  | _R :: _T :: _D :: _O :: _S :: _L :: _H :: _C :: [] => none
  | _R :: _T :: _D :: _O :: _S :: _L :: _H :: _C :: _P :: [] => none
  | R :: T :: D :: O :: S :: L :: H :: C :: P :: N :: [] =>
      some
        (MichaelLineUp.mk
          (michaelLineDecodeBHist R)
          (michaelLineDecodeBHist T)
          (michaelLineDecodeBHist D)
          (michaelLineDecodeBHist O)
          (michaelLineDecodeBHist S)
          (michaelLineDecodeBHist L)
          (michaelLineDecodeBHist H)
          (michaelLineDecodeBHist C)
          (michaelLineDecodeBHist P)
          (michaelLineDecodeBHist N))
  | _R :: _T :: _D :: _O :: _S :: _L :: _H :: _C :: _P :: _N :: _extra :: _rest =>
      none

private theorem michaelLine_round_trip :
    ∀ x : MichaelLineUp, michaelLineFromEventFlow (michaelLineToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R T D O S L H C P N =>
      change
        some
            (MichaelLineUp.mk
              (michaelLineDecodeBHist (michaelLineEncodeBHist R))
              (michaelLineDecodeBHist (michaelLineEncodeBHist T))
              (michaelLineDecodeBHist (michaelLineEncodeBHist D))
              (michaelLineDecodeBHist (michaelLineEncodeBHist O))
              (michaelLineDecodeBHist (michaelLineEncodeBHist S))
              (michaelLineDecodeBHist (michaelLineEncodeBHist L))
              (michaelLineDecodeBHist (michaelLineEncodeBHist H))
              (michaelLineDecodeBHist (michaelLineEncodeBHist C))
              (michaelLineDecodeBHist (michaelLineEncodeBHist P))
              (michaelLineDecodeBHist (michaelLineEncodeBHist N))) =
          some (MichaelLineUp.mk R T D O S L H C P N)
      rw [michaelLineDecode_encode_bhist R, michaelLineDecode_encode_bhist T,
        michaelLineDecode_encode_bhist D, michaelLineDecode_encode_bhist O,
        michaelLineDecode_encode_bhist S, michaelLineDecode_encode_bhist L,
        michaelLineDecode_encode_bhist H, michaelLineDecode_encode_bhist C,
        michaelLineDecode_encode_bhist P, michaelLineDecode_encode_bhist N]

private theorem michaelLineToEventFlow_injective {x y : MichaelLineUp} :
    michaelLineToEventFlow x = michaelLineToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      michaelLineFromEventFlow (michaelLineToEventFlow x) =
        michaelLineFromEventFlow (michaelLineToEventFlow y) :=
    congrArg michaelLineFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (michaelLine_round_trip x).symm
      (Eq.trans hread (michaelLine_round_trip y)))

private theorem michaelLine_fields_faithful :
    ∀ x y : MichaelLineUp, michaelLineFields x = michaelLineFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R T D O S L H C P N =>
      cases y with
      | mk R' T' D' O' S' L' H' C' P' N' =>
          cases hfields
          rfl

instance michaelLineBHistCarrier : BHistCarrier MichaelLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := michaelLineToEventFlow
  fromEventFlow := michaelLineFromEventFlow

instance michaelLineChapterTasteGate : ChapterTasteGate MichaelLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change michaelLineFromEventFlow (michaelLineToEventFlow x) = some x
    exact michaelLine_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (michaelLineToEventFlow_injective heq)

instance michaelLineFieldFaithful : FieldFaithful MichaelLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := michaelLineFields
  field_faithful := michaelLine_fields_faithful

instance michaelLineNontrivial : Nontrivial MichaelLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MichaelLineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MichaelLineUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def michaelLineTasteGate : ChapterTasteGate MichaelLineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  michaelLineChapterTasteGate

theorem MichaelLineTasteGate_single_carrier_alignment :
    (∀ h : BHist, michaelLineDecodeBHist (michaelLineEncodeBHist h) = h) ∧
      (∀ x : MichaelLineUp,
        michaelLineFromEventFlow (michaelLineToEventFlow x) = some x) ∧
        (∀ x y : MichaelLineUp,
          michaelLineToEventFlow x = michaelLineToEventFlow y → x = y) ∧
          michaelLineEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨michaelLineDecode_encode_bhist,
      michaelLine_round_trip,
      (fun _ _ heq => michaelLineToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MichaelLineUp
