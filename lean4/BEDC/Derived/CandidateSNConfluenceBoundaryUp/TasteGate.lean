import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CandidateSNConfluenceBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CandidateSNConfluenceBoundaryUp : Type where
  | mk (K N R E S J U H C P L : BHist) : CandidateSNConfluenceBoundaryUp
  deriving DecidableEq

def candidateSNConfluenceBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: candidateSNConfluenceBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: candidateSNConfluenceBoundaryEncodeBHist h

def candidateSNConfluenceBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (candidateSNConfluenceBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (candidateSNConfluenceBoundaryDecodeBHist tail)

private theorem candidateSNConfluenceBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      candidateSNConfluenceBoundaryDecodeBHist
        (candidateSNConfluenceBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def candidateSNConfluenceBoundaryFields :
    CandidateSNConfluenceBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CandidateSNConfluenceBoundaryUp.mk K N R E S J U H C P L =>
      [K, N, R, E, S, J, U, H, C, P, L]

def candidateSNConfluenceBoundaryToEventFlow :
    CandidateSNConfluenceBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (candidateSNConfluenceBoundaryFields x).map
        candidateSNConfluenceBoundaryEncodeBHist

def candidateSNConfluenceBoundaryFromEventFlow :
    EventFlow → Option CandidateSNConfluenceBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _a :: [] => none
  | _a :: _b :: [] => none
  | _a :: _b :: _c :: [] => none
  | _a :: _b :: _c :: _d :: [] => none
  | _a :: _b :: _c :: _d :: _e :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: [] => none
  | K :: N :: R :: E :: S :: J :: U :: H :: C :: P :: L :: [] =>
      some
        (CandidateSNConfluenceBoundaryUp.mk
          (candidateSNConfluenceBoundaryDecodeBHist K)
          (candidateSNConfluenceBoundaryDecodeBHist N)
          (candidateSNConfluenceBoundaryDecodeBHist R)
          (candidateSNConfluenceBoundaryDecodeBHist E)
          (candidateSNConfluenceBoundaryDecodeBHist S)
          (candidateSNConfluenceBoundaryDecodeBHist J)
          (candidateSNConfluenceBoundaryDecodeBHist U)
          (candidateSNConfluenceBoundaryDecodeBHist H)
          (candidateSNConfluenceBoundaryDecodeBHist C)
          (candidateSNConfluenceBoundaryDecodeBHist P)
          (candidateSNConfluenceBoundaryDecodeBHist L))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: _k :: _l ::
      _rest => none

private theorem candidateSNConfluenceBoundary_round_trip :
    ∀ x : CandidateSNConfluenceBoundaryUp,
      candidateSNConfluenceBoundaryFromEventFlow
        (candidateSNConfluenceBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K N R E S J U H C P L =>
      change
        some
          (CandidateSNConfluenceBoundaryUp.mk
            (candidateSNConfluenceBoundaryDecodeBHist
              (candidateSNConfluenceBoundaryEncodeBHist K))
            (candidateSNConfluenceBoundaryDecodeBHist
              (candidateSNConfluenceBoundaryEncodeBHist N))
            (candidateSNConfluenceBoundaryDecodeBHist
              (candidateSNConfluenceBoundaryEncodeBHist R))
            (candidateSNConfluenceBoundaryDecodeBHist
              (candidateSNConfluenceBoundaryEncodeBHist E))
            (candidateSNConfluenceBoundaryDecodeBHist
              (candidateSNConfluenceBoundaryEncodeBHist S))
            (candidateSNConfluenceBoundaryDecodeBHist
              (candidateSNConfluenceBoundaryEncodeBHist J))
            (candidateSNConfluenceBoundaryDecodeBHist
              (candidateSNConfluenceBoundaryEncodeBHist U))
            (candidateSNConfluenceBoundaryDecodeBHist
              (candidateSNConfluenceBoundaryEncodeBHist H))
            (candidateSNConfluenceBoundaryDecodeBHist
              (candidateSNConfluenceBoundaryEncodeBHist C))
            (candidateSNConfluenceBoundaryDecodeBHist
              (candidateSNConfluenceBoundaryEncodeBHist P))
            (candidateSNConfluenceBoundaryDecodeBHist
              (candidateSNConfluenceBoundaryEncodeBHist L))) =
          some (CandidateSNConfluenceBoundaryUp.mk K N R E S J U H C P L)
      rw [candidateSNConfluenceBoundaryDecode_encode_bhist K,
        candidateSNConfluenceBoundaryDecode_encode_bhist N,
        candidateSNConfluenceBoundaryDecode_encode_bhist R,
        candidateSNConfluenceBoundaryDecode_encode_bhist E,
        candidateSNConfluenceBoundaryDecode_encode_bhist S,
        candidateSNConfluenceBoundaryDecode_encode_bhist J,
        candidateSNConfluenceBoundaryDecode_encode_bhist U,
        candidateSNConfluenceBoundaryDecode_encode_bhist H,
        candidateSNConfluenceBoundaryDecode_encode_bhist C,
        candidateSNConfluenceBoundaryDecode_encode_bhist P,
        candidateSNConfluenceBoundaryDecode_encode_bhist L]

private theorem candidateSNConfluenceBoundaryToEventFlow_injective
    {x y : CandidateSNConfluenceBoundaryUp} :
    candidateSNConfluenceBoundaryToEventFlow x =
      candidateSNConfluenceBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      candidateSNConfluenceBoundaryFromEventFlow
          (candidateSNConfluenceBoundaryToEventFlow x) =
        candidateSNConfluenceBoundaryFromEventFlow
          (candidateSNConfluenceBoundaryToEventFlow y) :=
    congrArg candidateSNConfluenceBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (candidateSNConfluenceBoundary_round_trip x).symm
      (Eq.trans hread (candidateSNConfluenceBoundary_round_trip y)))

private theorem candidateSNConfluenceBoundary_fields_faithful :
    ∀ x y : CandidateSNConfluenceBoundaryUp,
      candidateSNConfluenceBoundaryFields x =
        candidateSNConfluenceBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K N R E S J U H C P L =>
      cases y with
      | mk K' N' R' E' S' J' U' H' C' P' L' =>
          cases hfields
          rfl

instance candidateSNConfluenceBoundaryBHistCarrier :
    BHistCarrier CandidateSNConfluenceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := candidateSNConfluenceBoundaryToEventFlow
  fromEventFlow := candidateSNConfluenceBoundaryFromEventFlow

instance candidateSNConfluenceBoundaryChapterTasteGate :
    ChapterTasteGate CandidateSNConfluenceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      candidateSNConfluenceBoundaryFromEventFlow
        (candidateSNConfluenceBoundaryToEventFlow x) = some x
    exact candidateSNConfluenceBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (candidateSNConfluenceBoundaryToEventFlow_injective heq)

instance candidateSNConfluenceBoundaryFieldFaithful :
    FieldFaithful CandidateSNConfluenceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := candidateSNConfluenceBoundaryFields
  field_faithful := candidateSNConfluenceBoundary_fields_faithful

instance candidateSNConfluenceBoundaryNontrivial :
    Nontrivial CandidateSNConfluenceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CandidateSNConfluenceBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CandidateSNConfluenceBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CandidateSNConfluenceBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  candidateSNConfluenceBoundaryChapterTasteGate

def taste_gate_witness : FieldFaithful CandidateSNConfluenceBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  candidateSNConfluenceBoundaryFieldFaithful

theorem CandidateSNConfluenceBoundaryTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CandidateSNConfluenceBoundaryUp) ∧
      Nonempty (FieldFaithful CandidateSNConfluenceBoundaryUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CandidateSNConfluenceBoundaryUp) ∧
          BHistCarrier.fromEventFlow
              (BHistCarrier.toEventFlow
                (CandidateSNConfluenceBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty)) =
            some
              (CandidateSNConfluenceBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨candidateSNConfluenceBoundaryChapterTasteGate⟩
  · constructor
    · exact ⟨candidateSNConfluenceBoundaryFieldFaithful⟩
    · constructor
      · exact ⟨candidateSNConfluenceBoundaryNontrivial⟩
      · change
          candidateSNConfluenceBoundaryFromEventFlow
              (candidateSNConfluenceBoundaryToEventFlow
                (CandidateSNConfluenceBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty)) =
            some
              (CandidateSNConfluenceBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty)
        exact
          candidateSNConfluenceBoundary_round_trip
            (CandidateSNConfluenceBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty)

end BEDC.Derived.CandidateSNConfluenceBoundaryUp
