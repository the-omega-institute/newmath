import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CandidateEvidenceSNRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CandidateEvidenceSNRouteUp : Type where
  | mk (E K M A I H C P N : BHist) : CandidateEvidenceSNRouteUp
  deriving DecidableEq

def candidateEvidenceSNRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: candidateEvidenceSNRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: candidateEvidenceSNRouteEncodeBHist h

def candidateEvidenceSNRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (candidateEvidenceSNRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (candidateEvidenceSNRouteDecodeBHist tail)

private theorem candidateEvidenceSNRouteDecode_encode_bhist :
    ∀ h : BHist,
      candidateEvidenceSNRouteDecodeBHist
        (candidateEvidenceSNRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def candidateEvidenceSNRouteToEventFlow :
    CandidateEvidenceSNRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CandidateEvidenceSNRouteUp.mk E K M A I H C P N =>
      [candidateEvidenceSNRouteEncodeBHist E,
        candidateEvidenceSNRouteEncodeBHist K,
        candidateEvidenceSNRouteEncodeBHist M,
        candidateEvidenceSNRouteEncodeBHist A,
        candidateEvidenceSNRouteEncodeBHist I,
        candidateEvidenceSNRouteEncodeBHist H,
        candidateEvidenceSNRouteEncodeBHist C,
        candidateEvidenceSNRouteEncodeBHist P,
        candidateEvidenceSNRouteEncodeBHist N]

def candidateEvidenceSNRouteFromEventFlow :
    EventFlow → Option CandidateEvidenceSNRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | E :: rest0 =>
      match rest0 with
      | [] => none
      | K :: rest1 =>
          match rest1 with
          | [] => none
          | M :: rest2 =>
              match rest2 with
              | [] => none
              | A :: rest3 =>
                  match rest3 with
                  | [] => none
                  | I :: rest4 =>
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
                                            (CandidateEvidenceSNRouteUp.mk
                                              (candidateEvidenceSNRouteDecodeBHist E)
                                              (candidateEvidenceSNRouteDecodeBHist K)
                                              (candidateEvidenceSNRouteDecodeBHist M)
                                              (candidateEvidenceSNRouteDecodeBHist A)
                                              (candidateEvidenceSNRouteDecodeBHist I)
                                              (candidateEvidenceSNRouteDecodeBHist H)
                                              (candidateEvidenceSNRouteDecodeBHist C)
                                              (candidateEvidenceSNRouteDecodeBHist P)
                                              (candidateEvidenceSNRouteDecodeBHist N))
                                      | _ :: _ => none

private theorem candidateEvidenceSNRoute_round_trip :
    ∀ x : CandidateEvidenceSNRouteUp,
      candidateEvidenceSNRouteFromEventFlow
        (candidateEvidenceSNRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E K M A I H C P N =>
      change
        some
          (CandidateEvidenceSNRouteUp.mk
            (candidateEvidenceSNRouteDecodeBHist
              (candidateEvidenceSNRouteEncodeBHist E))
            (candidateEvidenceSNRouteDecodeBHist
              (candidateEvidenceSNRouteEncodeBHist K))
            (candidateEvidenceSNRouteDecodeBHist
              (candidateEvidenceSNRouteEncodeBHist M))
            (candidateEvidenceSNRouteDecodeBHist
              (candidateEvidenceSNRouteEncodeBHist A))
            (candidateEvidenceSNRouteDecodeBHist
              (candidateEvidenceSNRouteEncodeBHist I))
            (candidateEvidenceSNRouteDecodeBHist
              (candidateEvidenceSNRouteEncodeBHist H))
            (candidateEvidenceSNRouteDecodeBHist
              (candidateEvidenceSNRouteEncodeBHist C))
            (candidateEvidenceSNRouteDecodeBHist
              (candidateEvidenceSNRouteEncodeBHist P))
            (candidateEvidenceSNRouteDecodeBHist
              (candidateEvidenceSNRouteEncodeBHist N))) =
          some (CandidateEvidenceSNRouteUp.mk E K M A I H C P N)
      rw [candidateEvidenceSNRouteDecode_encode_bhist E,
        candidateEvidenceSNRouteDecode_encode_bhist K,
        candidateEvidenceSNRouteDecode_encode_bhist M,
        candidateEvidenceSNRouteDecode_encode_bhist A,
        candidateEvidenceSNRouteDecode_encode_bhist I,
        candidateEvidenceSNRouteDecode_encode_bhist H,
        candidateEvidenceSNRouteDecode_encode_bhist C,
        candidateEvidenceSNRouteDecode_encode_bhist P,
        candidateEvidenceSNRouteDecode_encode_bhist N]

private theorem candidateEvidenceSNRouteToEventFlow_injective
    {x y : CandidateEvidenceSNRouteUp} :
    candidateEvidenceSNRouteToEventFlow x =
      candidateEvidenceSNRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      candidateEvidenceSNRouteFromEventFlow
          (candidateEvidenceSNRouteToEventFlow x) =
        candidateEvidenceSNRouteFromEventFlow
          (candidateEvidenceSNRouteToEventFlow y) :=
    congrArg candidateEvidenceSNRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (candidateEvidenceSNRoute_round_trip x).symm
      (Eq.trans hread (candidateEvidenceSNRoute_round_trip y)))

private def candidateEvidenceSNRouteFields :
    CandidateEvidenceSNRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CandidateEvidenceSNRouteUp.mk E K M A I H C P N => [E, K, M, A, I, H, C, P, N]

private theorem candidateEvidenceSNRoute_fields_faithful :
    ∀ x y : CandidateEvidenceSNRouteUp,
      candidateEvidenceSNRouteFields x = candidateEvidenceSNRouteFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E1 K1 M1 A1 I1 H1 C1 P1 N1 =>
      cases y with
      | mk E2 K2 M2 A2 I2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance candidateEvidenceSNRouteBHistCarrier :
    BHistCarrier CandidateEvidenceSNRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := candidateEvidenceSNRouteToEventFlow
  fromEventFlow := candidateEvidenceSNRouteFromEventFlow

instance candidateEvidenceSNRouteChapterTasteGate :
    ChapterTasteGate CandidateEvidenceSNRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      candidateEvidenceSNRouteFromEventFlow
        (candidateEvidenceSNRouteToEventFlow x) = some x
    exact candidateEvidenceSNRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (candidateEvidenceSNRouteToEventFlow_injective heq)

instance candidateEvidenceSNRouteFieldFaithful :
    FieldFaithful CandidateEvidenceSNRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := candidateEvidenceSNRouteFields
  field_faithful := candidateEvidenceSNRoute_fields_faithful

instance candidateEvidenceSNRouteNontrivial :
    Nontrivial CandidateEvidenceSNRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CandidateEvidenceSNRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CandidateEvidenceSNRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CandidateEvidenceSNRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  candidateEvidenceSNRouteChapterTasteGate

theorem CandidateEvidenceSNRouteTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      candidateEvidenceSNRouteDecodeBHist
        (candidateEvidenceSNRouteEncodeBHist h) = h) ∧
      (∀ x : CandidateEvidenceSNRouteUp,
        candidateEvidenceSNRouteFromEventFlow
          (candidateEvidenceSNRouteToEventFlow x) = some x) ∧
        (∀ x y : CandidateEvidenceSNRouteUp,
          candidateEvidenceSNRouteToEventFlow x =
            candidateEvidenceSNRouteToEventFlow y → x = y) ∧
          candidateEvidenceSNRouteEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∃ x y : CandidateEvidenceSNRouteUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨candidateEvidenceSNRouteDecode_encode_bhist,
      candidateEvidenceSNRoute_round_trip,
      (fun _ _ heq => candidateEvidenceSNRouteToEventFlow_injective heq),
      rfl,
      ⟨CandidateEvidenceSNRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        CandidateEvidenceSNRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

end BEDC.Derived.CandidateEvidenceSNRouteUp
