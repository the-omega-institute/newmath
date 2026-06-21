import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StopTrpFaceRankDeficiencyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StopTrpFaceRankDeficiencyUp : Type where
  | mk (W B C O S R L H K P N : BHist) : StopTrpFaceRankDeficiencyUp
  deriving DecidableEq

def stopTrpFaceRankDeficiencyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stopTrpFaceRankDeficiencyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stopTrpFaceRankDeficiencyEncodeBHist h

def stopTrpFaceRankDeficiencyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stopTrpFaceRankDeficiencyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stopTrpFaceRankDeficiencyDecodeBHist tail)

private theorem stopTrpFaceRankDeficiencyDecodeEncodeBHist :
    ∀ h : BHist,
      stopTrpFaceRankDeficiencyDecodeBHist (stopTrpFaceRankDeficiencyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def stopTrpFaceRankDeficiencyFields : StopTrpFaceRankDeficiencyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StopTrpFaceRankDeficiencyUp.mk W B C O S R L H K P N =>
      [W, B, C, O, S, R, L, H, K, P, N]

def stopTrpFaceRankDeficiencyToEventFlow : StopTrpFaceRankDeficiencyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StopTrpFaceRankDeficiencyUp.mk W B C O S R L H K P N =>
      [[BMark.b0], stopTrpFaceRankDeficiencyEncodeBHist W,
        [BMark.b1], stopTrpFaceRankDeficiencyEncodeBHist B,
        [BMark.b0, BMark.b0], stopTrpFaceRankDeficiencyEncodeBHist C,
        [BMark.b0, BMark.b1], stopTrpFaceRankDeficiencyEncodeBHist O,
        [BMark.b1, BMark.b0], stopTrpFaceRankDeficiencyEncodeBHist S,
        [BMark.b1, BMark.b1], stopTrpFaceRankDeficiencyEncodeBHist R,
        [BMark.b0, BMark.b0, BMark.b0], stopTrpFaceRankDeficiencyEncodeBHist L,
        [BMark.b0, BMark.b0, BMark.b1], stopTrpFaceRankDeficiencyEncodeBHist H,
        [BMark.b0, BMark.b1, BMark.b0], stopTrpFaceRankDeficiencyEncodeBHist K,
        [BMark.b0, BMark.b1, BMark.b1], stopTrpFaceRankDeficiencyEncodeBHist P,
        [BMark.b1, BMark.b0, BMark.b0], stopTrpFaceRankDeficiencyEncodeBHist N]

private def stopTrpFaceRankDeficiencyDecodePacket
    (W B C O S R L H K P N : RawEvent) : StopTrpFaceRankDeficiencyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  StopTrpFaceRankDeficiencyUp.mk
    (stopTrpFaceRankDeficiencyDecodeBHist W)
    (stopTrpFaceRankDeficiencyDecodeBHist B)
    (stopTrpFaceRankDeficiencyDecodeBHist C)
    (stopTrpFaceRankDeficiencyDecodeBHist O)
    (stopTrpFaceRankDeficiencyDecodeBHist S)
    (stopTrpFaceRankDeficiencyDecodeBHist R)
    (stopTrpFaceRankDeficiencyDecodeBHist L)
    (stopTrpFaceRankDeficiencyDecodeBHist H)
    (stopTrpFaceRankDeficiencyDecodeBHist K)
    (stopTrpFaceRankDeficiencyDecodeBHist P)
    (stopTrpFaceRankDeficiencyDecodeBHist N)

def stopTrpFaceRankDeficiencyFromEventFlow :
    EventFlow → Option StopTrpFaceRankDeficiencyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagW :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | _tagB :: rest2 =>
              match rest2 with
              | [] => none
              | B :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tagC :: rest4 =>
                      match rest4 with
                      | [] => none
                      | C :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tagO :: rest6 =>
                              match rest6 with
                              | [] => none
                              | O :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tagS :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | S :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tagR :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | R :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tagL :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | L :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tagH :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | H :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tagK :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | K :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tagP :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | P :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tagN :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | N :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (stopTrpFaceRankDeficiencyDecodePacket
                                                                                                  W B C O S R L H K P N)
                                                                                          | _ :: _ =>
                                                                                              none

private theorem stopTrpFaceRankDeficiency_round_trip :
    ∀ x : StopTrpFaceRankDeficiencyUp,
      stopTrpFaceRankDeficiencyFromEventFlow
        (stopTrpFaceRankDeficiencyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W B C O S R L H K P N =>
      change
        some
          (stopTrpFaceRankDeficiencyDecodePacket
            (stopTrpFaceRankDeficiencyEncodeBHist W)
            (stopTrpFaceRankDeficiencyEncodeBHist B)
            (stopTrpFaceRankDeficiencyEncodeBHist C)
            (stopTrpFaceRankDeficiencyEncodeBHist O)
            (stopTrpFaceRankDeficiencyEncodeBHist S)
            (stopTrpFaceRankDeficiencyEncodeBHist R)
            (stopTrpFaceRankDeficiencyEncodeBHist L)
            (stopTrpFaceRankDeficiencyEncodeBHist H)
            (stopTrpFaceRankDeficiencyEncodeBHist K)
            (stopTrpFaceRankDeficiencyEncodeBHist P)
            (stopTrpFaceRankDeficiencyEncodeBHist N)) =
          some (StopTrpFaceRankDeficiencyUp.mk W B C O S R L H K P N)
      unfold stopTrpFaceRankDeficiencyDecodePacket
      rw [stopTrpFaceRankDeficiencyDecodeEncodeBHist W,
        stopTrpFaceRankDeficiencyDecodeEncodeBHist B,
        stopTrpFaceRankDeficiencyDecodeEncodeBHist C,
        stopTrpFaceRankDeficiencyDecodeEncodeBHist O,
        stopTrpFaceRankDeficiencyDecodeEncodeBHist S,
        stopTrpFaceRankDeficiencyDecodeEncodeBHist R,
        stopTrpFaceRankDeficiencyDecodeEncodeBHist L,
        stopTrpFaceRankDeficiencyDecodeEncodeBHist H,
        stopTrpFaceRankDeficiencyDecodeEncodeBHist K,
        stopTrpFaceRankDeficiencyDecodeEncodeBHist P,
        stopTrpFaceRankDeficiencyDecodeEncodeBHist N]

private theorem stopTrpFaceRankDeficiencyToEventFlow_injective
    {x y : StopTrpFaceRankDeficiencyUp} :
    stopTrpFaceRankDeficiencyToEventFlow x =
      stopTrpFaceRankDeficiencyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stopTrpFaceRankDeficiencyFromEventFlow
          (stopTrpFaceRankDeficiencyToEventFlow x) =
        stopTrpFaceRankDeficiencyFromEventFlow
          (stopTrpFaceRankDeficiencyToEventFlow y) :=
    congrArg stopTrpFaceRankDeficiencyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (stopTrpFaceRankDeficiency_round_trip x).symm
      (Eq.trans hread (stopTrpFaceRankDeficiency_round_trip y)))

instance stopTrpFaceRankDeficiencyBHistCarrier :
    BHistCarrier StopTrpFaceRankDeficiencyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stopTrpFaceRankDeficiencyToEventFlow
  fromEventFlow := stopTrpFaceRankDeficiencyFromEventFlow

instance stopTrpFaceRankDeficiencyChapterTasteGate :
    ChapterTasteGate StopTrpFaceRankDeficiencyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      stopTrpFaceRankDeficiencyFromEventFlow
        (stopTrpFaceRankDeficiencyToEventFlow x) = some x
    exact stopTrpFaceRankDeficiency_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (stopTrpFaceRankDeficiencyToEventFlow_injective heq)

instance stopTrpFaceRankDeficiencyFieldFaithful :
    FieldFaithful StopTrpFaceRankDeficiencyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := stopTrpFaceRankDeficiencyFields
  field_faithful := by
    intro x y hfields
    cases x with
    | mk W B C O S R L H K P N =>
        cases y with
        | mk W' B' C' O' S' R' L' H' K' P' N' =>
            cases hfields
            rfl

instance stopTrpFaceRankDeficiencyNontrivial :
    Nontrivial StopTrpFaceRankDeficiencyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StopTrpFaceRankDeficiencyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StopTrpFaceRankDeficiencyUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem StopTrpFaceRankDeficiencyTasteGate_single_carrier_alignment :
    ∀ x : StopTrpFaceRankDeficiencyUp,
      ∃ W B C O S R L H K P N : BHist,
        x = StopTrpFaceRankDeficiencyUp.mk W B C O S R L H K P N ∧
          stopTrpFaceRankDeficiencyFields x = [W, B, C, O, S, R, L, H, K, P, N] ∧
            stopTrpFaceRankDeficiencyFromEventFlow
              (stopTrpFaceRankDeficiencyToEventFlow x) = some x ∧
              stopTrpFaceRankDeficiencyEncodeBHist BHist.Empty = ([] : RawEvent) ∧
                stopTrpFaceRankDeficiencyEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W B C O S R L H K P N =>
      exact
        ⟨W, B, C, O, S, R, L, H, K, P, N, rfl, rfl,
          stopTrpFaceRankDeficiency_round_trip _, rfl, rfl⟩

def stopTrpFaceRankDeficiencyTasteGate :
    (fun _ : BHist => ChapterTasteGate StopTrpFaceRankDeficiencyUp) BHist.Empty :=
  -- BEDC touchpoint anchor: BHist BMark
  stopTrpFaceRankDeficiencyChapterTasteGate

end BEDC.Derived.StopTrpFaceRankDeficiencyUp
