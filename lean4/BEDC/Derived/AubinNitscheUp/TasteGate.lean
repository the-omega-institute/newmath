import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AubinNitscheUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AubinNitscheUp : Type where
  | mk (E D R G Q S A H C P N : BHist) : AubinNitscheUp
  deriving DecidableEq

def aubinNitscheEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: aubinNitscheEncodeBHist h
  | BHist.e1 h => BMark.b1 :: aubinNitscheEncodeBHist h

def aubinNitscheDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (aubinNitscheDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (aubinNitscheDecodeBHist tail)

theorem aubinNitscheDecode_encode_bhist :
    ∀ h : BHist, aubinNitscheDecodeBHist (aubinNitscheEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def aubinNitscheDecodePacket
    (E D R G Q S A H C P N : RawEvent) : AubinNitscheUp :=
  -- BEDC touchpoint anchor: BHist BMark
  AubinNitscheUp.mk
    (aubinNitscheDecodeBHist E)
    (aubinNitscheDecodeBHist D)
    (aubinNitscheDecodeBHist R)
    (aubinNitscheDecodeBHist G)
    (aubinNitscheDecodeBHist Q)
    (aubinNitscheDecodeBHist S)
    (aubinNitscheDecodeBHist A)
    (aubinNitscheDecodeBHist H)
    (aubinNitscheDecodeBHist C)
    (aubinNitscheDecodeBHist P)
    (aubinNitscheDecodeBHist N)

def aubinNitscheFields : AubinNitscheUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AubinNitscheUp.mk E D R G Q S A H C P N => [E, D, R, G, Q, S, A, H, C, P, N]

def aubinNitscheToEventFlow : AubinNitscheUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AubinNitscheUp.mk E D R G Q S A H C P N =>
      [aubinNitscheEncodeBHist E, aubinNitscheEncodeBHist D, aubinNitscheEncodeBHist R,
        aubinNitscheEncodeBHist G, aubinNitscheEncodeBHist Q, aubinNitscheEncodeBHist S,
        aubinNitscheEncodeBHist A, aubinNitscheEncodeBHist H, aubinNitscheEncodeBHist C,
        aubinNitscheEncodeBHist P, aubinNitscheEncodeBHist N]

def aubinNitscheFromEventFlow : EventFlow → Option AubinNitscheUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | E :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | G :: rest3 =>
                  match rest3 with
                  | [] => none
                  | Q :: rest4 =>
                      match rest4 with
                      | [] => none
                      | S :: rest5 =>
                          match rest5 with
                          | [] => none
                          | A :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] => some (aubinNitscheDecodePacket E D R G Q S A H C P N)
                                              | _ :: _ => none

private theorem aubinNitsche_round_trip :
    ∀ x : AubinNitscheUp, aubinNitscheFromEventFlow (aubinNitscheToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E D R G Q S A H C P N =>
      change
        some
            (aubinNitscheDecodePacket
              (aubinNitscheEncodeBHist E)
              (aubinNitscheEncodeBHist D)
              (aubinNitscheEncodeBHist R)
              (aubinNitscheEncodeBHist G)
              (aubinNitscheEncodeBHist Q)
              (aubinNitscheEncodeBHist S)
              (aubinNitscheEncodeBHist A)
              (aubinNitscheEncodeBHist H)
              (aubinNitscheEncodeBHist C)
              (aubinNitscheEncodeBHist P)
              (aubinNitscheEncodeBHist N)) =
          some (AubinNitscheUp.mk E D R G Q S A H C P N)
      unfold aubinNitscheDecodePacket
      rw [aubinNitscheDecode_encode_bhist E, aubinNitscheDecode_encode_bhist D,
        aubinNitscheDecode_encode_bhist R, aubinNitscheDecode_encode_bhist G,
        aubinNitscheDecode_encode_bhist Q, aubinNitscheDecode_encode_bhist S,
        aubinNitscheDecode_encode_bhist A, aubinNitscheDecode_encode_bhist H,
        aubinNitscheDecode_encode_bhist C, aubinNitscheDecode_encode_bhist P,
        aubinNitscheDecode_encode_bhist N]

private theorem aubinNitscheToEventFlow_injective {x y : AubinNitscheUp} :
    aubinNitscheToEventFlow x = aubinNitscheToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      aubinNitscheFromEventFlow (aubinNitscheToEventFlow x) =
        aubinNitscheFromEventFlow (aubinNitscheToEventFlow y) :=
    congrArg aubinNitscheFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (aubinNitsche_round_trip x).symm (Eq.trans hread (aubinNitsche_round_trip y)))

instance aubinNitscheBHistCarrier : BHistCarrier AubinNitscheUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := aubinNitscheToEventFlow
  fromEventFlow := aubinNitscheFromEventFlow

instance aubinNitscheChapterTasteGate : ChapterTasteGate AubinNitscheUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change aubinNitscheFromEventFlow (aubinNitscheToEventFlow x) = some x
    exact aubinNitsche_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (aubinNitscheToEventFlow_injective heq)

def taste_gate : ChapterTasteGate AubinNitscheUp :=
  -- BEDC touchpoint anchor: BHist BMark
  aubinNitscheChapterTasteGate

theorem AubinNitscheTasteGate_single_carrier_alignment (x : AubinNitscheUp) :
    ∃ E D R G Q S A H C P N : BHist,
      x = AubinNitscheUp.mk E D R G Q S A H C P N ∧
        aubinNitscheFields x = [E, D, R, G, Q, S, A, H, C, P, N] ∧
          aubinNitscheFromEventFlow (aubinNitscheToEventFlow x) = some x ∧
            aubinNitscheEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  cases x with
  | mk E D R G Q S A H C P N =>
      exact
        ⟨E, D, R, G, Q, S, A, H, C, P, N, rfl, rfl,
          aubinNitsche_round_trip (AubinNitscheUp.mk E D R G Q S A H C P N), rfl⟩

end BEDC.Derived.AubinNitscheUp
