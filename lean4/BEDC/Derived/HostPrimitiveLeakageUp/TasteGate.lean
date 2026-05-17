import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HostPrimitiveLeakageUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HostPrimitiveLeakageUp : Type where
  | mk : (S Q E D F G H C P N : BHist) → HostPrimitiveLeakageUp
  deriving DecidableEq

def hostPrimitiveLeakageEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hostPrimitiveLeakageEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hostPrimitiveLeakageEncodeBHist h

def hostPrimitiveLeakageDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hostPrimitiveLeakageDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hostPrimitiveLeakageDecodeBHist tail)

private theorem hostPrimitiveLeakage_decode_encode_bhist :
    ∀ h : BHist,
      hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hostPrimitiveLeakageToEventFlow : HostPrimitiveLeakageUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HostPrimitiveLeakageUp.mk S Q E D F G H C P N =>
      [[BMark.b0],
        hostPrimitiveLeakageEncodeBHist S,
        [BMark.b1, BMark.b0],
        hostPrimitiveLeakageEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b0],
        hostPrimitiveLeakageEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hostPrimitiveLeakageEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hostPrimitiveLeakageEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hostPrimitiveLeakageEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hostPrimitiveLeakageEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        hostPrimitiveLeakageEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        hostPrimitiveLeakageEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        hostPrimitiveLeakageEncodeBHist N]

def hostPrimitiveLeakageFromEventFlow :
    EventFlow → Option HostPrimitiveLeakageUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | D :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | F :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | G :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | H :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | C :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | P :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (HostPrimitiveLeakageUp.mk
                                                                                          (hostPrimitiveLeakageDecodeBHist S)
                                                                                          (hostPrimitiveLeakageDecodeBHist Q)
                                                                                          (hostPrimitiveLeakageDecodeBHist E)
                                                                                          (hostPrimitiveLeakageDecodeBHist D)
                                                                                          (hostPrimitiveLeakageDecodeBHist F)
                                                                                          (hostPrimitiveLeakageDecodeBHist G)
                                                                                          (hostPrimitiveLeakageDecodeBHist H)
                                                                                          (hostPrimitiveLeakageDecodeBHist C)
                                                                                          (hostPrimitiveLeakageDecodeBHist P)
                                                                                          (hostPrimitiveLeakageDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem hostPrimitiveLeakage_round_trip :
    ∀ x : HostPrimitiveLeakageUp,
      hostPrimitiveLeakageFromEventFlow (hostPrimitiveLeakageToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q E D F G H C P N =>
      change
        some
          (HostPrimitiveLeakageUp.mk
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist S))
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist Q))
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist E))
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist D))
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist F))
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist G))
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist H))
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist C))
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist P))
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist N))) =
          some (HostPrimitiveLeakageUp.mk S Q E D F G H C P N)
      rw [hostPrimitiveLeakage_decode_encode_bhist S,
        hostPrimitiveLeakage_decode_encode_bhist Q,
        hostPrimitiveLeakage_decode_encode_bhist E,
        hostPrimitiveLeakage_decode_encode_bhist D,
        hostPrimitiveLeakage_decode_encode_bhist F,
        hostPrimitiveLeakage_decode_encode_bhist G,
        hostPrimitiveLeakage_decode_encode_bhist H,
        hostPrimitiveLeakage_decode_encode_bhist C,
        hostPrimitiveLeakage_decode_encode_bhist P,
        hostPrimitiveLeakage_decode_encode_bhist N]

private theorem hostPrimitiveLeakageToEventFlow_injective {x y : HostPrimitiveLeakageUp} :
    hostPrimitiveLeakageToEventFlow x = hostPrimitiveLeakageToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hostPrimitiveLeakageFromEventFlow (hostPrimitiveLeakageToEventFlow x) =
        hostPrimitiveLeakageFromEventFlow (hostPrimitiveLeakageToEventFlow y) :=
    congrArg hostPrimitiveLeakageFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hostPrimitiveLeakage_round_trip x).symm
      (Eq.trans hread (hostPrimitiveLeakage_round_trip y)))

def hostPrimitiveLeakageFields : HostPrimitiveLeakageUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HostPrimitiveLeakageUp.mk S Q E D F G H C P N => [S, Q, E, D, F, G, H, C, P, N]

private theorem hostPrimitiveLeakage_field_faithful :
    ∀ x y : HostPrimitiveLeakageUp,
      hostPrimitiveLeakageFields x = hostPrimitiveLeakageFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S Q E D F G H C P N =>
      cases y with
      | mk S' Q' E' D' F' G' H' C' P' N' =>
          cases hfields
          rfl

instance hostPrimitiveLeakageBHistCarrier :
    BHistCarrier HostPrimitiveLeakageUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hostPrimitiveLeakageToEventFlow
  fromEventFlow := hostPrimitiveLeakageFromEventFlow

instance hostPrimitiveLeakageChapterTasteGate :
    ChapterTasteGate HostPrimitiveLeakageUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hostPrimitiveLeakageFromEventFlow (hostPrimitiveLeakageToEventFlow x) = some x
    exact hostPrimitiveLeakage_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hostPrimitiveLeakageToEventFlow_injective heq)

instance hostPrimitiveLeakageFieldFaithful :
    FieldFaithful HostPrimitiveLeakageUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hostPrimitiveLeakageFields
  field_faithful := hostPrimitiveLeakage_field_faithful

instance hostPrimitiveLeakageNontrivial :
    Nontrivial HostPrimitiveLeakageUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HostPrimitiveLeakageUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HostPrimitiveLeakageUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HostPrimitiveLeakageUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hostPrimitiveLeakageChapterTasteGate

end BEDC.Derived.HostPrimitiveLeakageUp
