import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GapFailureBridgeAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GapFailureBridgeAuditUp : Type where
  | mk
      (T F B L X A H C P N : BHist) :
      GapFailureBridgeAuditUp
  deriving DecidableEq

def gapFailureBridgeAuditEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: gapFailureBridgeAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: gapFailureBridgeAuditEncodeBHist h

def gapFailureBridgeAuditDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (gapFailureBridgeAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (gapFailureBridgeAuditDecodeBHist tail)

private theorem gapFailureBridgeAudit_decode_encode_bhist :
    ∀ h : BHist,
      gapFailureBridgeAuditDecodeBHist (gapFailureBridgeAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def gapFailureBridgeAuditToEventFlow : GapFailureBridgeAuditUp → EventFlow
  | GapFailureBridgeAuditUp.mk T F B L X A H C P N =>
      [[BMark.b0],
        gapFailureBridgeAuditEncodeBHist T,
        [BMark.b1, BMark.b0],
        gapFailureBridgeAuditEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b0],
        gapFailureBridgeAuditEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gapFailureBridgeAuditEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gapFailureBridgeAuditEncodeBHist X,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gapFailureBridgeAuditEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gapFailureBridgeAuditEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        gapFailureBridgeAuditEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        gapFailureBridgeAuditEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        gapFailureBridgeAuditEncodeBHist N]

def gapFailureBridgeAuditFromEventFlow : EventFlow → Option GapFailureBridgeAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | F :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | B :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | L :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | X :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | A :: rest11 =>
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
                                                                                        (GapFailureBridgeAuditUp.mk
                                                                                          (gapFailureBridgeAuditDecodeBHist T)
                                                                                          (gapFailureBridgeAuditDecodeBHist F)
                                                                                          (gapFailureBridgeAuditDecodeBHist B)
                                                                                          (gapFailureBridgeAuditDecodeBHist L)
                                                                                          (gapFailureBridgeAuditDecodeBHist X)
                                                                                          (gapFailureBridgeAuditDecodeBHist A)
                                                                                          (gapFailureBridgeAuditDecodeBHist H)
                                                                                          (gapFailureBridgeAuditDecodeBHist C)
                                                                                          (gapFailureBridgeAuditDecodeBHist P)
                                                                                          (gapFailureBridgeAuditDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem gapFailureBridgeAudit_round_trip
    (x : GapFailureBridgeAuditUp) :
    gapFailureBridgeAuditFromEventFlow (gapFailureBridgeAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T F B L X A H C P N =>
      change
        some
          (GapFailureBridgeAuditUp.mk
            (gapFailureBridgeAuditDecodeBHist (gapFailureBridgeAuditEncodeBHist T))
            (gapFailureBridgeAuditDecodeBHist (gapFailureBridgeAuditEncodeBHist F))
            (gapFailureBridgeAuditDecodeBHist (gapFailureBridgeAuditEncodeBHist B))
            (gapFailureBridgeAuditDecodeBHist (gapFailureBridgeAuditEncodeBHist L))
            (gapFailureBridgeAuditDecodeBHist (gapFailureBridgeAuditEncodeBHist X))
            (gapFailureBridgeAuditDecodeBHist (gapFailureBridgeAuditEncodeBHist A))
            (gapFailureBridgeAuditDecodeBHist (gapFailureBridgeAuditEncodeBHist H))
            (gapFailureBridgeAuditDecodeBHist (gapFailureBridgeAuditEncodeBHist C))
            (gapFailureBridgeAuditDecodeBHist (gapFailureBridgeAuditEncodeBHist P))
            (gapFailureBridgeAuditDecodeBHist (gapFailureBridgeAuditEncodeBHist N))) =
          some (GapFailureBridgeAuditUp.mk T F B L X A H C P N)
      rw [gapFailureBridgeAudit_decode_encode_bhist T]
      rw [gapFailureBridgeAudit_decode_encode_bhist F]
      rw [gapFailureBridgeAudit_decode_encode_bhist B]
      rw [gapFailureBridgeAudit_decode_encode_bhist L]
      rw [gapFailureBridgeAudit_decode_encode_bhist X]
      rw [gapFailureBridgeAudit_decode_encode_bhist A]
      rw [gapFailureBridgeAudit_decode_encode_bhist H]
      rw [gapFailureBridgeAudit_decode_encode_bhist C]
      rw [gapFailureBridgeAudit_decode_encode_bhist P]
      rw [gapFailureBridgeAudit_decode_encode_bhist N]

private theorem gapFailureBridgeAuditToEventFlow_injective
    {x y : GapFailureBridgeAuditUp} :
    gapFailureBridgeAuditToEventFlow x = gapFailureBridgeAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      gapFailureBridgeAuditFromEventFlow (gapFailureBridgeAuditToEventFlow x) =
        gapFailureBridgeAuditFromEventFlow (gapFailureBridgeAuditToEventFlow y) :=
    congrArg gapFailureBridgeAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (gapFailureBridgeAudit_round_trip x).symm
      (Eq.trans hread (gapFailureBridgeAudit_round_trip y)))

def gapFailureBridgeAuditFields : GapFailureBridgeAuditUp → List BHist
  | GapFailureBridgeAuditUp.mk T F B L X A H C P N =>
      [T, F, B, L, X, A, H, C, P, N]

private theorem gapFailureBridgeAudit_field_faithful :
    ∀ x y : GapFailureBridgeAuditUp,
      gapFailureBridgeAuditFields x = gapFailureBridgeAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 F1 B1 L1 X1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 F2 B2 L2 X2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance gapFailureBridgeAuditBHistCarrier : BHistCarrier GapFailureBridgeAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := gapFailureBridgeAuditToEventFlow
  fromEventFlow := gapFailureBridgeAuditFromEventFlow

instance gapFailureBridgeAuditChapterTasteGate : ChapterTasteGate GapFailureBridgeAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change gapFailureBridgeAuditFromEventFlow (gapFailureBridgeAuditToEventFlow x) = some x
    exact gapFailureBridgeAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (gapFailureBridgeAuditToEventFlow_injective heq)

instance gapFailureBridgeAuditFieldFaithful : FieldFaithful GapFailureBridgeAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := gapFailureBridgeAuditFields
  field_faithful := gapFailureBridgeAudit_field_faithful

instance gapFailureBridgeAuditNontrivial : Nontrivial GapFailureBridgeAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GapFailureBridgeAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      GapFailureBridgeAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro heq
        cases heq⟩

def taste_gate : ChapterTasteGate GapFailureBridgeAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  gapFailureBridgeAuditChapterTasteGate

theorem GapFailureBridgeAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist, gapFailureBridgeAuditDecodeBHist (gapFailureBridgeAuditEncodeBHist h) = h) ∧
      (∀ x : GapFailureBridgeAuditUp,
        gapFailureBridgeAuditFromEventFlow (gapFailureBridgeAuditToEventFlow x) = some x) ∧
      (∀ x y : GapFailureBridgeAuditUp,
        gapFailureBridgeAuditToEventFlow x = gapFailureBridgeAuditToEventFlow y -> x = y) ∧
      gapFailureBridgeAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact gapFailureBridgeAudit_decode_encode_bhist
  · constructor
    · intro x
      exact gapFailureBridgeAudit_round_trip x
    · constructor
      · intro x y heq
        exact gapFailureBridgeAuditToEventFlow_injective heq
      · rfl

end BEDC.Derived.GapFailureBridgeAuditUp
