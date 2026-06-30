import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailRequestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailRequestUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk : (W Q D R E H C P N : BHist) → CauchyTailRequestUp
  deriving DecidableEq

def cauchyTailRequestEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailRequestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailRequestEncodeBHist h

def cauchyTailRequestDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailRequestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailRequestDecodeBHist tail)

private theorem cauchyTailRequest_decode_encode_bhist :
    ∀ h : BHist, cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyTailRequestFields : CauchyTailRequestUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailRequestUp.mk W Q D R E H C P N => [W, Q, D, R, E, H, C, P, N]

def cauchyTailRequestToEventFlow : CauchyTailRequestUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailRequestUp.mk W Q D R E H C P N =>
      [[BMark.b1, BMark.b0, BMark.b0],
        cauchyTailRequestEncodeBHist W,
        cauchyTailRequestEncodeBHist Q,
        cauchyTailRequestEncodeBHist D,
        cauchyTailRequestEncodeBHist R,
        cauchyTailRequestEncodeBHist E,
        cauchyTailRequestEncodeBHist H,
        cauchyTailRequestEncodeBHist C,
        cauchyTailRequestEncodeBHist P,
        cauchyTailRequestEncodeBHist N]

def cauchyTailRequestFromEventFlow : EventFlow → Option CauchyTailRequestUp
  -- BEDC touchpoint anchor: BHist BMark
  | [[BMark.b1, BMark.b0, BMark.b0], W, Q, D, R, E, H, C, P, N] =>
      some
        (CauchyTailRequestUp.mk
          (cauchyTailRequestDecodeBHist W)
          (cauchyTailRequestDecodeBHist Q)
          (cauchyTailRequestDecodeBHist D)
          (cauchyTailRequestDecodeBHist R)
          (cauchyTailRequestDecodeBHist E)
          (cauchyTailRequestDecodeBHist H)
          (cauchyTailRequestDecodeBHist C)
          (cauchyTailRequestDecodeBHist P)
          (cauchyTailRequestDecodeBHist N))
  | _ => none

private theorem cauchyTailRequest_round_trip :
    ∀ x : CauchyTailRequestUp,
      cauchyTailRequestFromEventFlow (cauchyTailRequestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W Q D R E H C P N =>
      change
        some
          (CauchyTailRequestUp.mk
            (cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist W))
            (cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist Q))
            (cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist D))
            (cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist R))
            (cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist E))
            (cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist H))
            (cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist C))
            (cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist P))
            (cauchyTailRequestDecodeBHist (cauchyTailRequestEncodeBHist N))) =
          some (CauchyTailRequestUp.mk W Q D R E H C P N)
      rw [cauchyTailRequest_decode_encode_bhist W,
        cauchyTailRequest_decode_encode_bhist Q,
        cauchyTailRequest_decode_encode_bhist D,
        cauchyTailRequest_decode_encode_bhist R,
        cauchyTailRequest_decode_encode_bhist E,
        cauchyTailRequest_decode_encode_bhist H,
        cauchyTailRequest_decode_encode_bhist C,
        cauchyTailRequest_decode_encode_bhist P,
        cauchyTailRequest_decode_encode_bhist N]

private theorem cauchyTailRequestToEventFlow_injective {x y : CauchyTailRequestUp} :
    cauchyTailRequestToEventFlow x = cauchyTailRequestToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailRequestFromEventFlow (cauchyTailRequestToEventFlow x) =
        cauchyTailRequestFromEventFlow (cauchyTailRequestToEventFlow y) :=
    congrArg cauchyTailRequestFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyTailRequest_round_trip x).symm
      (Eq.trans hread (cauchyTailRequest_round_trip y)))

private theorem cauchyTailRequest_field_faithful :
    ∀ x y : CauchyTailRequestUp,
      cauchyTailRequestFields x = cauchyTailRequestFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Wa Qa Da Ra Ea Ha Ca Pa Na =>
      cases y with
      | mk Wb Qb Db Rb Eb Hb Cb Pb Nb =>
          injection hfields with hW t1
          injection t1 with hQ t2
          injection t2 with hD t3
          injection t3 with hR t4
          injection t4 with hE t5
          injection t5 with hH t6
          injection t6 with hC t7
          injection t7 with hP t8
          injection t8 with hN _
          cases hW
          cases hQ
          cases hD
          cases hR
          cases hE
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance cauchyTailRequestBHistCarrier : BHistCarrier CauchyTailRequestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailRequestToEventFlow
  fromEventFlow := cauchyTailRequestFromEventFlow

instance cauchyTailRequestChapterTasteGate : ChapterTasteGate CauchyTailRequestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyTailRequestFromEventFlow (cauchyTailRequestToEventFlow x) = some x
    exact cauchyTailRequest_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyTailRequestToEventFlow_injective heq)

instance cauchyTailRequestFieldFaithful : FieldFaithful CauchyTailRequestUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyTailRequestFields
  field_faithful := cauchyTailRequest_field_faithful

instance cauchyTailRequestNontrivial : Nontrivial CauchyTailRequestUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyTailRequestUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyTailRequestUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyTailRequestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyTailRequestChapterTasteGate

theorem CauchyTailRequestTasteGate_single_carrier_alignment :
    ∀ W Q D R E H C P N : BHist,
      cauchyTailRequestToEventFlow (CauchyTailRequestUp.mk W Q D R E H C P N) =
        [[BMark.b1, BMark.b0, BMark.b0],
          cauchyTailRequestEncodeBHist W,
          cauchyTailRequestEncodeBHist Q,
          cauchyTailRequestEncodeBHist D,
          cauchyTailRequestEncodeBHist R,
          cauchyTailRequestEncodeBHist E,
          cauchyTailRequestEncodeBHist H,
          cauchyTailRequestEncodeBHist C,
          cauchyTailRequestEncodeBHist P,
          cauchyTailRequestEncodeBHist N] := by
  -- BEDC touchpoint anchor: BHist BMark
  intro W Q D R E H C P N
  rfl

end BEDC.Derived.CauchyTailRequestUp
