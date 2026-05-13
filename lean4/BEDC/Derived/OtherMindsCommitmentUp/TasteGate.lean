import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OtherMindsCommitmentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OtherMindsCommitmentUp : Type where
  | mk :
      (observer candidate locality evidence gap transports routes provenance name : BHist) →
      OtherMindsCommitmentUp
  deriving DecidableEq

private def otherMindsCommitmentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: otherMindsCommitmentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: otherMindsCommitmentEncodeBHist h

private def otherMindsCommitmentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (otherMindsCommitmentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (otherMindsCommitmentDecodeBHist tail)

private theorem otherMindsCommitmentDecode_encode_bhist :
    ∀ h : BHist, otherMindsCommitmentDecodeBHist (otherMindsCommitmentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def otherMindsCommitmentToEventFlow : OtherMindsCommitmentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | OtherMindsCommitmentUp.mk observer candidate locality evidence gap transports routes
      provenance name =>
      [[BMark.b0],
        otherMindsCommitmentEncodeBHist observer,
        [BMark.b1, BMark.b0],
        otherMindsCommitmentEncodeBHist candidate,
        [BMark.b1, BMark.b1, BMark.b0],
        otherMindsCommitmentEncodeBHist locality,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        otherMindsCommitmentEncodeBHist evidence,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        otherMindsCommitmentEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        otherMindsCommitmentEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        otherMindsCommitmentEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        otherMindsCommitmentEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        otherMindsCommitmentEncodeBHist name]

private def otherMindsCommitmentFromEventFlow : EventFlow → Option OtherMindsCommitmentUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | observer :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | candidate :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | locality :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | evidence :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | gap :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transports :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (OtherMindsCommitmentUp.mk
                                                                                  (otherMindsCommitmentDecodeBHist
                                                                                    observer)
                                                                                  (otherMindsCommitmentDecodeBHist
                                                                                    candidate)
                                                                                  (otherMindsCommitmentDecodeBHist
                                                                                    locality)
                                                                                  (otherMindsCommitmentDecodeBHist
                                                                                    evidence)
                                                                                  (otherMindsCommitmentDecodeBHist
                                                                                    gap)
                                                                                  (otherMindsCommitmentDecodeBHist
                                                                                    transports)
                                                                                  (otherMindsCommitmentDecodeBHist
                                                                                    routes)
                                                                                  (otherMindsCommitmentDecodeBHist
                                                                                    provenance)
                                                                                  (otherMindsCommitmentDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem otherMindsCommitment_round_trip :
    ∀ x : OtherMindsCommitmentUp,
      otherMindsCommitmentFromEventFlow (otherMindsCommitmentToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observer candidate locality evidence gap transports routes provenance name =>
      change
        some
          (OtherMindsCommitmentUp.mk
            (otherMindsCommitmentDecodeBHist (otherMindsCommitmentEncodeBHist observer))
            (otherMindsCommitmentDecodeBHist (otherMindsCommitmentEncodeBHist candidate))
            (otherMindsCommitmentDecodeBHist (otherMindsCommitmentEncodeBHist locality))
            (otherMindsCommitmentDecodeBHist (otherMindsCommitmentEncodeBHist evidence))
            (otherMindsCommitmentDecodeBHist (otherMindsCommitmentEncodeBHist gap))
            (otherMindsCommitmentDecodeBHist (otherMindsCommitmentEncodeBHist transports))
            (otherMindsCommitmentDecodeBHist (otherMindsCommitmentEncodeBHist routes))
            (otherMindsCommitmentDecodeBHist (otherMindsCommitmentEncodeBHist provenance))
            (otherMindsCommitmentDecodeBHist (otherMindsCommitmentEncodeBHist name))) =
          some
            (OtherMindsCommitmentUp.mk observer candidate locality evidence gap transports
              routes provenance name)
      rw [otherMindsCommitmentDecode_encode_bhist observer,
        otherMindsCommitmentDecode_encode_bhist candidate,
        otherMindsCommitmentDecode_encode_bhist locality,
        otherMindsCommitmentDecode_encode_bhist evidence,
        otherMindsCommitmentDecode_encode_bhist gap,
        otherMindsCommitmentDecode_encode_bhist transports,
        otherMindsCommitmentDecode_encode_bhist routes,
        otherMindsCommitmentDecode_encode_bhist provenance,
        otherMindsCommitmentDecode_encode_bhist name]

private theorem otherMindsCommitmentToEventFlow_injective {x y : OtherMindsCommitmentUp} :
    otherMindsCommitmentToEventFlow x = otherMindsCommitmentToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      otherMindsCommitmentFromEventFlow (otherMindsCommitmentToEventFlow x) =
        otherMindsCommitmentFromEventFlow (otherMindsCommitmentToEventFlow y) :=
    congrArg otherMindsCommitmentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (otherMindsCommitment_round_trip x).symm
      (Eq.trans hread (otherMindsCommitment_round_trip y)))

instance otherMindsCommitmentBHistCarrier : BHistCarrier OtherMindsCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := otherMindsCommitmentToEventFlow
  fromEventFlow := otherMindsCommitmentFromEventFlow

def otherMindsCommitmentTasteGate : ChapterTasteGate OtherMindsCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change otherMindsCommitmentFromEventFlow (otherMindsCommitmentToEventFlow x) = some x
    exact otherMindsCommitment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (otherMindsCommitmentToEventFlow_injective heq)

instance otherMindsCommitmentTasteGate_instance : ChapterTasteGate OtherMindsCommitmentUp :=
  -- BEDC touchpoint anchor: BHist BMark
  otherMindsCommitmentTasteGate

end BEDC.Derived.OtherMindsCommitmentUp
