import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProofTermErasureClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProofTermErasureClassifierUp : Type where
  | mk : (proof erased membership replay readback transport provenance name : BHist) →
      ProofTermErasureClassifierUp
  deriving DecidableEq

def proofTermErasureClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: proofTermErasureClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: proofTermErasureClassifierEncodeBHist h

def proofTermErasureClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (proofTermErasureClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (proofTermErasureClassifierDecodeBHist tail)

private theorem ProofTermErasureClassifierTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      proofTermErasureClassifierDecodeBHist
        (proofTermErasureClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def proofTermErasureClassifierToEventFlow :
    ProofTermErasureClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ProofTermErasureClassifierUp.mk proof erased membership replay readback transport
      provenance name =>
      [[BMark.b0],
        proofTermErasureClassifierEncodeBHist proof,
        [BMark.b1, BMark.b0],
        proofTermErasureClassifierEncodeBHist erased,
        [BMark.b1, BMark.b1, BMark.b0],
        proofTermErasureClassifierEncodeBHist membership,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofTermErasureClassifierEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofTermErasureClassifierEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofTermErasureClassifierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofTermErasureClassifierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        proofTermErasureClassifierEncodeBHist name]

def proofTermErasureClassifierFromEventFlow :
    EventFlow → Option ProofTermErasureClassifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | proof :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | erased :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | membership :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | readback :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (ProofTermErasureClassifierUp.mk
                                                                          (proofTermErasureClassifierDecodeBHist
                                                                            proof)
                                                                          (proofTermErasureClassifierDecodeBHist
                                                                            erased)
                                                                          (proofTermErasureClassifierDecodeBHist
                                                                            membership)
                                                                          (proofTermErasureClassifierDecodeBHist
                                                                            replay)
                                                                          (proofTermErasureClassifierDecodeBHist
                                                                            readback)
                                                                          (proofTermErasureClassifierDecodeBHist
                                                                            transport)
                                                                          (proofTermErasureClassifierDecodeBHist
                                                                            provenance)
                                                                          (proofTermErasureClassifierDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem ProofTermErasureClassifierTasteGate_single_carrier_alignment_round :
    ∀ x : ProofTermErasureClassifierUp,
      proofTermErasureClassifierFromEventFlow
        (proofTermErasureClassifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk proof erased membership replay readback transport provenance name =>
      change
        some
          (ProofTermErasureClassifierUp.mk
            (proofTermErasureClassifierDecodeBHist
              (proofTermErasureClassifierEncodeBHist proof))
            (proofTermErasureClassifierDecodeBHist
              (proofTermErasureClassifierEncodeBHist erased))
            (proofTermErasureClassifierDecodeBHist
              (proofTermErasureClassifierEncodeBHist membership))
            (proofTermErasureClassifierDecodeBHist
              (proofTermErasureClassifierEncodeBHist replay))
            (proofTermErasureClassifierDecodeBHist
              (proofTermErasureClassifierEncodeBHist readback))
            (proofTermErasureClassifierDecodeBHist
              (proofTermErasureClassifierEncodeBHist transport))
            (proofTermErasureClassifierDecodeBHist
              (proofTermErasureClassifierEncodeBHist provenance))
            (proofTermErasureClassifierDecodeBHist
              (proofTermErasureClassifierEncodeBHist name))) =
          some
            (ProofTermErasureClassifierUp.mk proof erased membership replay readback
              transport provenance name)
      rw [ProofTermErasureClassifierTasteGate_single_carrier_alignment_decode proof,
        ProofTermErasureClassifierTasteGate_single_carrier_alignment_decode erased,
        ProofTermErasureClassifierTasteGate_single_carrier_alignment_decode membership,
        ProofTermErasureClassifierTasteGate_single_carrier_alignment_decode replay,
        ProofTermErasureClassifierTasteGate_single_carrier_alignment_decode readback,
        ProofTermErasureClassifierTasteGate_single_carrier_alignment_decode transport,
        ProofTermErasureClassifierTasteGate_single_carrier_alignment_decode provenance,
        ProofTermErasureClassifierTasteGate_single_carrier_alignment_decode name]

private theorem ProofTermErasureClassifierTasteGate_single_carrier_alignment_injective
    {x y : ProofTermErasureClassifierUp} :
    proofTermErasureClassifierToEventFlow x =
      proofTermErasureClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      proofTermErasureClassifierFromEventFlow (proofTermErasureClassifierToEventFlow x) =
        proofTermErasureClassifierFromEventFlow (proofTermErasureClassifierToEventFlow y) :=
    congrArg proofTermErasureClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ProofTermErasureClassifierTasteGate_single_carrier_alignment_round x).symm
      (Eq.trans hread
        (ProofTermErasureClassifierTasteGate_single_carrier_alignment_round y)))

instance proofTermErasureClassifierBHistCarrier :
    BHistCarrier ProofTermErasureClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := proofTermErasureClassifierToEventFlow
  fromEventFlow := proofTermErasureClassifierFromEventFlow

instance proofTermErasureClassifierChapterTasteGate :
    ChapterTasteGate ProofTermErasureClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      proofTermErasureClassifierFromEventFlow
        (proofTermErasureClassifierToEventFlow x) = some x
    exact ProofTermErasureClassifierTasteGate_single_carrier_alignment_round x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ProofTermErasureClassifierTasteGate_single_carrier_alignment_injective heq)

instance proofTermErasureClassifierFieldFaithful :
    FieldFaithful ProofTermErasureClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ProofTermErasureClassifierUp.mk proof erased membership replay readback transport
        provenance name =>
        [proof, erased, membership, replay, readback, transport, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk proof1 erased1 membership1 replay1 readback1 transport1 provenance1 name1 =>
        cases y with
        | mk proof2 erased2 membership2 replay2 readback2 transport2 provenance2 name2 =>
            injection h with hProof t1
            injection t1 with hErased t2
            injection t2 with hMembership t3
            injection t3 with hReplay t4
            injection t4 with hReadback t5
            injection t5 with hTransport t6
            injection t6 with hProvenance t7
            injection t7 with hName _
            cases hProof
            cases hErased
            cases hMembership
            cases hReplay
            cases hReadback
            cases hTransport
            cases hProvenance
            cases hName
            rfl

theorem ProofTermErasureClassifierTasteGate_single_carrier_alignment :
    (forall h : BHist, proofTermErasureClassifierDecodeBHist
      (proofTermErasureClassifierEncodeBHist h) = h) /\
      (forall x : ProofTermErasureClassifierUp, proofTermErasureClassifierFromEventFlow
        (proofTermErasureClassifierToEventFlow x) = some x) /\
        (forall x y : ProofTermErasureClassifierUp,
          proofTermErasureClassifierToEventFlow x =
            proofTermErasureClassifierToEventFlow y -> x = y) /\
          proofTermErasureClassifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ProofTermErasureClassifierTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ProofTermErasureClassifierTasteGate_single_carrier_alignment_round
    · constructor
      · intro x y heq
        exact ProofTermErasureClassifierTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.ProofTermErasureClassifierUp
