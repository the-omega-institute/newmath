import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InductionClosureLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InductionClosureLedgerUp : Type where
  | mk : (generator classifier residue transport continuation provenance name : BHist) →
      InductionClosureLedgerUp
  deriving DecidableEq

def inductionClosureLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inductionClosureLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inductionClosureLedgerEncodeBHist h

def inductionClosureLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inductionClosureLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inductionClosureLedgerDecodeBHist tail)

private theorem inductionClosureLedger_decode_encode_bhist :
    ∀ h : BHist,
      inductionClosureLedgerDecodeBHist (inductionClosureLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem inductionClosureLedger_mk_congr
    {generator generator' classifier classifier' residue residue' transport transport'
      continuation continuation' provenance provenance' name name' : BHist}
    (hGenerator : generator' = generator)
    (hClassifier : classifier' = classifier)
    (hResidue : residue' = residue)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    InductionClosureLedgerUp.mk generator' classifier' residue' transport'
        continuation' provenance' name' =
      InductionClosureLedgerUp.mk generator classifier residue transport continuation
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hGenerator
  cases hClassifier
  cases hResidue
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

def inductionClosureLedgerToEventFlow : InductionClosureLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InductionClosureLedgerUp.mk generator classifier residue transport continuation
      provenance name =>
      [[BMark.b0],
        inductionClosureLedgerEncodeBHist generator,
        [BMark.b1, BMark.b0],
        inductionClosureLedgerEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b0],
        inductionClosureLedgerEncodeBHist residue,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inductionClosureLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inductionClosureLedgerEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inductionClosureLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inductionClosureLedgerEncodeBHist name]

def inductionClosureLedgerFromEventFlow : EventFlow → Option InductionClosureLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | generator :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | classifier :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | residue :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | continuation :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | name :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (InductionClosureLedgerUp.mk
                                                                  (inductionClosureLedgerDecodeBHist generator)
                                                                  (inductionClosureLedgerDecodeBHist classifier)
                                                                  (inductionClosureLedgerDecodeBHist residue)
                                                                  (inductionClosureLedgerDecodeBHist transport)
                                                                  (inductionClosureLedgerDecodeBHist continuation)
                                                                  (inductionClosureLedgerDecodeBHist provenance)
                                                                  (inductionClosureLedgerDecodeBHist name))
                                                          | _ :: _ => none

private theorem inductionClosureLedger_round_trip :
    ∀ x : InductionClosureLedgerUp,
      inductionClosureLedgerFromEventFlow (inductionClosureLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk generator classifier residue transport continuation provenance name =>
      change
        some
          (InductionClosureLedgerUp.mk
            (inductionClosureLedgerDecodeBHist
              (inductionClosureLedgerEncodeBHist generator))
            (inductionClosureLedgerDecodeBHist
              (inductionClosureLedgerEncodeBHist classifier))
            (inductionClosureLedgerDecodeBHist
              (inductionClosureLedgerEncodeBHist residue))
            (inductionClosureLedgerDecodeBHist
              (inductionClosureLedgerEncodeBHist transport))
            (inductionClosureLedgerDecodeBHist
              (inductionClosureLedgerEncodeBHist continuation))
            (inductionClosureLedgerDecodeBHist
              (inductionClosureLedgerEncodeBHist provenance))
            (inductionClosureLedgerDecodeBHist
              (inductionClosureLedgerEncodeBHist name))) =
          some
            (InductionClosureLedgerUp.mk generator classifier residue transport
              continuation provenance name)
      exact
        congrArg some
          (inductionClosureLedger_mk_congr
            (inductionClosureLedger_decode_encode_bhist generator)
            (inductionClosureLedger_decode_encode_bhist classifier)
            (inductionClosureLedger_decode_encode_bhist residue)
            (inductionClosureLedger_decode_encode_bhist transport)
            (inductionClosureLedger_decode_encode_bhist continuation)
            (inductionClosureLedger_decode_encode_bhist provenance)
            (inductionClosureLedger_decode_encode_bhist name))

private theorem inductionClosureLedgerToEventFlow_injective
    {x y : InductionClosureLedgerUp} :
    inductionClosureLedgerToEventFlow x = inductionClosureLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inductionClosureLedgerFromEventFlow (inductionClosureLedgerToEventFlow x) =
        inductionClosureLedgerFromEventFlow (inductionClosureLedgerToEventFlow y) :=
    congrArg inductionClosureLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (inductionClosureLedger_round_trip x).symm
      (Eq.trans hread (inductionClosureLedger_round_trip y)))

instance inductionClosureLedgerBHistCarrier : BHistCarrier InductionClosureLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inductionClosureLedgerToEventFlow
  fromEventFlow := inductionClosureLedgerFromEventFlow

instance inductionClosureLedgerChapterTasteGate :
    ChapterTasteGate InductionClosureLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      inductionClosureLedgerFromEventFlow (inductionClosureLedgerToEventFlow x) =
        some x
    exact inductionClosureLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (inductionClosureLedgerToEventFlow_injective heq)

theorem InductionClosureLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      inductionClosureLedgerDecodeBHist (inductionClosureLedgerEncodeBHist h) = h) ∧
      (∀ x : InductionClosureLedgerUp,
        inductionClosureLedgerFromEventFlow (inductionClosureLedgerToEventFlow x) = some x) ∧
        (∀ x y : InductionClosureLedgerUp,
          inductionClosureLedgerToEventFlow x = inductionClosureLedgerToEventFlow y → x = y) ∧
          inductionClosureLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact inductionClosureLedger_decode_encode_bhist
  · constructor
    · exact inductionClosureLedger_round_trip
    · constructor
      · intro x y heq
        exact inductionClosureLedgerToEventFlow_injective heq
      · rfl

end BEDC.Derived.InductionClosureLedgerUp
