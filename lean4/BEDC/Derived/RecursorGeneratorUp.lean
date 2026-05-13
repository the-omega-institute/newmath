import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RecursorGeneratorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

inductive RecursorGeneratorUp : Type where
  | mk :
      (signature eliminator branches audit metacic transport cont provenance name : BHist) →
      RecursorGeneratorUp
  deriving DecidableEq

def recursorGeneratorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: recursorGeneratorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: recursorGeneratorEncodeBHist h

def recursorGeneratorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (recursorGeneratorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (recursorGeneratorDecodeBHist tail)

private theorem recursorGeneratorDecode_encode_bhist :
    ∀ h : BHist, recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem RecursorGeneratorTasteGate_single_carrier_alignment_mk_congr
    {signature signature' eliminator eliminator' branches branches' audit audit'
      metacic metacic' transport transport' cont cont' provenance provenance'
      name name' : BHist}
    (hSignature : signature' = signature)
    (hEliminator : eliminator' = eliminator)
    (hBranches : branches' = branches)
    (hAudit : audit' = audit)
    (hMetaCIC : metacic' = metacic)
    (hTransport : transport' = transport)
    (hCont : cont' = cont)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    RecursorGeneratorUp.mk signature' eliminator' branches' audit' metacic' transport'
        cont' provenance' name' =
      RecursorGeneratorUp.mk signature eliminator branches audit metacic transport cont
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSignature
  cases hEliminator
  cases hBranches
  cases hAudit
  cases hMetaCIC
  cases hTransport
  cases hCont
  cases hProvenance
  cases hName
  rfl

def recursorGeneratorToEventFlow : RecursorGeneratorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RecursorGeneratorUp.mk signature eliminator branches audit metacic transport cont
      provenance name =>
      [[BMark.b0],
        recursorGeneratorEncodeBHist signature,
        [BMark.b1, BMark.b0],
        recursorGeneratorEncodeBHist eliminator,
        [BMark.b1, BMark.b1, BMark.b0],
        recursorGeneratorEncodeBHist branches,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorGeneratorEncodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorGeneratorEncodeBHist metacic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorGeneratorEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorGeneratorEncodeBHist cont,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        recursorGeneratorEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        recursorGeneratorEncodeBHist name]

def recursorGeneratorFromEventFlow : EventFlow → Option RecursorGeneratorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | signature :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | eliminator :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | branches :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | audit :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | metacic :: rest9 =>
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
                                                      | cont :: rest13 =>
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
                                                                                (RecursorGeneratorUp.mk
                                                                                  (recursorGeneratorDecodeBHist
                                                                                    signature)
                                                                                  (recursorGeneratorDecodeBHist
                                                                                    eliminator)
                                                                                  (recursorGeneratorDecodeBHist
                                                                                    branches)
                                                                                  (recursorGeneratorDecodeBHist
                                                                                    audit)
                                                                                  (recursorGeneratorDecodeBHist
                                                                                    metacic)
                                                                                  (recursorGeneratorDecodeBHist
                                                                                    transport)
                                                                                  (recursorGeneratorDecodeBHist
                                                                                    cont)
                                                                                  (recursorGeneratorDecodeBHist
                                                                                    provenance)
                                                                                  (recursorGeneratorDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem recursorGenerator_round_trip :
    ∀ x : RecursorGeneratorUp,
      recursorGeneratorFromEventFlow (recursorGeneratorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk signature eliminator branches audit metacic transport cont provenance name =>
      change
        some
          (RecursorGeneratorUp.mk
            (recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist signature))
            (recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist eliminator))
            (recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist branches))
            (recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist audit))
            (recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist metacic))
            (recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist transport))
            (recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist cont))
            (recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist provenance))
            (recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist name))) =
          some
            (RecursorGeneratorUp.mk signature eliminator branches audit metacic transport cont
              provenance name)
      exact
        congrArg some
          (RecursorGeneratorTasteGate_single_carrier_alignment_mk_congr
            (recursorGeneratorDecode_encode_bhist signature)
            (recursorGeneratorDecode_encode_bhist eliminator)
            (recursorGeneratorDecode_encode_bhist branches)
            (recursorGeneratorDecode_encode_bhist audit)
            (recursorGeneratorDecode_encode_bhist metacic)
            (recursorGeneratorDecode_encode_bhist transport)
            (recursorGeneratorDecode_encode_bhist cont)
            (recursorGeneratorDecode_encode_bhist provenance)
            (recursorGeneratorDecode_encode_bhist name))

private theorem recursorGeneratorToEventFlow_injective {x y : RecursorGeneratorUp} :
    recursorGeneratorToEventFlow x = recursorGeneratorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      recursorGeneratorFromEventFlow (recursorGeneratorToEventFlow x) =
        recursorGeneratorFromEventFlow (recursorGeneratorToEventFlow y) :=
    congrArg recursorGeneratorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (recursorGenerator_round_trip x).symm
      (Eq.trans hread (recursorGenerator_round_trip y)))

theorem RecursorGeneratorTasteGate_single_carrier_alignment :
    (forall h : BHist, recursorGeneratorDecodeBHist (recursorGeneratorEncodeBHist h) = h) /\
      (forall x : RecursorGeneratorUp,
        recursorGeneratorFromEventFlow (recursorGeneratorToEventFlow x) = some x) /\
        (forall x y : RecursorGeneratorUp,
          recursorGeneratorToEventFlow x = recursorGeneratorToEventFlow y -> x = y) /\
          recursorGeneratorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact recursorGeneratorDecode_encode_bhist
  · constructor
    · exact recursorGenerator_round_trip
    · constructor
      · intro x y heq
        exact recursorGeneratorToEventFlow_injective heq
      · rfl

end BEDC.Derived.RecursorGeneratorUp
