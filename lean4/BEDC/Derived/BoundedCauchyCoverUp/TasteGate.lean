import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedCauchyCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedCauchyCoverUp : Type where
  | mk :
      (budget modulus windows dyadic regular transport continuation provenance name : BHist) →
      BoundedCauchyCoverUp
  deriving DecidableEq

def boundedCauchyCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedCauchyCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedCauchyCoverEncodeBHist h

def boundedCauchyCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedCauchyCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedCauchyCoverDecodeBHist tail)

private theorem boundedCauchyCoverDecode_encode_bhist :
    ∀ h : BHist, boundedCauchyCoverDecodeBHist (boundedCauchyCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem boundedCauchyCover_mk_congr
    {budget budget' modulus modulus' windows windows' dyadic dyadic' regular regular'
      transport transport' continuation continuation' provenance provenance' name name' : BHist}
    (hBudget : budget' = budget)
    (hModulus : modulus' = modulus)
    (hWindows : windows' = windows)
    (hDyadic : dyadic' = dyadic)
    (hRegular : regular' = regular)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    BoundedCauchyCoverUp.mk budget' modulus' windows' dyadic' regular' transport'
        continuation' provenance' name' =
      BoundedCauchyCoverUp.mk budget modulus windows dyadic regular transport continuation
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hBudget
  cases hModulus
  cases hWindows
  cases hDyadic
  cases hRegular
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

def boundedCauchyCoverToEventFlow : BoundedCauchyCoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedCauchyCoverUp.mk budget modulus windows dyadic regular transport continuation
      provenance name =>
      [[BMark.b0],
        boundedCauchyCoverEncodeBHist budget,
        [BMark.b1, BMark.b0],
        boundedCauchyCoverEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b0],
        boundedCauchyCoverEncodeBHist windows,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedCauchyCoverEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedCauchyCoverEncodeBHist regular,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedCauchyCoverEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedCauchyCoverEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        boundedCauchyCoverEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        boundedCauchyCoverEncodeBHist name]

def boundedCauchyCoverFromEventFlow : EventFlow → Option BoundedCauchyCoverUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | budget :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | modulus :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | windows :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | dyadic :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | regular :: rest9 =>
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
                                                      | continuation :: rest13 =>
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
                                                                                (BoundedCauchyCoverUp.mk
                                                                                  (boundedCauchyCoverDecodeBHist
                                                                                    budget)
                                                                                  (boundedCauchyCoverDecodeBHist
                                                                                    modulus)
                                                                                  (boundedCauchyCoverDecodeBHist
                                                                                    windows)
                                                                                  (boundedCauchyCoverDecodeBHist
                                                                                    dyadic)
                                                                                  (boundedCauchyCoverDecodeBHist
                                                                                    regular)
                                                                                  (boundedCauchyCoverDecodeBHist
                                                                                    transport)
                                                                                  (boundedCauchyCoverDecodeBHist
                                                                                    continuation)
                                                                                  (boundedCauchyCoverDecodeBHist
                                                                                    provenance)
                                                                                  (boundedCauchyCoverDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem boundedCauchyCover_round_trip :
    ∀ x : BoundedCauchyCoverUp,
      boundedCauchyCoverFromEventFlow (boundedCauchyCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk budget modulus windows dyadic regular transport continuation provenance name =>
      change
        some
          (BoundedCauchyCoverUp.mk
            (boundedCauchyCoverDecodeBHist (boundedCauchyCoverEncodeBHist budget))
            (boundedCauchyCoverDecodeBHist (boundedCauchyCoverEncodeBHist modulus))
            (boundedCauchyCoverDecodeBHist (boundedCauchyCoverEncodeBHist windows))
            (boundedCauchyCoverDecodeBHist (boundedCauchyCoverEncodeBHist dyadic))
            (boundedCauchyCoverDecodeBHist (boundedCauchyCoverEncodeBHist regular))
            (boundedCauchyCoverDecodeBHist (boundedCauchyCoverEncodeBHist transport))
            (boundedCauchyCoverDecodeBHist (boundedCauchyCoverEncodeBHist continuation))
            (boundedCauchyCoverDecodeBHist (boundedCauchyCoverEncodeBHist provenance))
            (boundedCauchyCoverDecodeBHist (boundedCauchyCoverEncodeBHist name))) =
          some
            (BoundedCauchyCoverUp.mk budget modulus windows dyadic regular transport
              continuation provenance name)
      exact
        congrArg some
          (boundedCauchyCover_mk_congr
            (boundedCauchyCoverDecode_encode_bhist budget)
            (boundedCauchyCoverDecode_encode_bhist modulus)
            (boundedCauchyCoverDecode_encode_bhist windows)
            (boundedCauchyCoverDecode_encode_bhist dyadic)
            (boundedCauchyCoverDecode_encode_bhist regular)
            (boundedCauchyCoverDecode_encode_bhist transport)
            (boundedCauchyCoverDecode_encode_bhist continuation)
            (boundedCauchyCoverDecode_encode_bhist provenance)
            (boundedCauchyCoverDecode_encode_bhist name))

private theorem boundedCauchyCoverToEventFlow_injective {x y : BoundedCauchyCoverUp} :
    boundedCauchyCoverToEventFlow x = boundedCauchyCoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedCauchyCoverFromEventFlow (boundedCauchyCoverToEventFlow x) =
        boundedCauchyCoverFromEventFlow (boundedCauchyCoverToEventFlow y) :=
    congrArg boundedCauchyCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (boundedCauchyCover_round_trip x).symm
      (Eq.trans hread (boundedCauchyCover_round_trip y)))

instance boundedCauchyCoverBHistCarrier : BHistCarrier BoundedCauchyCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedCauchyCoverToEventFlow
  fromEventFlow := boundedCauchyCoverFromEventFlow

instance boundedCauchyCoverChapterTasteGate : ChapterTasteGate BoundedCauchyCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedCauchyCoverFromEventFlow (boundedCauchyCoverToEventFlow x) = some x
    exact boundedCauchyCover_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedCauchyCoverToEventFlow_injective heq)

theorem BoundedCauchyCoverTasteGate_single_carrier_alignment :
    (∀ h : BHist, boundedCauchyCoverDecodeBHist (boundedCauchyCoverEncodeBHist h) = h) ∧
      (∀ x : BoundedCauchyCoverUp,
        boundedCauchyCoverFromEventFlow (boundedCauchyCoverToEventFlow x) = some x) ∧
        (∀ x y : BoundedCauchyCoverUp,
          boundedCauchyCoverToEventFlow x = boundedCauchyCoverToEventFlow y → x = y) ∧
          boundedCauchyCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact boundedCauchyCoverDecode_encode_bhist
  · constructor
    · exact boundedCauchyCover_round_trip
    · constructor
      · intro x y heq
        exact boundedCauchyCoverToEventFlow_injective heq
      · rfl

end BEDC.Derived.BoundedCauchyCoverUp
