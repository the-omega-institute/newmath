import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySwapBisimulationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySwapBisimulationUp : Type where
  | mk :
      (leftSource rightSource leftSchedule rightSchedule selector oppositeSelector
        commonLedger forwardSeal oppositeSeal transport continuation provenance name : BHist) →
      RegularCauchySwapBisimulationUp
  deriving DecidableEq

private def regularCauchySwapBisimulationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySwapBisimulationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySwapBisimulationEncodeBHist h

private def regularCauchySwapBisimulationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySwapBisimulationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySwapBisimulationDecodeBHist tail)

private theorem regularCauchySwapBisimulationDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchySwapBisimulationDecodeBHist
        (regularCauchySwapBisimulationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem regularCauchySwapBisimulation_mk_congr
    {leftSource leftSource' rightSource rightSource' leftSchedule leftSchedule'
      rightSchedule rightSchedule' selector selector' oppositeSelector oppositeSelector'
      commonLedger commonLedger' forwardSeal forwardSeal' oppositeSeal oppositeSeal'
      transport transport' continuation continuation' provenance provenance' name name' : BHist}
    (hLeftSource : leftSource' = leftSource)
    (hRightSource : rightSource' = rightSource)
    (hLeftSchedule : leftSchedule' = leftSchedule)
    (hRightSchedule : rightSchedule' = rightSchedule)
    (hSelector : selector' = selector)
    (hOppositeSelector : oppositeSelector' = oppositeSelector)
    (hCommonLedger : commonLedger' = commonLedger)
    (hForwardSeal : forwardSeal' = forwardSeal)
    (hOppositeSeal : oppositeSeal' = oppositeSeal)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    RegularCauchySwapBisimulationUp.mk leftSource' rightSource' leftSchedule'
        rightSchedule' selector' oppositeSelector' commonLedger' forwardSeal' oppositeSeal'
        transport' continuation' provenance' name' =
      RegularCauchySwapBisimulationUp.mk leftSource rightSource leftSchedule rightSchedule
        selector oppositeSelector commonLedger forwardSeal oppositeSeal transport continuation
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hLeftSource
  cases hRightSource
  cases hLeftSchedule
  cases hRightSchedule
  cases hSelector
  cases hOppositeSelector
  cases hCommonLedger
  cases hForwardSeal
  cases hOppositeSeal
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

private def regularCauchySwapBisimulationToEventFlow :
    RegularCauchySwapBisimulationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySwapBisimulationUp.mk leftSource rightSource leftSchedule rightSchedule
      selector oppositeSelector commonLedger forwardSeal oppositeSeal transport continuation
      provenance name =>
      [[BMark.b0],
        regularCauchySwapBisimulationEncodeBHist leftSource,
        [BMark.b1, BMark.b0],
        regularCauchySwapBisimulationEncodeBHist rightSource,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchySwapBisimulationEncodeBHist leftSchedule,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySwapBisimulationEncodeBHist rightSchedule,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySwapBisimulationEncodeBHist selector,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySwapBisimulationEncodeBHist oppositeSelector,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySwapBisimulationEncodeBHist commonLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchySwapBisimulationEncodeBHist forwardSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchySwapBisimulationEncodeBHist oppositeSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchySwapBisimulationEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySwapBisimulationEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySwapBisimulationEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySwapBisimulationEncodeBHist name]

private def regularCauchySwapBisimulationFromEventFlow :
    EventFlow → Option RegularCauchySwapBisimulationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | leftSource :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | rightSource :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | leftSchedule :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | rightSchedule :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | selector :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | oppositeSelector :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | commonLedger :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | forwardSeal :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | oppositeSeal :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | transport :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | continuation :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | provenance :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] => none
                                                                                                  | _tag12 :: rest24 =>
                                                                                                      match rest24 with
                                                                                                      | [] => none
                                                                                                      | name :: rest25 =>
                                                                                                          match rest25 with
                                                                                                          | [] =>
                                                                                                              some
                                                                                                                (RegularCauchySwapBisimulationUp.mk
                                                                                                                  (regularCauchySwapBisimulationDecodeBHist leftSource)
                                                                                                                  (regularCauchySwapBisimulationDecodeBHist rightSource)
                                                                                                                  (regularCauchySwapBisimulationDecodeBHist leftSchedule)
                                                                                                                  (regularCauchySwapBisimulationDecodeBHist rightSchedule)
                                                                                                                  (regularCauchySwapBisimulationDecodeBHist selector)
                                                                                                                  (regularCauchySwapBisimulationDecodeBHist oppositeSelector)
                                                                                                                  (regularCauchySwapBisimulationDecodeBHist commonLedger)
                                                                                                                  (regularCauchySwapBisimulationDecodeBHist forwardSeal)
                                                                                                                  (regularCauchySwapBisimulationDecodeBHist oppositeSeal)
                                                                                                                  (regularCauchySwapBisimulationDecodeBHist transport)
                                                                                                                  (regularCauchySwapBisimulationDecodeBHist continuation)
                                                                                                                  (regularCauchySwapBisimulationDecodeBHist provenance)
                                                                                                                  (regularCauchySwapBisimulationDecodeBHist name))
                                                                                                          | _ :: _ => none

private theorem regularCauchySwapBisimulation_round_trip :
    ∀ x : RegularCauchySwapBisimulationUp,
      regularCauchySwapBisimulationFromEventFlow
        (regularCauchySwapBisimulationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk leftSource rightSource leftSchedule rightSchedule selector oppositeSelector
      commonLedger forwardSeal oppositeSeal transport continuation provenance name =>
      change
        some
          (RegularCauchySwapBisimulationUp.mk
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist leftSource))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist rightSource))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist leftSchedule))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist rightSchedule))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist selector))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist oppositeSelector))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist commonLedger))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist forwardSeal))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist oppositeSeal))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist transport))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist continuation))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist provenance))
            (regularCauchySwapBisimulationDecodeBHist
              (regularCauchySwapBisimulationEncodeBHist name))) =
          some
            (RegularCauchySwapBisimulationUp.mk leftSource rightSource leftSchedule
              rightSchedule selector oppositeSelector commonLedger forwardSeal oppositeSeal
              transport continuation provenance name)
      exact
        congrArg some
          (regularCauchySwapBisimulation_mk_congr
            (regularCauchySwapBisimulationDecode_encode_bhist leftSource)
            (regularCauchySwapBisimulationDecode_encode_bhist rightSource)
            (regularCauchySwapBisimulationDecode_encode_bhist leftSchedule)
            (regularCauchySwapBisimulationDecode_encode_bhist rightSchedule)
            (regularCauchySwapBisimulationDecode_encode_bhist selector)
            (regularCauchySwapBisimulationDecode_encode_bhist oppositeSelector)
            (regularCauchySwapBisimulationDecode_encode_bhist commonLedger)
            (regularCauchySwapBisimulationDecode_encode_bhist forwardSeal)
            (regularCauchySwapBisimulationDecode_encode_bhist oppositeSeal)
            (regularCauchySwapBisimulationDecode_encode_bhist transport)
            (regularCauchySwapBisimulationDecode_encode_bhist continuation)
            (regularCauchySwapBisimulationDecode_encode_bhist provenance)
            (regularCauchySwapBisimulationDecode_encode_bhist name))

private theorem regularCauchySwapBisimulationToEventFlow_injective
    {x y : RegularCauchySwapBisimulationUp} :
    regularCauchySwapBisimulationToEventFlow x =
      regularCauchySwapBisimulationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySwapBisimulationFromEventFlow
          (regularCauchySwapBisimulationToEventFlow x) =
        regularCauchySwapBisimulationFromEventFlow
          (regularCauchySwapBisimulationToEventFlow y) :=
    congrArg regularCauchySwapBisimulationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchySwapBisimulation_round_trip x).symm
      (Eq.trans hread (regularCauchySwapBisimulation_round_trip y)))

instance regularCauchySwapBisimulationBHistCarrier :
    BHistCarrier RegularCauchySwapBisimulationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySwapBisimulationToEventFlow
  fromEventFlow := regularCauchySwapBisimulationFromEventFlow

instance regularCauchySwapBisimulationChapterTasteGate :
    ChapterTasteGate RegularCauchySwapBisimulationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySwapBisimulationFromEventFlow
        (regularCauchySwapBisimulationToEventFlow x) = some x
    exact regularCauchySwapBisimulation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySwapBisimulationToEventFlow_injective heq)

theorem RegularCauchySwapBisimulationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchySwapBisimulationDecodeBHist
        (regularCauchySwapBisimulationEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySwapBisimulationUp,
        regularCauchySwapBisimulationFromEventFlow
          (regularCauchySwapBisimulationToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchySwapBisimulationUp,
          regularCauchySwapBisimulationToEventFlow x =
            regularCauchySwapBisimulationToEventFlow y → x = y) ∧
          regularCauchySwapBisimulationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchySwapBisimulationDecode_encode_bhist
  · constructor
    · exact regularCauchySwapBisimulation_round_trip
    · constructor
      · intro x y heq
        exact regularCauchySwapBisimulationToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchySwapBisimulationUp
