import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailBudgetUp : Type where
  | mk :
      (source threshold budget windows dyadic readback sealRow transport route provenance
        name : BHist) →
      RegularCauchyTailBudgetUp
  deriving DecidableEq

def regularCauchyTailBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailBudgetEncodeBHist h

def regularCauchyTailBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailBudgetDecodeBHist tail)

private theorem regularCauchyTailBudget_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyTailBudgetDecodeBHist
        (regularCauchyTailBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem regularCauchyTailBudget_mk_congr
    {source source' threshold threshold' budget budget' windows windows' dyadic dyadic'
      readback readback' sealRow sealRow' transport transport' route route' provenance provenance'
      name name' : BHist}
    (hSource : source' = source)
    (hThreshold : threshold' = threshold)
    (hBudget : budget' = budget)
    (hWindows : windows' = windows)
    (hDyadic : dyadic' = dyadic)
    (hReadback : readback' = readback)
    (hSeal : sealRow' = sealRow)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    RegularCauchyTailBudgetUp.mk source' threshold' budget' windows' dyadic' readback' sealRow'
        transport' route' provenance' name' =
      RegularCauchyTailBudgetUp.mk source threshold budget windows dyadic readback sealRow
        transport route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hThreshold
  cases hBudget
  cases hWindows
  cases hDyadic
  cases hReadback
  cases hSeal
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def regularCauchyTailBudgetToEventFlow : RegularCauchyTailBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailBudgetUp.mk source threshold budget windows dyadic readback sealRow transport
      route provenance name =>
      [[BMark.b0],
        regularCauchyTailBudgetEncodeBHist source,
        [BMark.b1, BMark.b0],
        regularCauchyTailBudgetEncodeBHist threshold,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailBudgetEncodeBHist budget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailBudgetEncodeBHist windows,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailBudgetEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailBudgetEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailBudgetEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyTailBudgetEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyTailBudgetEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailBudgetEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailBudgetEncodeBHist name]

def regularCauchyTailBudgetFromEventFlow : EventFlow → Option RegularCauchyTailBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | threshold :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | budget :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | windows :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | dyadic :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | readback :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | sealRow :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | route :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | name :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (RegularCauchyTailBudgetUp.mk
                                                                                                  (regularCauchyTailBudgetDecodeBHist source)
                                                                                                  (regularCauchyTailBudgetDecodeBHist threshold)
                                                                                                  (regularCauchyTailBudgetDecodeBHist budget)
                                                                                                  (regularCauchyTailBudgetDecodeBHist windows)
                                                                                                  (regularCauchyTailBudgetDecodeBHist dyadic)
                                                                                                  (regularCauchyTailBudgetDecodeBHist readback)
                                                                                                  (regularCauchyTailBudgetDecodeBHist sealRow)
                                                                                                  (regularCauchyTailBudgetDecodeBHist transport)
                                                                                                  (regularCauchyTailBudgetDecodeBHist route)
                                                                                                  (regularCauchyTailBudgetDecodeBHist provenance)
                                                                                                  (regularCauchyTailBudgetDecodeBHist name))
                                                                                          | _ :: _ => none

private theorem regularCauchyTailBudget_round_trip :
    ∀ x : RegularCauchyTailBudgetUp,
      regularCauchyTailBudgetFromEventFlow
        (regularCauchyTailBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source threshold budget windows dyadic readback sealRow transport route provenance name =>
      change
        some
          (RegularCauchyTailBudgetUp.mk
            (regularCauchyTailBudgetDecodeBHist
              (regularCauchyTailBudgetEncodeBHist source))
            (regularCauchyTailBudgetDecodeBHist
              (regularCauchyTailBudgetEncodeBHist threshold))
            (regularCauchyTailBudgetDecodeBHist
              (regularCauchyTailBudgetEncodeBHist budget))
            (regularCauchyTailBudgetDecodeBHist
              (regularCauchyTailBudgetEncodeBHist windows))
            (regularCauchyTailBudgetDecodeBHist
              (regularCauchyTailBudgetEncodeBHist dyadic))
            (regularCauchyTailBudgetDecodeBHist
              (regularCauchyTailBudgetEncodeBHist readback))
            (regularCauchyTailBudgetDecodeBHist
              (regularCauchyTailBudgetEncodeBHist sealRow))
            (regularCauchyTailBudgetDecodeBHist
              (regularCauchyTailBudgetEncodeBHist transport))
            (regularCauchyTailBudgetDecodeBHist
              (regularCauchyTailBudgetEncodeBHist route))
            (regularCauchyTailBudgetDecodeBHist
              (regularCauchyTailBudgetEncodeBHist provenance))
            (regularCauchyTailBudgetDecodeBHist
              (regularCauchyTailBudgetEncodeBHist name))) =
          some
            (RegularCauchyTailBudgetUp.mk source threshold budget windows dyadic readback
              sealRow transport route provenance name)
      exact
        congrArg some
          (regularCauchyTailBudget_mk_congr
            (regularCauchyTailBudget_decode_encode_bhist source)
            (regularCauchyTailBudget_decode_encode_bhist threshold)
            (regularCauchyTailBudget_decode_encode_bhist budget)
            (regularCauchyTailBudget_decode_encode_bhist windows)
            (regularCauchyTailBudget_decode_encode_bhist dyadic)
            (regularCauchyTailBudget_decode_encode_bhist readback)
            (regularCauchyTailBudget_decode_encode_bhist sealRow)
            (regularCauchyTailBudget_decode_encode_bhist transport)
            (regularCauchyTailBudget_decode_encode_bhist route)
            (regularCauchyTailBudget_decode_encode_bhist provenance)
            (regularCauchyTailBudget_decode_encode_bhist name))

private theorem regularCauchyTailBudgetToEventFlow_injective
    {x y : RegularCauchyTailBudgetUp} :
    regularCauchyTailBudgetToEventFlow x =
      regularCauchyTailBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailBudgetFromEventFlow
          (regularCauchyTailBudgetToEventFlow x) =
        regularCauchyTailBudgetFromEventFlow
          (regularCauchyTailBudgetToEventFlow y) :=
    congrArg regularCauchyTailBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTailBudget_round_trip x).symm
      (Eq.trans hread (regularCauchyTailBudget_round_trip y)))

instance regularCauchyTailBudgetBHistCarrier :
    BHistCarrier RegularCauchyTailBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailBudgetToEventFlow
  fromEventFlow := regularCauchyTailBudgetFromEventFlow

instance regularCauchyTailBudgetChapterTasteGate :
    ChapterTasteGate RegularCauchyTailBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailBudgetFromEventFlow
        (regularCauchyTailBudgetToEventFlow x) = some x
    exact regularCauchyTailBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailBudgetToEventFlow_injective heq)

instance regularCauchyTailBudgetFieldFaithful :
    FieldFaithful RegularCauchyTailBudgetUp where
  fields
    | RegularCauchyTailBudgetUp.mk source threshold budget windows dyadic readback sealRow
        transport route provenance name =>
        [source, threshold, budget, windows, dyadic, readback, sealRow, transport, route,
          provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y hfields
    cases x with
    | mk source threshold budget windows dyadic readback sealRow transport route provenance name =>
        cases y with
        | mk source' threshold' budget' windows' dyadic' readback' sealRow' transport' route'
            provenance' name' =>
            cases hfields
            rfl

instance regularCauchyTailBudgetNontrivial :
    Nontrivial RegularCauchyTailBudgetUp where
  witness_pair :=
    -- BEDC touchpoint anchor: BHist BMark
    ⟨RegularCauchyTailBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyTailBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyTailBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem RegularCauchyTailBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyTailBudgetDecodeBHist
        (regularCauchyTailBudgetEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyTailBudgetUp,
        regularCauchyTailBudgetFromEventFlow
          (regularCauchyTailBudgetToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyTailBudgetUp,
          regularCauchyTailBudgetToEventFlow x =
            regularCauchyTailBudgetToEventFlow y → x = y) ∧
          regularCauchyTailBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyTailBudget_decode_encode_bhist
  · constructor
    · exact regularCauchyTailBudget_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyTailBudgetToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyTailBudgetUp
