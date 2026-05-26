import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCancellationUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCancellationUp : Type where
  | mk :
      (sourceX sourceY shared sumX sumY difference budget zeroBoundary readback realSeal
        transport replay provenance name : BHist) →
      RegularCauchyCancellationUp
  deriving DecidableEq

def regularCauchyCancellationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCancellationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCancellationEncodeBHist h

def regularCauchyCancellationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCancellationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCancellationDecodeBHist tail)

theorem RegularCauchyCancellationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyCancellationDecodeBHist (regularCauchyCancellationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyCancellationFields : RegularCauchyCancellationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCancellationUp.mk sourceX sourceY shared sumX sumY difference budget
      zeroBoundary readback realSeal transport replay provenance name =>
      [sourceX, sourceY, shared, sumX, sumY, difference, budget, zeroBoundary, readback,
        realSeal, transport, replay, provenance, name]

def regularCauchyCancellationToEventFlow : RegularCauchyCancellationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCancellationUp.mk sourceX sourceY shared sumX sumY difference budget
      zeroBoundary readback realSeal transport replay provenance name =>
      [[BMark.b0],
        regularCauchyCancellationEncodeBHist sourceX,
        [BMark.b1, BMark.b0],
        regularCauchyCancellationEncodeBHist sourceY,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCancellationEncodeBHist shared,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCancellationEncodeBHist sumX,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCancellationEncodeBHist sumY,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCancellationEncodeBHist difference,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCancellationEncodeBHist budget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyCancellationEncodeBHist zeroBoundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyCancellationEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCancellationEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCancellationEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCancellationEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCancellationEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCancellationEncodeBHist name]

def regularCauchyCancellationFromEventFlow : EventFlow → Option RegularCauchyCancellationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | sourceX :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | sourceY :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | shared :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | sumX :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | sumY :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | difference :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | budget :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | zeroBoundary :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | readback :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | realSeal :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | transport :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | replay :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] => none
                                                                                                  | _tag12 :: rest24 =>
                                                                                                      match rest24 with
                                                                                                      | [] => none
                                                                                                      | provenance :: rest25 =>
                                                                                                          match rest25 with
                                                                                                          | [] => none
                                                                                                          | _tag13 :: rest26 =>
                                                                                                              match rest26 with
                                                                                                              | [] => none
                                                                                                              | name :: rest27 =>
                                                                                                                  match rest27 with
                                                                                                                  | [] =>
                                                                                                                      some
                                                                                                                        (RegularCauchyCancellationUp.mk
                                                                                                                          (regularCauchyCancellationDecodeBHist
                                                                                                                            sourceX)
                                                                                                                          (regularCauchyCancellationDecodeBHist
                                                                                                                            sourceY)
                                                                                                                          (regularCauchyCancellationDecodeBHist
                                                                                                                            shared)
                                                                                                                          (regularCauchyCancellationDecodeBHist
                                                                                                                            sumX)
                                                                                                                          (regularCauchyCancellationDecodeBHist
                                                                                                                            sumY)
                                                                                                                          (regularCauchyCancellationDecodeBHist
                                                                                                                            difference)
                                                                                                                          (regularCauchyCancellationDecodeBHist
                                                                                                                            budget)
                                                                                                                          (regularCauchyCancellationDecodeBHist
                                                                                                                            zeroBoundary)
                                                                                                                          (regularCauchyCancellationDecodeBHist
                                                                                                                            readback)
                                                                                                                          (regularCauchyCancellationDecodeBHist
                                                                                                                            realSeal)
                                                                                                                          (regularCauchyCancellationDecodeBHist
                                                                                                                            transport)
                                                                                                                          (regularCauchyCancellationDecodeBHist
                                                                                                                            replay)
                                                                                                                          (regularCauchyCancellationDecodeBHist
                                                                                                                            provenance)
                                                                                                                          (regularCauchyCancellationDecodeBHist
                                                                                                                            name))
                                                                                                                  | _ :: _ => none

private theorem regularCauchyCancellation_mk_congr
    {sourceX sourceX' sourceY sourceY' shared shared' sumX sumX' sumY sumY'
      difference difference' budget budget' zeroBoundary zeroBoundary' readback readback'
      realSeal realSeal' transport transport' replay replay' provenance provenance'
      name name' : BHist}
    (hSourceX : sourceX' = sourceX)
    (hSourceY : sourceY' = sourceY)
    (hShared : shared' = shared)
    (hSumX : sumX' = sumX)
    (hSumY : sumY' = sumY)
    (hDifference : difference' = difference)
    (hBudget : budget' = budget)
    (hZeroBoundary : zeroBoundary' = zeroBoundary)
    (hReadback : readback' = readback)
    (hRealSeal : realSeal' = realSeal)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    RegularCauchyCancellationUp.mk sourceX' sourceY' shared' sumX' sumY' difference'
        budget' zeroBoundary' readback' realSeal' transport' replay' provenance' name' =
      RegularCauchyCancellationUp.mk sourceX sourceY shared sumX sumY difference budget
        zeroBoundary readback realSeal transport replay provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSourceX
  cases hSourceY
  cases hShared
  cases hSumX
  cases hSumY
  cases hDifference
  cases hBudget
  cases hZeroBoundary
  cases hReadback
  cases hRealSeal
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

theorem RegularCauchyCancellationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyCancellationUp,
      regularCauchyCancellationFromEventFlow (regularCauchyCancellationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceX sourceY shared sumX sumY difference budget zeroBoundary readback realSeal
      transport replay provenance name =>
      change
        some
          (RegularCauchyCancellationUp.mk
            (regularCauchyCancellationDecodeBHist
              (regularCauchyCancellationEncodeBHist sourceX))
            (regularCauchyCancellationDecodeBHist
              (regularCauchyCancellationEncodeBHist sourceY))
            (regularCauchyCancellationDecodeBHist
              (regularCauchyCancellationEncodeBHist shared))
            (regularCauchyCancellationDecodeBHist
              (regularCauchyCancellationEncodeBHist sumX))
            (regularCauchyCancellationDecodeBHist
              (regularCauchyCancellationEncodeBHist sumY))
            (regularCauchyCancellationDecodeBHist
              (regularCauchyCancellationEncodeBHist difference))
            (regularCauchyCancellationDecodeBHist
              (regularCauchyCancellationEncodeBHist budget))
            (regularCauchyCancellationDecodeBHist
              (regularCauchyCancellationEncodeBHist zeroBoundary))
            (regularCauchyCancellationDecodeBHist
              (regularCauchyCancellationEncodeBHist readback))
            (regularCauchyCancellationDecodeBHist
              (regularCauchyCancellationEncodeBHist realSeal))
            (regularCauchyCancellationDecodeBHist
              (regularCauchyCancellationEncodeBHist transport))
            (regularCauchyCancellationDecodeBHist
              (regularCauchyCancellationEncodeBHist replay))
            (regularCauchyCancellationDecodeBHist
              (regularCauchyCancellationEncodeBHist provenance))
            (regularCauchyCancellationDecodeBHist
              (regularCauchyCancellationEncodeBHist name))) =
          some
            (RegularCauchyCancellationUp.mk sourceX sourceY shared sumX sumY difference
              budget zeroBoundary readback realSeal transport replay provenance name)
      exact
        congrArg some
          (regularCauchyCancellation_mk_congr
            (RegularCauchyCancellationTasteGate_single_carrier_alignment_decode_encode sourceX)
            (RegularCauchyCancellationTasteGate_single_carrier_alignment_decode_encode sourceY)
            (RegularCauchyCancellationTasteGate_single_carrier_alignment_decode_encode shared)
            (RegularCauchyCancellationTasteGate_single_carrier_alignment_decode_encode sumX)
            (RegularCauchyCancellationTasteGate_single_carrier_alignment_decode_encode sumY)
            (RegularCauchyCancellationTasteGate_single_carrier_alignment_decode_encode difference)
            (RegularCauchyCancellationTasteGate_single_carrier_alignment_decode_encode budget)
            (RegularCauchyCancellationTasteGate_single_carrier_alignment_decode_encode
              zeroBoundary)
            (RegularCauchyCancellationTasteGate_single_carrier_alignment_decode_encode readback)
            (RegularCauchyCancellationTasteGate_single_carrier_alignment_decode_encode realSeal)
            (RegularCauchyCancellationTasteGate_single_carrier_alignment_decode_encode transport)
            (RegularCauchyCancellationTasteGate_single_carrier_alignment_decode_encode replay)
            (RegularCauchyCancellationTasteGate_single_carrier_alignment_decode_encode
              provenance)
            (RegularCauchyCancellationTasteGate_single_carrier_alignment_decode_encode name))

theorem RegularCauchyCancellationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyCancellationUp} :
    regularCauchyCancellationToEventFlow x = regularCauchyCancellationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCancellationFromEventFlow (regularCauchyCancellationToEventFlow x) =
        regularCauchyCancellationFromEventFlow (regularCauchyCancellationToEventFlow y) :=
    congrArg regularCauchyCancellationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyCancellationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyCancellationTasteGate_single_carrier_alignment_round_trip y)))

theorem RegularCauchyCancellationTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RegularCauchyCancellationUp,
      regularCauchyCancellationFields x = regularCauchyCancellationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk sourceX₁ sourceY₁ shared₁ sumX₁ sumY₁ difference₁ budget₁ zeroBoundary₁
      readback₁ realSeal₁ transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk sourceX₂ sourceY₂ shared₂ sumX₂ sumY₂ difference₂ budget₂ zeroBoundary₂
          readback₂ realSeal₂ transport₂ replay₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance regularCauchyCancellationBHistCarrier : BHistCarrier RegularCauchyCancellationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCancellationToEventFlow
  fromEventFlow := regularCauchyCancellationFromEventFlow

instance regularCauchyCancellationChapterTasteGate :
    ChapterTasteGate RegularCauchyCancellationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCancellationFromEventFlow (regularCauchyCancellationToEventFlow x) =
        some x
    exact RegularCauchyCancellationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyCancellationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyCancellationFieldFaithful :
    FieldFaithful RegularCauchyCancellationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyCancellationFields
  field_faithful := RegularCauchyCancellationTasteGate_single_carrier_alignment_field_faithful

instance regularCauchyCancellationNontrivial :
    Nontrivial RegularCauchyCancellationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyCancellationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyCancellationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyCancellationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyCancellationUp) ∧
      Nonempty (FieldFaithful RegularCauchyCancellationUp) ∧
        Nonempty (Nontrivial RegularCauchyCancellationUp) ∧
          (∀ h : BHist,
            regularCauchyCancellationDecodeBHist
                (regularCauchyCancellationEncodeBHist h) =
              h) ∧
            (∀ x : RegularCauchyCancellationUp,
              regularCauchyCancellationFromEventFlow
                  (regularCauchyCancellationToEventFlow x) =
                some x) ∧
              (∀ x y : RegularCauchyCancellationUp,
                regularCauchyCancellationToEventFlow x =
                    regularCauchyCancellationToEventFlow y →
                  x = y) ∧
                regularCauchyCancellationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨regularCauchyCancellationChapterTasteGate⟩,
      ⟨regularCauchyCancellationFieldFaithful⟩,
      ⟨regularCauchyCancellationNontrivial⟩,
      RegularCauchyCancellationTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchyCancellationTasteGate_single_carrier_alignment_round_trip,
      (by
        intro x y heq
        exact
          RegularCauchyCancellationTasteGate_single_carrier_alignment_toEventFlow_injective
            heq),
      rfl⟩

end BEDC.Derived.RegularCauchyCancellationUp.TasteGate
