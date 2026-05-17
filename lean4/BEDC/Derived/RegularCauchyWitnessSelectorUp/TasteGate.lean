import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyWitnessSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyWitnessSelectorUp : Type where
  | mk :
      (modulusRequest selectedWindow tolerance readback sealRow transport route provenance
        name : BHist) →
        RegularCauchyWitnessSelectorUp
  deriving DecidableEq

def regularCauchyWitnessSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyWitnessSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyWitnessSelectorEncodeBHist h

def regularCauchyWitnessSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyWitnessSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyWitnessSelectorDecodeBHist tail)

private theorem regularCauchyWitnessSelectorDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyWitnessSelectorDecodeBHist
        (regularCauchyWitnessSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyWitnessSelectorToEventFlow :
    RegularCauchyWitnessSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyWitnessSelectorUp.mk modulusRequest selectedWindow tolerance readback sealRow
      transport route provenance name =>
      [regularCauchyWitnessSelectorEncodeBHist modulusRequest,
        regularCauchyWitnessSelectorEncodeBHist selectedWindow,
        regularCauchyWitnessSelectorEncodeBHist tolerance,
        regularCauchyWitnessSelectorEncodeBHist readback,
        regularCauchyWitnessSelectorEncodeBHist sealRow,
        regularCauchyWitnessSelectorEncodeBHist transport,
        regularCauchyWitnessSelectorEncodeBHist route,
        regularCauchyWitnessSelectorEncodeBHist provenance,
        regularCauchyWitnessSelectorEncodeBHist name]

def regularCauchyWitnessSelectorFromEventFlow :
    EventFlow → Option RegularCauchyWitnessSelectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | modulusRequest :: rest0 =>
      match rest0 with
      | [] => none
      | selectedWindow :: rest1 =>
          match rest1 with
          | [] => none
          | tolerance :: rest2 =>
              match rest2 with
              | [] => none
              | readback :: rest3 =>
                  match rest3 with
                  | [] => none
                  | sealRow :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | route :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | name :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (RegularCauchyWitnessSelectorUp.mk
                                              (regularCauchyWitnessSelectorDecodeBHist
                                                modulusRequest)
                                              (regularCauchyWitnessSelectorDecodeBHist
                                                selectedWindow)
                                              (regularCauchyWitnessSelectorDecodeBHist tolerance)
                                              (regularCauchyWitnessSelectorDecodeBHist readback)
                                              (regularCauchyWitnessSelectorDecodeBHist sealRow)
                                              (regularCauchyWitnessSelectorDecodeBHist transport)
                                              (regularCauchyWitnessSelectorDecodeBHist route)
                                              (regularCauchyWitnessSelectorDecodeBHist provenance)
                                              (regularCauchyWitnessSelectorDecodeBHist name))
                                      | _ :: _ => none

private theorem regularCauchyWitnessSelector_round_trip :
    ∀ x : RegularCauchyWitnessSelectorUp,
      regularCauchyWitnessSelectorFromEventFlow
        (regularCauchyWitnessSelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk modulusRequest selectedWindow tolerance readback sealRow transport route provenance name =>
      change
        some
          (RegularCauchyWitnessSelectorUp.mk
            (regularCauchyWitnessSelectorDecodeBHist
              (regularCauchyWitnessSelectorEncodeBHist modulusRequest))
            (regularCauchyWitnessSelectorDecodeBHist
              (regularCauchyWitnessSelectorEncodeBHist selectedWindow))
            (regularCauchyWitnessSelectorDecodeBHist
              (regularCauchyWitnessSelectorEncodeBHist tolerance))
            (regularCauchyWitnessSelectorDecodeBHist
              (regularCauchyWitnessSelectorEncodeBHist readback))
            (regularCauchyWitnessSelectorDecodeBHist
              (regularCauchyWitnessSelectorEncodeBHist sealRow))
            (regularCauchyWitnessSelectorDecodeBHist
              (regularCauchyWitnessSelectorEncodeBHist transport))
            (regularCauchyWitnessSelectorDecodeBHist
              (regularCauchyWitnessSelectorEncodeBHist route))
            (regularCauchyWitnessSelectorDecodeBHist
              (regularCauchyWitnessSelectorEncodeBHist provenance))
            (regularCauchyWitnessSelectorDecodeBHist
              (regularCauchyWitnessSelectorEncodeBHist name))) =
          some
            (RegularCauchyWitnessSelectorUp.mk modulusRequest selectedWindow tolerance readback
              sealRow transport route provenance name)
      rw [regularCauchyWitnessSelectorDecode_encode_bhist modulusRequest,
        regularCauchyWitnessSelectorDecode_encode_bhist selectedWindow,
        regularCauchyWitnessSelectorDecode_encode_bhist tolerance,
        regularCauchyWitnessSelectorDecode_encode_bhist readback,
        regularCauchyWitnessSelectorDecode_encode_bhist sealRow,
        regularCauchyWitnessSelectorDecode_encode_bhist transport,
        regularCauchyWitnessSelectorDecode_encode_bhist route,
        regularCauchyWitnessSelectorDecode_encode_bhist provenance,
        regularCauchyWitnessSelectorDecode_encode_bhist name]

private theorem regularCauchyWitnessSelectorToEventFlow_injective
    {x y : RegularCauchyWitnessSelectorUp} :
    regularCauchyWitnessSelectorToEventFlow x =
      regularCauchyWitnessSelectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyWitnessSelectorFromEventFlow
          (regularCauchyWitnessSelectorToEventFlow x) =
        regularCauchyWitnessSelectorFromEventFlow
          (regularCauchyWitnessSelectorToEventFlow y) :=
    congrArg regularCauchyWitnessSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyWitnessSelector_round_trip x).symm
      (Eq.trans hread (regularCauchyWitnessSelector_round_trip y)))

instance regularCauchyWitnessSelectorBHistCarrier :
    BHistCarrier RegularCauchyWitnessSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyWitnessSelectorToEventFlow
  fromEventFlow := regularCauchyWitnessSelectorFromEventFlow

instance regularCauchyWitnessSelectorChapterTasteGate :
    ChapterTasteGate RegularCauchyWitnessSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyWitnessSelectorFromEventFlow
        (regularCauchyWitnessSelectorToEventFlow x) = some x
    exact regularCauchyWitnessSelector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyWitnessSelectorToEventFlow_injective heq)

instance regularCauchyWitnessSelectorFieldFaithful :
    FieldFaithful RegularCauchyWitnessSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | RegularCauchyWitnessSelectorUp.mk modulusRequest selectedWindow tolerance readback sealRow
        transport route provenance name =>
        [modulusRequest, selectedWindow, tolerance, readback, sealRow, transport, route,
          provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk modulusRequest₁ selectedWindow₁ tolerance₁ readback₁ sealRow₁ transport₁ route₁
        provenance₁ name₁ =>
        cases y with
        | mk modulusRequest₂ selectedWindow₂ tolerance₂ readback₂ sealRow₂ transport₂ route₂
            provenance₂ name₂ =>
            simp only [] at h
            cases h
            rfl

instance regularCauchyWitnessSelectorNontrivial :
    Nontrivial RegularCauchyWitnessSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyWitnessSelectorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyWitnessSelectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyWitnessSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyWitnessSelectorChapterTasteGate

theorem RegularCauchyWitnessSelectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        regularCauchyWitnessSelectorDecodeBHist
          (regularCauchyWitnessSelectorEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyWitnessSelectorUp,
        regularCauchyWitnessSelectorFromEventFlow
          (regularCauchyWitnessSelectorToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyWitnessSelectorUp,
          regularCauchyWitnessSelectorToEventFlow x =
          regularCauchyWitnessSelectorToEventFlow y → x = y) ∧
      regularCauchyWitnessSelectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk modulusRequest selectedWindow tolerance readback sealRow transport route provenance
          name =>
          change
            some
              (RegularCauchyWitnessSelectorUp.mk
                (regularCauchyWitnessSelectorDecodeBHist
                  (regularCauchyWitnessSelectorEncodeBHist modulusRequest))
                (regularCauchyWitnessSelectorDecodeBHist
                  (regularCauchyWitnessSelectorEncodeBHist selectedWindow))
                (regularCauchyWitnessSelectorDecodeBHist
                  (regularCauchyWitnessSelectorEncodeBHist tolerance))
                (regularCauchyWitnessSelectorDecodeBHist
                  (regularCauchyWitnessSelectorEncodeBHist readback))
                (regularCauchyWitnessSelectorDecodeBHist
                  (regularCauchyWitnessSelectorEncodeBHist sealRow))
                (regularCauchyWitnessSelectorDecodeBHist
                  (regularCauchyWitnessSelectorEncodeBHist transport))
                (regularCauchyWitnessSelectorDecodeBHist
                  (regularCauchyWitnessSelectorEncodeBHist route))
                (regularCauchyWitnessSelectorDecodeBHist
                  (regularCauchyWitnessSelectorEncodeBHist provenance))
                (regularCauchyWitnessSelectorDecodeBHist
                  (regularCauchyWitnessSelectorEncodeBHist name))) =
              some
                (RegularCauchyWitnessSelectorUp.mk modulusRequest selectedWindow tolerance
                  readback sealRow transport route provenance name)
          rw [regularCauchyWitnessSelectorDecode_encode_bhist modulusRequest,
            regularCauchyWitnessSelectorDecode_encode_bhist selectedWindow,
            regularCauchyWitnessSelectorDecode_encode_bhist tolerance,
            regularCauchyWitnessSelectorDecode_encode_bhist readback,
            regularCauchyWitnessSelectorDecode_encode_bhist sealRow,
            regularCauchyWitnessSelectorDecode_encode_bhist transport,
            regularCauchyWitnessSelectorDecode_encode_bhist route,
            regularCauchyWitnessSelectorDecode_encode_bhist provenance,
            regularCauchyWitnessSelectorDecode_encode_bhist name]
    · constructor
      · intro x y heq
        cases x with
        | mk modulusRequest₁ selectedWindow₁ tolerance₁ readback₁ sealRow₁ transport₁
            route₁ provenance₁ name₁ =>
            cases y with
            | mk modulusRequest₂ selectedWindow₂ tolerance₂ readback₂ sealRow₂ transport₂
                route₂ provenance₂ name₂ =>
                change
                  [regularCauchyWitnessSelectorEncodeBHist modulusRequest₁,
                    regularCauchyWitnessSelectorEncodeBHist selectedWindow₁,
                    regularCauchyWitnessSelectorEncodeBHist tolerance₁,
                    regularCauchyWitnessSelectorEncodeBHist readback₁,
                    regularCauchyWitnessSelectorEncodeBHist sealRow₁,
                    regularCauchyWitnessSelectorEncodeBHist transport₁,
                    regularCauchyWitnessSelectorEncodeBHist route₁,
                    regularCauchyWitnessSelectorEncodeBHist provenance₁,
                    regularCauchyWitnessSelectorEncodeBHist name₁] =
                  [regularCauchyWitnessSelectorEncodeBHist modulusRequest₂,
                    regularCauchyWitnessSelectorEncodeBHist selectedWindow₂,
                    regularCauchyWitnessSelectorEncodeBHist tolerance₂,
                    regularCauchyWitnessSelectorEncodeBHist readback₂,
                    regularCauchyWitnessSelectorEncodeBHist sealRow₂,
                    regularCauchyWitnessSelectorEncodeBHist transport₂,
                    regularCauchyWitnessSelectorEncodeBHist route₂,
                    regularCauchyWitnessSelectorEncodeBHist provenance₂,
                    regularCauchyWitnessSelectorEncodeBHist name₂] at heq
                injection heq with hModulusRequest t1
                injection t1 with hSelectedWindow t2
                injection t2 with hTolerance t3
                injection t3 with hReadback t4
                injection t4 with hSealRow t5
                injection t5 with hTransport t6
                injection t6 with hRoute t7
                injection t7 with hProvenance t8
                injection t8 with hName _
                have hModulusRequestRow : modulusRequest₁ = modulusRequest₂ := by
                  have hdecode := congrArg regularCauchyWitnessSelectorDecodeBHist
                    hModulusRequest
                  rw [regularCauchyWitnessSelectorDecode_encode_bhist modulusRequest₁,
                    regularCauchyWitnessSelectorDecode_encode_bhist modulusRequest₂] at hdecode
                  exact hdecode
                have hSelectedWindowRow : selectedWindow₁ = selectedWindow₂ := by
                  have hdecode := congrArg regularCauchyWitnessSelectorDecodeBHist
                    hSelectedWindow
                  rw [regularCauchyWitnessSelectorDecode_encode_bhist selectedWindow₁,
                    regularCauchyWitnessSelectorDecode_encode_bhist selectedWindow₂] at hdecode
                  exact hdecode
                have hToleranceRow : tolerance₁ = tolerance₂ := by
                  have hdecode := congrArg regularCauchyWitnessSelectorDecodeBHist hTolerance
                  rw [regularCauchyWitnessSelectorDecode_encode_bhist tolerance₁,
                    regularCauchyWitnessSelectorDecode_encode_bhist tolerance₂] at hdecode
                  exact hdecode
                have hReadbackRow : readback₁ = readback₂ := by
                  have hdecode := congrArg regularCauchyWitnessSelectorDecodeBHist hReadback
                  rw [regularCauchyWitnessSelectorDecode_encode_bhist readback₁,
                    regularCauchyWitnessSelectorDecode_encode_bhist readback₂] at hdecode
                  exact hdecode
                have hSealRowEq : sealRow₁ = sealRow₂ := by
                  have hdecode := congrArg regularCauchyWitnessSelectorDecodeBHist hSealRow
                  rw [regularCauchyWitnessSelectorDecode_encode_bhist sealRow₁,
                    regularCauchyWitnessSelectorDecode_encode_bhist sealRow₂] at hdecode
                  exact hdecode
                have hTransportRow : transport₁ = transport₂ := by
                  have hdecode := congrArg regularCauchyWitnessSelectorDecodeBHist hTransport
                  rw [regularCauchyWitnessSelectorDecode_encode_bhist transport₁,
                    regularCauchyWitnessSelectorDecode_encode_bhist transport₂] at hdecode
                  exact hdecode
                have hRouteRow : route₁ = route₂ := by
                  have hdecode := congrArg regularCauchyWitnessSelectorDecodeBHist hRoute
                  rw [regularCauchyWitnessSelectorDecode_encode_bhist route₁,
                    regularCauchyWitnessSelectorDecode_encode_bhist route₂] at hdecode
                  exact hdecode
                have hProvenanceRow : provenance₁ = provenance₂ := by
                  have hdecode := congrArg regularCauchyWitnessSelectorDecodeBHist hProvenance
                  rw [regularCauchyWitnessSelectorDecode_encode_bhist provenance₁,
                    regularCauchyWitnessSelectorDecode_encode_bhist provenance₂] at hdecode
                  exact hdecode
                have hNameRow : name₁ = name₂ := by
                  have hdecode := congrArg regularCauchyWitnessSelectorDecodeBHist hName
                  rw [regularCauchyWitnessSelectorDecode_encode_bhist name₁,
                    regularCauchyWitnessSelectorDecode_encode_bhist name₂] at hdecode
                  exact hdecode
                cases hModulusRequestRow
                cases hSelectedWindowRow
                cases hToleranceRow
                cases hReadbackRow
                cases hSealRowEq
                cases hTransportRow
                cases hRouteRow
                cases hProvenanceRow
                cases hNameRow
                rfl
      · rfl

end BEDC.Derived.RegularCauchyWitnessSelectorUp
