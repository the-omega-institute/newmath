import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FractionalPartUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FractionalPartUp : Type where
  | mk :
      (sourceReal integerPart residualReal bracket dyadicTolerance streamWindow
        regularReadback transport continuation provenance localName : BHist) →
        FractionalPartUp
  deriving DecidableEq

def fractionalPartEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fractionalPartEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fractionalPartEncodeBHist h

def fractionalPartDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fractionalPartDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fractionalPartDecodeBHist tail)

private theorem FractionalPartTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, fractionalPartDecodeBHist (fractionalPartEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def fractionalPartFields : FractionalPartUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FractionalPartUp.mk sourceReal integerPart residualReal bracket dyadicTolerance
      streamWindow regularReadback transport continuation provenance localName =>
      [sourceReal, integerPart, residualReal, bracket, dyadicTolerance, streamWindow,
        regularReadback, transport, continuation, provenance, localName]

def fractionalPartToEventFlow : FractionalPartUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fractionalPartFields x).map fractionalPartEncodeBHist

def fractionalPartFromEventFlow : EventFlow → Option FractionalPartUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | sourceReal :: rest0 =>
      match rest0 with
      | [] => none
      | integerPart :: rest1 =>
          match rest1 with
          | [] => none
          | residualReal :: rest2 =>
              match rest2 with
              | [] => none
              | bracket :: rest3 =>
                  match rest3 with
                  | [] => none
                  | dyadicTolerance :: rest4 =>
                      match rest4 with
                      | [] => none
                      | streamWindow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | regularReadback :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | continuation :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | localName :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (FractionalPartUp.mk
                                                      (fractionalPartDecodeBHist sourceReal)
                                                      (fractionalPartDecodeBHist integerPart)
                                                      (fractionalPartDecodeBHist residualReal)
                                                      (fractionalPartDecodeBHist bracket)
                                                      (fractionalPartDecodeBHist dyadicTolerance)
                                                      (fractionalPartDecodeBHist streamWindow)
                                                      (fractionalPartDecodeBHist regularReadback)
                                                      (fractionalPartDecodeBHist transport)
                                                      (fractionalPartDecodeBHist continuation)
                                                      (fractionalPartDecodeBHist provenance)
                                                      (fractionalPartDecodeBHist localName))
                                              | _ :: _ => none

private theorem FractionalPartTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FractionalPartUp,
      fractionalPartFromEventFlow (fractionalPartToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceReal integerPart residualReal bracket dyadicTolerance streamWindow regularReadback
      transport continuation provenance localName =>
      change
        some
          (FractionalPartUp.mk
            (fractionalPartDecodeBHist (fractionalPartEncodeBHist sourceReal))
            (fractionalPartDecodeBHist (fractionalPartEncodeBHist integerPart))
            (fractionalPartDecodeBHist (fractionalPartEncodeBHist residualReal))
            (fractionalPartDecodeBHist (fractionalPartEncodeBHist bracket))
            (fractionalPartDecodeBHist (fractionalPartEncodeBHist dyadicTolerance))
            (fractionalPartDecodeBHist (fractionalPartEncodeBHist streamWindow))
            (fractionalPartDecodeBHist (fractionalPartEncodeBHist regularReadback))
            (fractionalPartDecodeBHist (fractionalPartEncodeBHist transport))
            (fractionalPartDecodeBHist (fractionalPartEncodeBHist continuation))
            (fractionalPartDecodeBHist (fractionalPartEncodeBHist provenance))
            (fractionalPartDecodeBHist (fractionalPartEncodeBHist localName))) =
          some
            (FractionalPartUp.mk sourceReal integerPart residualReal bracket dyadicTolerance
              streamWindow regularReadback transport continuation provenance localName)
      rw [FractionalPartTasteGate_single_carrier_alignment_decode_encode sourceReal,
        FractionalPartTasteGate_single_carrier_alignment_decode_encode integerPart,
        FractionalPartTasteGate_single_carrier_alignment_decode_encode residualReal,
        FractionalPartTasteGate_single_carrier_alignment_decode_encode bracket,
        FractionalPartTasteGate_single_carrier_alignment_decode_encode dyadicTolerance,
        FractionalPartTasteGate_single_carrier_alignment_decode_encode streamWindow,
        FractionalPartTasteGate_single_carrier_alignment_decode_encode regularReadback,
        FractionalPartTasteGate_single_carrier_alignment_decode_encode transport,
        FractionalPartTasteGate_single_carrier_alignment_decode_encode continuation,
        FractionalPartTasteGate_single_carrier_alignment_decode_encode provenance,
        FractionalPartTasteGate_single_carrier_alignment_decode_encode localName]

private theorem FractionalPartTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FractionalPartUp} :
    fractionalPartToEventFlow x = fractionalPartToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fractionalPartFromEventFlow (fractionalPartToEventFlow x) =
        fractionalPartFromEventFlow (fractionalPartToEventFlow y) :=
    congrArg fractionalPartFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FractionalPartTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FractionalPartTasteGate_single_carrier_alignment_round_trip y)))

private theorem FractionalPartTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : FractionalPartUp, fractionalPartFields x = fractionalPartFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk sourceReal₁ integerPart₁ residualReal₁ bracket₁ dyadicTolerance₁ streamWindow₁
      regularReadback₁ transport₁ continuation₁ provenance₁ localName₁ =>
      cases y with
      | mk sourceReal₂ integerPart₂ residualReal₂ bracket₂ dyadicTolerance₂ streamWindow₂
          regularReadback₂ transport₂ continuation₂ provenance₂ localName₂ =>
          injection hfields with hSourceReal tail0
          injection tail0 with hIntegerPart tail1
          injection tail1 with hResidualReal tail2
          injection tail2 with hBracket tail3
          injection tail3 with hDyadicTolerance tail4
          injection tail4 with hStreamWindow tail5
          injection tail5 with hRegularReadback tail6
          injection tail6 with hTransport tail7
          injection tail7 with hContinuation tail8
          injection tail8 with hProvenance tail9
          injection tail9 with hLocalName _
          subst hSourceReal
          subst hIntegerPart
          subst hResidualReal
          subst hBracket
          subst hDyadicTolerance
          subst hStreamWindow
          subst hRegularReadback
          subst hTransport
          subst hContinuation
          subst hProvenance
          subst hLocalName
          rfl

instance fractionalPartBHistCarrier : BHistCarrier FractionalPartUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fractionalPartToEventFlow
  fromEventFlow := fractionalPartFromEventFlow

instance fractionalPartChapterTasteGate : ChapterTasteGate FractionalPartUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fractionalPartFromEventFlow (fractionalPartToEventFlow x) = some x
    exact FractionalPartTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FractionalPartTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance fractionalPartFieldFaithful : FieldFaithful FractionalPartUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fractionalPartFields
  field_faithful := FractionalPartTasteGate_single_carrier_alignment_fields_faithful

instance fractionalPartNontrivial : Nontrivial FractionalPartUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FractionalPartUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FractionalPartUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FractionalPartUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fractionalPartChapterTasteGate

theorem FractionalPartTasteGate_single_carrier_alignment :
    (∀ h : BHist, fractionalPartDecodeBHist (fractionalPartEncodeBHist h) = h) ∧
      (∀ x : FractionalPartUp,
        fractionalPartFromEventFlow (fractionalPartToEventFlow x) = some x) ∧
        (∀ x y : FractionalPartUp,
          fractionalPartToEventFlow x = fractionalPartToEventFlow y → x = y) ∧
          fractionalPartEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨FractionalPartTasteGate_single_carrier_alignment_decode_encode,
      FractionalPartTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        FractionalPartTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FractionalPartUp
