import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactLebesgueUniformHandoffUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactLebesgueUniformHandoffUp : Type where
  | mk :
      (compactSource pointwiseMap radiusLedger compactSelector uniformModulus
        continuation transport handoffTrace provenance localName : BHist) →
        CompactLebesgueUniformHandoffUp
  deriving DecidableEq

def compactLebesgueUniformHandoffEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactLebesgueUniformHandoffEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactLebesgueUniformHandoffEncodeBHist h

def compactLebesgueUniformHandoffDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactLebesgueUniformHandoffDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactLebesgueUniformHandoffDecodeBHist tail)

private theorem compactLebesgueUniformHandoffDecode_encode_bhist :
    ∀ h : BHist,
      compactLebesgueUniformHandoffDecodeBHist
        (compactLebesgueUniformHandoffEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compactLebesgueUniformHandoffFields :
    CompactLebesgueUniformHandoffUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactLebesgueUniformHandoffUp.mk compactSource pointwiseMap radiusLedger
      compactSelector uniformModulus continuation transport handoffTrace provenance
      localName =>
      [compactSource, pointwiseMap, radiusLedger, compactSelector, uniformModulus,
        continuation, transport, handoffTrace, provenance, localName]

def compactLebesgueUniformHandoffToEventFlow :
    CompactLebesgueUniformHandoffUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactLebesgueUniformHandoffFields x).map
      compactLebesgueUniformHandoffEncodeBHist

def compactLebesgueUniformHandoffFromEventFlow :
    EventFlow → Option CompactLebesgueUniformHandoffUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | compactSource :: rest0 =>
      match rest0 with
      | [] => none
      | pointwiseMap :: rest1 =>
          match rest1 with
          | [] => none
          | radiusLedger :: rest2 =>
              match rest2 with
              | [] => none
              | compactSelector :: rest3 =>
                  match rest3 with
                  | [] => none
                  | uniformModulus :: rest4 =>
                      match rest4 with
                      | [] => none
                      | continuation :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | handoffTrace :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localName :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (CompactLebesgueUniformHandoffUp.mk
                                                  (compactLebesgueUniformHandoffDecodeBHist
                                                    compactSource)
                                                  (compactLebesgueUniformHandoffDecodeBHist
                                                    pointwiseMap)
                                                  (compactLebesgueUniformHandoffDecodeBHist
                                                    radiusLedger)
                                                  (compactLebesgueUniformHandoffDecodeBHist
                                                    compactSelector)
                                                  (compactLebesgueUniformHandoffDecodeBHist
                                                    uniformModulus)
                                                  (compactLebesgueUniformHandoffDecodeBHist
                                                    continuation)
                                                  (compactLebesgueUniformHandoffDecodeBHist
                                                    transport)
                                                  (compactLebesgueUniformHandoffDecodeBHist
                                                    handoffTrace)
                                                  (compactLebesgueUniformHandoffDecodeBHist
                                                    provenance)
                                                  (compactLebesgueUniformHandoffDecodeBHist
                                                    localName))
                                          | _ :: _ => none

private theorem compactLebesgueUniformHandoff_round_trip :
    ∀ x : CompactLebesgueUniformHandoffUp,
      compactLebesgueUniformHandoffFromEventFlow
        (compactLebesgueUniformHandoffToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compactSource pointwiseMap radiusLedger compactSelector uniformModulus
      continuation transport handoffTrace provenance localName =>
      change
        some
          (CompactLebesgueUniformHandoffUp.mk
            (compactLebesgueUniformHandoffDecodeBHist
              (compactLebesgueUniformHandoffEncodeBHist compactSource))
            (compactLebesgueUniformHandoffDecodeBHist
              (compactLebesgueUniformHandoffEncodeBHist pointwiseMap))
            (compactLebesgueUniformHandoffDecodeBHist
              (compactLebesgueUniformHandoffEncodeBHist radiusLedger))
            (compactLebesgueUniformHandoffDecodeBHist
              (compactLebesgueUniformHandoffEncodeBHist compactSelector))
            (compactLebesgueUniformHandoffDecodeBHist
              (compactLebesgueUniformHandoffEncodeBHist uniformModulus))
            (compactLebesgueUniformHandoffDecodeBHist
              (compactLebesgueUniformHandoffEncodeBHist continuation))
            (compactLebesgueUniformHandoffDecodeBHist
              (compactLebesgueUniformHandoffEncodeBHist transport))
            (compactLebesgueUniformHandoffDecodeBHist
              (compactLebesgueUniformHandoffEncodeBHist handoffTrace))
            (compactLebesgueUniformHandoffDecodeBHist
              (compactLebesgueUniformHandoffEncodeBHist provenance))
            (compactLebesgueUniformHandoffDecodeBHist
              (compactLebesgueUniformHandoffEncodeBHist localName))) =
          some
            (CompactLebesgueUniformHandoffUp.mk compactSource pointwiseMap radiusLedger
              compactSelector uniformModulus continuation transport handoffTrace provenance
              localName)
      rw [compactLebesgueUniformHandoffDecode_encode_bhist compactSource,
        compactLebesgueUniformHandoffDecode_encode_bhist pointwiseMap,
        compactLebesgueUniformHandoffDecode_encode_bhist radiusLedger,
        compactLebesgueUniformHandoffDecode_encode_bhist compactSelector,
        compactLebesgueUniformHandoffDecode_encode_bhist uniformModulus,
        compactLebesgueUniformHandoffDecode_encode_bhist continuation,
        compactLebesgueUniformHandoffDecode_encode_bhist transport,
        compactLebesgueUniformHandoffDecode_encode_bhist handoffTrace,
        compactLebesgueUniformHandoffDecode_encode_bhist provenance,
        compactLebesgueUniformHandoffDecode_encode_bhist localName]

private theorem compactLebesgueUniformHandoffToEventFlow_injective
    {x y : CompactLebesgueUniformHandoffUp} :
    compactLebesgueUniformHandoffToEventFlow x =
      compactLebesgueUniformHandoffToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactLebesgueUniformHandoffFromEventFlow
          (compactLebesgueUniformHandoffToEventFlow x) =
        compactLebesgueUniformHandoffFromEventFlow
          (compactLebesgueUniformHandoffToEventFlow y) :=
    congrArg compactLebesgueUniformHandoffFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactLebesgueUniformHandoff_round_trip x).symm
      (Eq.trans hread (compactLebesgueUniformHandoff_round_trip y)))

private theorem compactLebesgueUniformHandoff_field_faithful :
    ∀ x y : CompactLebesgueUniformHandoffUp,
      compactLebesgueUniformHandoffFields x =
        compactLebesgueUniformHandoffFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk compactSource₁ pointwiseMap₁ radiusLedger₁ compactSelector₁ uniformModulus₁
      continuation₁ transport₁ handoffTrace₁ provenance₁ localName₁ =>
      cases y with
      | mk compactSource₂ pointwiseMap₂ radiusLedger₂ compactSelector₂ uniformModulus₂
          continuation₂ transport₂ handoffTrace₂ provenance₂ localName₂ =>
          cases h
          rfl

instance compactLebesgueUniformHandoffBHistCarrier :
    BHistCarrier CompactLebesgueUniformHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactLebesgueUniformHandoffToEventFlow
  fromEventFlow := compactLebesgueUniformHandoffFromEventFlow

instance compactLebesgueUniformHandoffChapterTasteGate :
    ChapterTasteGate CompactLebesgueUniformHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactLebesgueUniformHandoffFromEventFlow
        (compactLebesgueUniformHandoffToEventFlow x) = some x
    exact compactLebesgueUniformHandoff_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactLebesgueUniformHandoffToEventFlow_injective heq)

instance compactLebesgueUniformHandoffFieldFaithful :
    FieldFaithful CompactLebesgueUniformHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactLebesgueUniformHandoffFields
  field_faithful := compactLebesgueUniformHandoff_field_faithful

instance compactLebesgueUniformHandoffNontrivial :
    Nontrivial CompactLebesgueUniformHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactLebesgueUniformHandoffUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CompactLebesgueUniformHandoffUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompactLebesgueUniformHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactLebesgueUniformHandoffChapterTasteGate

theorem CompactLebesgueUniformHandoffTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactLebesgueUniformHandoffDecodeBHist
        (compactLebesgueUniformHandoffEncodeBHist h) = h) ∧
      (∀ x : CompactLebesgueUniformHandoffUp,
        compactLebesgueUniformHandoffFromEventFlow
          (compactLebesgueUniformHandoffToEventFlow x) = some x) ∧
        (∀ x y : CompactLebesgueUniformHandoffUp,
          compactLebesgueUniformHandoffToEventFlow x =
            compactLebesgueUniformHandoffToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate CompactLebesgueUniformHandoffUp) ∧
            Nonempty (FieldFaithful CompactLebesgueUniformHandoffUp) ∧
              Nonempty (Nontrivial CompactLebesgueUniformHandoffUp) ∧
                compactLebesgueUniformHandoffEncodeBHist BHist.Empty =
                  ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact compactLebesgueUniformHandoffDecode_encode_bhist
  · constructor
    · exact compactLebesgueUniformHandoff_round_trip
    · constructor
      · intro x y heq
        exact compactLebesgueUniformHandoffToEventFlow_injective heq
      · constructor
        · exact ⟨compactLebesgueUniformHandoffChapterTasteGate⟩
        · constructor
          · exact ⟨compactLebesgueUniformHandoffFieldFaithful⟩
          · constructor
            · exact ⟨compactLebesgueUniformHandoffNontrivial⟩
            · rfl

end BEDC.Derived.CompactLebesgueUniformHandoffUp.TasteGate

namespace BEDC.Derived.CompactLebesgueUniformHandoffUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.CompactLebesgueUniformHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.CompactLebesgueUniformHandoffUp
