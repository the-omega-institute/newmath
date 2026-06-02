import BEDC.Derived.EntropyUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EntropyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EntropyUp : Type where
  | mk
      (distribution integral logWeight transport ledger provenance localName : BHist) :
      EntropyUp
  deriving DecidableEq

def entropyEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: entropyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: entropyEncodeBHist h

def entropyDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (entropyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (entropyDecodeBHist tail)

private theorem entropyDecode_encode_bhist :
    forall h : BHist, entropyDecodeBHist (entropyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def entropyFields : EntropyUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EntropyUp.mk distribution integral logWeight transport ledger provenance localName =>
      [distribution, integral, logWeight, transport, ledger, provenance, localName]

def entropyToEventFlow : EntropyUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (entropyFields x).map entropyEncodeBHist

def entropyFromEventFlow : EventFlow -> Option EntropyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | distribution :: rest0 =>
      match rest0 with
      | [] => none
      | integral :: rest1 =>
          match rest1 with
          | [] => none
          | logWeight :: rest2 =>
              match rest2 with
              | [] => none
              | transport :: rest3 =>
                  match rest3 with
                  | [] => none
                  | ledger :: rest4 =>
                      match rest4 with
                      | [] => none
                      | provenance :: rest5 =>
                          match rest5 with
                          | [] => none
                          | localName :: rest6 =>
                              match rest6 with
                              | [] =>
                                  some
                                    (EntropyUp.mk
                                      (entropyDecodeBHist distribution)
                                      (entropyDecodeBHist integral)
                                      (entropyDecodeBHist logWeight)
                                      (entropyDecodeBHist transport)
                                      (entropyDecodeBHist ledger)
                                      (entropyDecodeBHist provenance)
                                      (entropyDecodeBHist localName))
                              | _ :: _ => none

private theorem entropy_round_trip :
    forall x : EntropyUp, entropyFromEventFlow (entropyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk distribution integral logWeight transport ledger provenance localName =>
      change
        some
          (EntropyUp.mk
            (entropyDecodeBHist (entropyEncodeBHist distribution))
            (entropyDecodeBHist (entropyEncodeBHist integral))
            (entropyDecodeBHist (entropyEncodeBHist logWeight))
            (entropyDecodeBHist (entropyEncodeBHist transport))
            (entropyDecodeBHist (entropyEncodeBHist ledger))
            (entropyDecodeBHist (entropyEncodeBHist provenance))
            (entropyDecodeBHist (entropyEncodeBHist localName))) =
          some
            (EntropyUp.mk distribution integral logWeight transport ledger provenance localName)
      rw [entropyDecode_encode_bhist distribution, entropyDecode_encode_bhist integral,
        entropyDecode_encode_bhist logWeight, entropyDecode_encode_bhist transport,
        entropyDecode_encode_bhist ledger, entropyDecode_encode_bhist provenance,
        entropyDecode_encode_bhist localName]

private theorem entropyToEventFlow_injective {x y : EntropyUp} :
    entropyToEventFlow x = entropyToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      entropyFromEventFlow (entropyToEventFlow x) =
        entropyFromEventFlow (entropyToEventFlow y) :=
    congrArg entropyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (entropy_round_trip x).symm (Eq.trans hread (entropy_round_trip y)))

private theorem entropy_fields_faithful :
    forall x y : EntropyUp, entropyFields x = entropyFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk distribution1 integral1 logWeight1 transport1 ledger1 provenance1 localName1 =>
      cases y with
      | mk distribution2 integral2 logWeight2 transport2 ledger2 provenance2 localName2 =>
          cases hfields
          rfl

instance entropyBHistCarrier : BHistCarrier EntropyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := entropyToEventFlow
  fromEventFlow := entropyFromEventFlow

instance entropyChapterTasteGate : ChapterTasteGate EntropyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change entropyFromEventFlow (entropyToEventFlow x) = some x
    exact entropy_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (entropyToEventFlow_injective heq)

instance entropyFieldFaithful : FieldFaithful EntropyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := entropyFields
  field_faithful := entropy_fields_faithful

instance entropyNontrivial : Nontrivial EntropyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EntropyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      EntropyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem EntropyUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate EntropyUp) ∧ Nonempty (FieldFaithful EntropyUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial EntropyUp) ∧
        (∀ h : BHist, entropyDecodeBHist (entropyEncodeBHist h) = h) ∧
          (∀ x : EntropyUp, entropyFromEventFlow (entropyToEventFlow x) = some x) ∧
            (∀ x y : EntropyUp, entropyToEventFlow x = entropyToEventFlow y -> x = y) ∧
              entropyEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨entropyChapterTasteGate⟩
  · constructor
    · exact ⟨entropyFieldFaithful⟩
    · constructor
      · exact ⟨entropyNontrivial⟩
      · constructor
        · exact entropyDecode_encode_bhist
        · constructor
          · exact entropy_round_trip
          · constructor
            · intro x y heq
              exact entropyToEventFlow_injective heq
            · rfl

end BEDC.Derived.EntropyUp
