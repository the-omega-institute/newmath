import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteWindowEnvelopeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteWindowEnvelopeUp : Type where
  | mk (source anchor window ledger classifier sealRow endpoint provenance name : BHist) :
      FiniteWindowEnvelopeUp
  deriving DecidableEq

def finiteWindowEnvelopeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteWindowEnvelopeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteWindowEnvelopeEncodeBHist h

def finiteWindowEnvelopeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteWindowEnvelopeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteWindowEnvelopeDecodeBHist tail)

private theorem finiteWindowEnvelope_decode_encode :
    ∀ h : BHist, finiteWindowEnvelopeDecodeBHist (finiteWindowEnvelopeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteWindowEnvelopeFields : FiniteWindowEnvelopeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteWindowEnvelopeUp.mk source anchor window ledger classifier sealRow endpoint provenance name =>
      [source, anchor, window, ledger, classifier, sealRow, endpoint, provenance, name]

def finiteWindowEnvelopeToEventFlow : FiniteWindowEnvelopeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (finiteWindowEnvelopeFields x).map finiteWindowEnvelopeEncodeBHist

def finiteWindowEnvelopeFromEventFlow : EventFlow → Option FiniteWindowEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    match ef with
    | [] => none
    | source :: rest1 =>
        match rest1 with
        | [] => none
        | anchor :: rest2 =>
            match rest2 with
            | [] => none
            | window :: rest3 =>
                match rest3 with
                | [] => none
                | ledger :: rest4 =>
                    match rest4 with
                    | [] => none
                    | classifier :: rest5 =>
                        match rest5 with
                        | [] => none
                        | sealRow :: rest6 =>
                            match rest6 with
                            | [] => none
                            | endpoint :: rest7 =>
                                match rest7 with
                                | [] => none
                                | provenance :: rest8 =>
                                    match rest8 with
                                    | [] => none
                                    | name :: rest9 =>
                                        match rest9 with
                                        | [] =>
                                            some
                                              (FiniteWindowEnvelopeUp.mk
                                                (finiteWindowEnvelopeDecodeBHist source)
                                                (finiteWindowEnvelopeDecodeBHist anchor)
                                                (finiteWindowEnvelopeDecodeBHist window)
                                                (finiteWindowEnvelopeDecodeBHist ledger)
                                                (finiteWindowEnvelopeDecodeBHist classifier)
                                                (finiteWindowEnvelopeDecodeBHist sealRow)
                                                (finiteWindowEnvelopeDecodeBHist endpoint)
                                                (finiteWindowEnvelopeDecodeBHist provenance)
                                                (finiteWindowEnvelopeDecodeBHist name))
                                        | _ :: _ => none

private theorem finiteWindowEnvelope_round_trip :
    ∀ x : FiniteWindowEnvelopeUp,
      finiteWindowEnvelopeFromEventFlow (finiteWindowEnvelopeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source anchor window ledger classifier sealRow endpoint provenance name =>
      change
        some
            (FiniteWindowEnvelopeUp.mk
              (finiteWindowEnvelopeDecodeBHist (finiteWindowEnvelopeEncodeBHist source))
              (finiteWindowEnvelopeDecodeBHist (finiteWindowEnvelopeEncodeBHist anchor))
              (finiteWindowEnvelopeDecodeBHist (finiteWindowEnvelopeEncodeBHist window))
              (finiteWindowEnvelopeDecodeBHist (finiteWindowEnvelopeEncodeBHist ledger))
              (finiteWindowEnvelopeDecodeBHist (finiteWindowEnvelopeEncodeBHist classifier))
              (finiteWindowEnvelopeDecodeBHist (finiteWindowEnvelopeEncodeBHist sealRow))
              (finiteWindowEnvelopeDecodeBHist (finiteWindowEnvelopeEncodeBHist endpoint))
              (finiteWindowEnvelopeDecodeBHist (finiteWindowEnvelopeEncodeBHist provenance))
              (finiteWindowEnvelopeDecodeBHist (finiteWindowEnvelopeEncodeBHist name))) =
          some
            (FiniteWindowEnvelopeUp.mk source anchor window ledger classifier sealRow endpoint
              provenance name)
      rw [finiteWindowEnvelope_decode_encode source, finiteWindowEnvelope_decode_encode anchor,
        finiteWindowEnvelope_decode_encode window, finiteWindowEnvelope_decode_encode ledger,
        finiteWindowEnvelope_decode_encode classifier, finiteWindowEnvelope_decode_encode sealRow,
        finiteWindowEnvelope_decode_encode endpoint, finiteWindowEnvelope_decode_encode provenance,
        finiteWindowEnvelope_decode_encode name]

private theorem finiteWindowEnvelopeToEventFlow_injective {x y : FiniteWindowEnvelopeUp} :
    finiteWindowEnvelopeToEventFlow x = finiteWindowEnvelopeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteWindowEnvelopeFromEventFlow (finiteWindowEnvelopeToEventFlow x) =
        finiteWindowEnvelopeFromEventFlow (finiteWindowEnvelopeToEventFlow y) :=
    congrArg finiteWindowEnvelopeFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (finiteWindowEnvelope_round_trip x).symm
        (Eq.trans hread (finiteWindowEnvelope_round_trip y)))

private theorem finiteWindowEnvelope_fields_faithful :
    ∀ x y : FiniteWindowEnvelopeUp,
      finiteWindowEnvelopeFields x = finiteWindowEnvelopeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source anchor window ledger classifier sealRow endpoint provenance name =>
      cases y with
      | mk source' anchor' window' ledger' classifier' sealRow' endpoint' provenance' name' =>
          cases hfields
          rfl

instance finiteWindowEnvelopeBHistCarrier : BHistCarrier FiniteWindowEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteWindowEnvelopeToEventFlow
  fromEventFlow := finiteWindowEnvelopeFromEventFlow

instance finiteWindowEnvelopeChapterTasteGate : ChapterTasteGate FiniteWindowEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteWindowEnvelopeFromEventFlow (finiteWindowEnvelopeToEventFlow x) = some x
    exact finiteWindowEnvelope_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteWindowEnvelopeToEventFlow_injective heq)

instance finiteWindowEnvelopeFieldFaithful : FieldFaithful FiniteWindowEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteWindowEnvelopeFields
  field_faithful := finiteWindowEnvelope_fields_faithful

instance finiteWindowEnvelopeNontrivial : Nontrivial FiniteWindowEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteWindowEnvelopeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteWindowEnvelopeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteWindowEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteWindowEnvelopeChapterTasteGate

theorem FiniteWindowEnvelopeTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteWindowEnvelopeDecodeBHist (finiteWindowEnvelopeEncodeBHist h) = h) ∧
      (∀ x : FiniteWindowEnvelopeUp,
        finiteWindowEnvelopeFromEventFlow (finiteWindowEnvelopeToEventFlow x) = some x) ∧
        (∀ x y : FiniteWindowEnvelopeUp,
          finiteWindowEnvelopeToEventFlow x = finiteWindowEnvelopeToEventFlow y → x = y) ∧
          finiteWindowEnvelopeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact finiteWindowEnvelope_decode_encode
  · constructor
    · exact finiteWindowEnvelope_round_trip
    · constructor
      · intro x y heq
        exact finiteWindowEnvelopeToEventFlow_injective heq
      · rfl

end BEDC.Derived.FiniteWindowEnvelopeUp
