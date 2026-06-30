import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AnalyticContinuationOperationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AnalyticContinuationOperationUp : Type where
  | mk (domainLeft domainRight inputLeft inputRight overlap operation output ledger transport route pkg name : BHist) : AnalyticContinuationOperationUp
  deriving DecidableEq

def analyticContinuationOperationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: analyticContinuationOperationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: analyticContinuationOperationEncodeBHist h

def analyticContinuationOperationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (analyticContinuationOperationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (analyticContinuationOperationDecodeBHist tail)

private theorem analyticContinuationOperation_decode_encode_bhist :
    ∀ h : BHist,
      analyticContinuationOperationDecodeBHist
        (analyticContinuationOperationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def analyticContinuationOperationFields :
    AnalyticContinuationOperationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AnalyticContinuationOperationUp.mk domainLeft domainRight inputLeft inputRight overlap operation output ledger transport route pkg name =>
      [domainLeft, domainRight, inputLeft, inputRight, overlap, operation, output, ledger, transport, route, pkg, name]

def analyticContinuationOperationToEventFlow :
    AnalyticContinuationOperationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (analyticContinuationOperationFields x).map
      analyticContinuationOperationEncodeBHist

def analyticContinuationOperationFromEventFlow :
    EventFlow → Option AnalyticContinuationOperationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | domainLeft :: rest =>
      match rest with
      | [] => none
      | domainRight :: rest =>
          match rest with
          | [] => none
          | inputLeft :: rest =>
              match rest with
              | [] => none
              | inputRight :: rest =>
                  match rest with
                  | [] => none
                  | overlap :: rest =>
                      match rest with
                      | [] => none
                      | operation :: rest =>
                          match rest with
                          | [] => none
                          | output :: rest =>
                              match rest with
                              | [] => none
                              | ledger :: rest =>
                                  match rest with
                                  | [] => none
                                  | transport :: rest =>
                                      match rest with
                                      | [] => none
                                      | route :: rest =>
                                          match rest with
                                          | [] => none
                                          | pkg :: rest =>
                                              match rest with
                                              | [] => none
                                              | name :: rest =>
                                                  match rest with
                                                  | [] =>
                                                      some
                                                        (AnalyticContinuationOperationUp.mk
                                                          (analyticContinuationOperationDecodeBHist domainLeft)
                                                          (analyticContinuationOperationDecodeBHist domainRight)
                                                          (analyticContinuationOperationDecodeBHist inputLeft)
                                                          (analyticContinuationOperationDecodeBHist inputRight)
                                                          (analyticContinuationOperationDecodeBHist overlap)
                                                          (analyticContinuationOperationDecodeBHist operation)
                                                          (analyticContinuationOperationDecodeBHist output)
                                                          (analyticContinuationOperationDecodeBHist ledger)
                                                          (analyticContinuationOperationDecodeBHist transport)
                                                          (analyticContinuationOperationDecodeBHist route)
                                                          (analyticContinuationOperationDecodeBHist pkg)
                                                          (analyticContinuationOperationDecodeBHist name))
                                                  | _ :: _ => none

private theorem analyticContinuationOperation_round_trip :
    ∀ x : AnalyticContinuationOperationUp,
      analyticContinuationOperationFromEventFlow
        (analyticContinuationOperationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk domainLeft domainRight inputLeft inputRight overlap operation output ledger transport route pkg name =>
      change
        some
          (AnalyticContinuationOperationUp.mk
            (analyticContinuationOperationDecodeBHist
              (analyticContinuationOperationEncodeBHist domainLeft))
            (analyticContinuationOperationDecodeBHist
              (analyticContinuationOperationEncodeBHist domainRight))
            (analyticContinuationOperationDecodeBHist
              (analyticContinuationOperationEncodeBHist inputLeft))
            (analyticContinuationOperationDecodeBHist
              (analyticContinuationOperationEncodeBHist inputRight))
            (analyticContinuationOperationDecodeBHist
              (analyticContinuationOperationEncodeBHist overlap))
            (analyticContinuationOperationDecodeBHist
              (analyticContinuationOperationEncodeBHist operation))
            (analyticContinuationOperationDecodeBHist
              (analyticContinuationOperationEncodeBHist output))
            (analyticContinuationOperationDecodeBHist
              (analyticContinuationOperationEncodeBHist ledger))
            (analyticContinuationOperationDecodeBHist
              (analyticContinuationOperationEncodeBHist transport))
            (analyticContinuationOperationDecodeBHist
              (analyticContinuationOperationEncodeBHist route))
            (analyticContinuationOperationDecodeBHist
              (analyticContinuationOperationEncodeBHist pkg))
            (analyticContinuationOperationDecodeBHist
              (analyticContinuationOperationEncodeBHist name))) =
          some (AnalyticContinuationOperationUp.mk domainLeft domainRight inputLeft inputRight overlap operation output ledger transport route pkg name)
      rw [analyticContinuationOperation_decode_encode_bhist domainLeft,
        analyticContinuationOperation_decode_encode_bhist domainRight,
        analyticContinuationOperation_decode_encode_bhist inputLeft,
        analyticContinuationOperation_decode_encode_bhist inputRight,
        analyticContinuationOperation_decode_encode_bhist overlap,
        analyticContinuationOperation_decode_encode_bhist operation,
        analyticContinuationOperation_decode_encode_bhist output,
        analyticContinuationOperation_decode_encode_bhist ledger,
        analyticContinuationOperation_decode_encode_bhist transport,
        analyticContinuationOperation_decode_encode_bhist route,
        analyticContinuationOperation_decode_encode_bhist pkg,
        analyticContinuationOperation_decode_encode_bhist name]

private theorem analyticContinuationOperationToEventFlow_injective
    {x y : AnalyticContinuationOperationUp} :
    analyticContinuationOperationToEventFlow x =
      analyticContinuationOperationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      analyticContinuationOperationFromEventFlow
          (analyticContinuationOperationToEventFlow x) =
        analyticContinuationOperationFromEventFlow
          (analyticContinuationOperationToEventFlow y) :=
    congrArg analyticContinuationOperationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (analyticContinuationOperation_round_trip x).symm
      (Eq.trans hread (analyticContinuationOperation_round_trip y)))

private theorem analyticContinuationOperation_fields_faithful :
    ∀ x y : AnalyticContinuationOperationUp,
      analyticContinuationOperationFields x =
        analyticContinuationOperationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk domainLeft domainRight inputLeft inputRight overlap operation output ledger transport route pkg name =>
      cases y with
      | mk domainLeft' domainRight' inputLeft' inputRight' overlap' operation' output' ledger' transport' route' pkg' name' =>
          cases hfields
          rfl

instance analyticContinuationOperationBHistCarrier :
    BHistCarrier AnalyticContinuationOperationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := analyticContinuationOperationToEventFlow
  fromEventFlow := analyticContinuationOperationFromEventFlow

instance analyticContinuationOperationChapterTasteGate :
    ChapterTasteGate AnalyticContinuationOperationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      analyticContinuationOperationFromEventFlow
        (analyticContinuationOperationToEventFlow x) = some x
    exact analyticContinuationOperation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (analyticContinuationOperationToEventFlow_injective heq)

instance analyticContinuationOperationFieldFaithful :
    FieldFaithful AnalyticContinuationOperationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := analyticContinuationOperationFields
  field_faithful := analyticContinuationOperation_fields_faithful

instance analyticContinuationOperationNontrivial :
    Nontrivial AnalyticContinuationOperationUp where
  witness_pair :=
    ⟨AnalyticContinuationOperationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      AnalyticContinuationOperationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AnalyticContinuationOperationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  analyticContinuationOperationChapterTasteGate

theorem AnalyticContinuationOperationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        analyticContinuationOperationDecodeBHist
          (analyticContinuationOperationEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier AnalyticContinuationOperationUp) ∧
        Nonempty (ChapterTasteGate AnalyticContinuationOperationUp) ∧
          analyticContinuationOperationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨analyticContinuationOperation_decode_encode_bhist,
      ⟨analyticContinuationOperationBHistCarrier⟩,
      ⟨analyticContinuationOperationChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.AnalyticContinuationOperationUp
