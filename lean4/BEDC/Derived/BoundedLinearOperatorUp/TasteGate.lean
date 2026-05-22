import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedLinearOperatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedLinearOperatorUp : Type where
  | mk (source target endpoint bound ledger transport continuation provenance name : BHist) :
      BoundedLinearOperatorUp
  deriving DecidableEq

def boundedLinearOperatorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedLinearOperatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedLinearOperatorEncodeBHist h

def boundedLinearOperatorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedLinearOperatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedLinearOperatorDecodeBHist tail)

private theorem boundedLinearOperator_decode_encode_bhist :
    ∀ h : BHist, boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def boundedLinearOperatorFields : BoundedLinearOperatorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedLinearOperatorUp.mk source target endpoint bound ledger transport continuation provenance
      name =>
      [source, target, endpoint, bound, ledger, transport, continuation, provenance, name]

def boundedLinearOperatorToEventFlow : BoundedLinearOperatorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (boundedLinearOperatorFields x).map boundedLinearOperatorEncodeBHist

def boundedLinearOperatorFromEventFlow : EventFlow → Option BoundedLinearOperatorUp
  -- BEDC touchpoint anchor: BHist BMark
  | source :: restSource =>
      match restSource with
      | target :: restTarget =>
          match restTarget with
          | endpoint :: restEndpoint =>
              match restEndpoint with
              | bound :: restBound =>
                  match restBound with
                  | ledger :: restLedger =>
                      match restLedger with
                      | transport :: restTransport =>
                          match restTransport with
                          | continuation :: restContinuation =>
                              match restContinuation with
                              | provenance :: restProvenance =>
                                  match restProvenance with
                                  | name :: restName =>
                                      match restName with
                                      | [] =>
                                          some
                                            (BoundedLinearOperatorUp.mk
                                              (boundedLinearOperatorDecodeBHist source)
                                              (boundedLinearOperatorDecodeBHist target)
                                              (boundedLinearOperatorDecodeBHist endpoint)
                                              (boundedLinearOperatorDecodeBHist bound)
                                              (boundedLinearOperatorDecodeBHist ledger)
                                              (boundedLinearOperatorDecodeBHist transport)
                                              (boundedLinearOperatorDecodeBHist continuation)
                                              (boundedLinearOperatorDecodeBHist provenance)
                                              (boundedLinearOperatorDecodeBHist name))
                                      | _ :: _ => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem boundedLinearOperator_round_trip :
    ∀ x : BoundedLinearOperatorUp,
      boundedLinearOperatorFromEventFlow (boundedLinearOperatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk source target endpoint bound ledger transport continuation provenance name =>
      change
        some
          (BoundedLinearOperatorUp.mk
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist source))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist target))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist endpoint))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist bound))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist ledger))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist transport))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist continuation))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist provenance))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist name))) =
          some
            (BoundedLinearOperatorUp.mk source target endpoint bound ledger transport
              continuation provenance name)
      rw [boundedLinearOperator_decode_encode_bhist source,
        boundedLinearOperator_decode_encode_bhist target,
        boundedLinearOperator_decode_encode_bhist endpoint,
        boundedLinearOperator_decode_encode_bhist bound,
        boundedLinearOperator_decode_encode_bhist ledger,
        boundedLinearOperator_decode_encode_bhist transport,
        boundedLinearOperator_decode_encode_bhist continuation,
        boundedLinearOperator_decode_encode_bhist provenance,
        boundedLinearOperator_decode_encode_bhist name]

private theorem boundedLinearOperatorToEventFlow_injective {x y : BoundedLinearOperatorUp} :
    boundedLinearOperatorToEventFlow x = boundedLinearOperatorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = boundedLinearOperatorFromEventFlow (boundedLinearOperatorToEventFlow x) :=
        (boundedLinearOperator_round_trip x).symm
      _ = boundedLinearOperatorFromEventFlow (boundedLinearOperatorToEventFlow y) :=
        congrArg boundedLinearOperatorFromEventFlow hxy
      _ = some y := boundedLinearOperator_round_trip y
  exact Option.some.inj optionEq

instance boundedLinearOperatorBHistCarrier : BHistCarrier BoundedLinearOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedLinearOperatorToEventFlow
  fromEventFlow := boundedLinearOperatorFromEventFlow

instance boundedLinearOperatorChapterTasteGate : ChapterTasteGate BoundedLinearOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedLinearOperatorFromEventFlow (boundedLinearOperatorToEventFlow x) = some x
    exact boundedLinearOperator_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedLinearOperatorToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BoundedLinearOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedLinearOperatorChapterTasteGate

theorem BoundedLinearOperatorTasteGate_single_carrier_alignment :
    (∀ h : BHist, boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist h) = h) ∧
      (∀ x : BoundedLinearOperatorUp,
        boundedLinearOperatorFromEventFlow (boundedLinearOperatorToEventFlow x) = some x) ∧
        (∀ x y : BoundedLinearOperatorUp,
          boundedLinearOperatorToEventFlow x = boundedLinearOperatorToEventFlow y → x = y) ∧
          boundedLinearOperatorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨boundedLinearOperator_decode_encode_bhist,
      boundedLinearOperator_round_trip,
      (by
        intro x y heq
        exact boundedLinearOperatorToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BoundedLinearOperatorUp
