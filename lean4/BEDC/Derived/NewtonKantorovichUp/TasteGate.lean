import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NewtonKantorovichUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NewtonKantorovichUp : Type where
  | mk :
      (derivative inverse neighbourhood ledger residual banach replay readback realSeal
        transport continuation provenance localName : BHist) →
      NewtonKantorovichUp
  deriving DecidableEq

def newtonKantorovichEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: newtonKantorovichEncodeBHist h
  | BHist.e1 h => BMark.b1 :: newtonKantorovichEncodeBHist h

def newtonKantorovichDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (newtonKantorovichDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (newtonKantorovichDecodeBHist tail)

private theorem newtonKantorovich_decode_encode_bhist :
    ∀ h : BHist, newtonKantorovichDecodeBHist (newtonKantorovichEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def newtonKantorovichFields : NewtonKantorovichUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NewtonKantorovichUp.mk derivative inverse neighbourhood ledger residual banach replay
      readback realSeal transport continuation provenance localName =>
      [derivative, inverse, neighbourhood, ledger, residual, banach, replay, readback,
        realSeal, transport, continuation, provenance, localName]

def newtonKantorovichToEventFlow : NewtonKantorovichUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (newtonKantorovichFields x).map newtonKantorovichEncodeBHist

def newtonKantorovichFromEventFlow : EventFlow → Option NewtonKantorovichUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | derivative :: rest0 =>
      match rest0 with
      | [] => none
      | inverse :: rest1 =>
          match rest1 with
          | [] => none
          | neighbourhood :: rest2 =>
              match rest2 with
              | [] => none
              | ledger :: rest3 =>
                  match rest3 with
                  | [] => none
                  | residual :: rest4 =>
                      match rest4 with
                      | [] => none
                      | banach :: rest5 =>
                          match rest5 with
                          | [] => none
                          | replay :: rest6 =>
                              match rest6 with
                              | [] => none
                              | readback :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | realSeal :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | continuation :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | localName :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (NewtonKantorovichUp.mk
                                                              (newtonKantorovichDecodeBHist
                                                                derivative)
                                                              (newtonKantorovichDecodeBHist
                                                                inverse)
                                                              (newtonKantorovichDecodeBHist
                                                                neighbourhood)
                                                              (newtonKantorovichDecodeBHist
                                                                ledger)
                                                              (newtonKantorovichDecodeBHist
                                                                residual)
                                                              (newtonKantorovichDecodeBHist
                                                                banach)
                                                              (newtonKantorovichDecodeBHist
                                                                replay)
                                                              (newtonKantorovichDecodeBHist
                                                                readback)
                                                              (newtonKantorovichDecodeBHist
                                                                realSeal)
                                                              (newtonKantorovichDecodeBHist
                                                                transport)
                                                              (newtonKantorovichDecodeBHist
                                                                continuation)
                                                              (newtonKantorovichDecodeBHist
                                                                provenance)
                                                              (newtonKantorovichDecodeBHist
                                                                localName))
                                                      | _ :: _ => none

private theorem newtonKantorovich_round_trip :
    ∀ x : NewtonKantorovichUp,
      newtonKantorovichFromEventFlow (newtonKantorovichToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk derivative inverse neighbourhood ledger residual banach replay readback realSeal
      transport continuation provenance localName =>
      change
        some
          (NewtonKantorovichUp.mk
            (newtonKantorovichDecodeBHist (newtonKantorovichEncodeBHist derivative))
            (newtonKantorovichDecodeBHist (newtonKantorovichEncodeBHist inverse))
            (newtonKantorovichDecodeBHist (newtonKantorovichEncodeBHist neighbourhood))
            (newtonKantorovichDecodeBHist (newtonKantorovichEncodeBHist ledger))
            (newtonKantorovichDecodeBHist (newtonKantorovichEncodeBHist residual))
            (newtonKantorovichDecodeBHist (newtonKantorovichEncodeBHist banach))
            (newtonKantorovichDecodeBHist (newtonKantorovichEncodeBHist replay))
            (newtonKantorovichDecodeBHist (newtonKantorovichEncodeBHist readback))
            (newtonKantorovichDecodeBHist (newtonKantorovichEncodeBHist realSeal))
            (newtonKantorovichDecodeBHist (newtonKantorovichEncodeBHist transport))
            (newtonKantorovichDecodeBHist (newtonKantorovichEncodeBHist continuation))
            (newtonKantorovichDecodeBHist (newtonKantorovichEncodeBHist provenance))
            (newtonKantorovichDecodeBHist (newtonKantorovichEncodeBHist localName))) =
          some
            (NewtonKantorovichUp.mk derivative inverse neighbourhood ledger residual banach
              replay readback realSeal transport continuation provenance localName)
      rw [newtonKantorovich_decode_encode_bhist derivative,
        newtonKantorovich_decode_encode_bhist inverse,
        newtonKantorovich_decode_encode_bhist neighbourhood,
        newtonKantorovich_decode_encode_bhist ledger,
        newtonKantorovich_decode_encode_bhist residual,
        newtonKantorovich_decode_encode_bhist banach,
        newtonKantorovich_decode_encode_bhist replay,
        newtonKantorovich_decode_encode_bhist readback,
        newtonKantorovich_decode_encode_bhist realSeal,
        newtonKantorovich_decode_encode_bhist transport,
        newtonKantorovich_decode_encode_bhist continuation,
        newtonKantorovich_decode_encode_bhist provenance,
        newtonKantorovich_decode_encode_bhist localName]

private theorem newtonKantorovichToEventFlow_injective {x y : NewtonKantorovichUp} :
    newtonKantorovichToEventFlow x = newtonKantorovichToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      newtonKantorovichFromEventFlow (newtonKantorovichToEventFlow x) =
        newtonKantorovichFromEventFlow (newtonKantorovichToEventFlow y) :=
    congrArg newtonKantorovichFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (newtonKantorovich_round_trip x).symm
      (Eq.trans hread (newtonKantorovich_round_trip y)))

instance newtonKantorovichBHistCarrier : BHistCarrier NewtonKantorovichUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := newtonKantorovichToEventFlow
  fromEventFlow := newtonKantorovichFromEventFlow

instance newtonKantorovichChapterTasteGate : ChapterTasteGate NewtonKantorovichUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change newtonKantorovichFromEventFlow (newtonKantorovichToEventFlow x) = some x
    exact newtonKantorovich_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (newtonKantorovichToEventFlow_injective heq)

def taste_gate : ChapterTasteGate NewtonKantorovichUp :=
  -- BEDC touchpoint anchor: BHist BMark
  newtonKantorovichChapterTasteGate

theorem NewtonKantorovichTasteGate_single_carrier_alignment :
    (∀ h : BHist, newtonKantorovichDecodeBHist (newtonKantorovichEncodeBHist h) = h) ∧
      (∀ x : NewtonKantorovichUp,
        newtonKantorovichFromEventFlow (newtonKantorovichToEventFlow x) = some x) ∧
        (∀ x y : NewtonKantorovichUp,
          newtonKantorovichToEventFlow x = newtonKantorovichToEventFlow y → x = y) ∧
          newtonKantorovichEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact newtonKantorovich_decode_encode_bhist
  · constructor
    · exact newtonKantorovich_round_trip
    · constructor
      · intro x y heq
        exact newtonKantorovichToEventFlow_injective heq
      · rfl

end BEDC.Derived.NewtonKantorovichUp
