import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteObservationCofinalitySelectorUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteObservationCofinalitySelectorUp : Type where
  | mk :
      (budget request windows dyadic regular endpoint transport continuation provenance
        localNameCert : BHist) →
      FiniteObservationCofinalitySelectorUp
  deriving DecidableEq

def finiteObservationCofinalitySelectorFields :
    FiniteObservationCofinalitySelectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteObservationCofinalitySelectorUp.mk budget request windows dyadic regular endpoint
      transport continuation provenance localNameCert =>
      [budget, request, windows, dyadic, regular, endpoint, transport, continuation,
        provenance, localNameCert]

def finiteObservationCofinalitySelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteObservationCofinalitySelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteObservationCofinalitySelectorEncodeBHist h

def finiteObservationCofinalitySelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteObservationCofinalitySelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteObservationCofinalitySelectorDecodeBHist tail)

private theorem finiteObservationCofinalitySelectorDecodeEncodeBHist :
    ∀ h : BHist,
      finiteObservationCofinalitySelectorDecodeBHist
        (finiteObservationCofinalitySelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem finiteObservationCofinalitySelector_mk_congr
    {budget budget' request request' windows windows' dyadic dyadic' regular regular'
      endpoint endpoint' transport transport' continuation continuation' provenance provenance'
      localNameCert localNameCert' : BHist}
    (hBudget : budget' = budget)
    (hRequest : request' = request)
    (hWindows : windows' = windows)
    (hDyadic : dyadic' = dyadic)
    (hRegular : regular' = regular)
    (hSeal : endpoint' = endpoint)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hLocalNameCert : localNameCert' = localNameCert) :
    FiniteObservationCofinalitySelectorUp.mk budget' request' windows' dyadic' regular'
        endpoint' transport' continuation' provenance' localNameCert' =
      FiniteObservationCofinalitySelectorUp.mk budget request windows dyadic regular endpoint
        transport continuation provenance localNameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hBudget
  cases hRequest
  cases hWindows
  cases hDyadic
  cases hRegular
  cases hSeal
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hLocalNameCert
  rfl

def finiteObservationCofinalitySelectorToEventFlow :
    FiniteObservationCofinalitySelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (finiteObservationCofinalitySelectorFields x).map
        finiteObservationCofinalitySelectorEncodeBHist

def finiteObservationCofinalitySelectorFromEventFlow :
    EventFlow → Option FiniteObservationCofinalitySelectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | budget :: rest0 =>
      match rest0 with
      | [] => none
      | request :: rest1 =>
          match rest1 with
          | [] => none
          | windows :: rest2 =>
              match rest2 with
              | [] => none
              | dyadic :: rest3 =>
                  match rest3 with
                  | [] => none
                  | regular :: rest4 =>
                      match rest4 with
                      | [] => none
                      | endpoint :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | continuation :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localNameCert :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (FiniteObservationCofinalitySelectorUp.mk
                                                  (finiteObservationCofinalitySelectorDecodeBHist
                                                    budget)
                                                  (finiteObservationCofinalitySelectorDecodeBHist
                                                    request)
                                                  (finiteObservationCofinalitySelectorDecodeBHist
                                                    windows)
                                                  (finiteObservationCofinalitySelectorDecodeBHist
                                                    dyadic)
                                                  (finiteObservationCofinalitySelectorDecodeBHist
                                                    regular)
                                                  (finiteObservationCofinalitySelectorDecodeBHist
                                                    endpoint)
                                                  (finiteObservationCofinalitySelectorDecodeBHist
                                                    transport)
                                                  (finiteObservationCofinalitySelectorDecodeBHist
                                                    continuation)
                                                  (finiteObservationCofinalitySelectorDecodeBHist
                                                    provenance)
                                                  (finiteObservationCofinalitySelectorDecodeBHist
                                                    localNameCert))
                                          | _ :: _ => none

private theorem finiteObservationCofinalitySelector_round_trip :
    ∀ x : FiniteObservationCofinalitySelectorUp,
      finiteObservationCofinalitySelectorFromEventFlow
        (finiteObservationCofinalitySelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk budget request windows dyadic regular endpoint transport continuation provenance
      localNameCert =>
      exact
        congrArg some
          (finiteObservationCofinalitySelector_mk_congr
            (finiteObservationCofinalitySelectorDecodeEncodeBHist budget)
            (finiteObservationCofinalitySelectorDecodeEncodeBHist request)
            (finiteObservationCofinalitySelectorDecodeEncodeBHist windows)
            (finiteObservationCofinalitySelectorDecodeEncodeBHist dyadic)
            (finiteObservationCofinalitySelectorDecodeEncodeBHist regular)
            (finiteObservationCofinalitySelectorDecodeEncodeBHist endpoint)
            (finiteObservationCofinalitySelectorDecodeEncodeBHist transport)
            (finiteObservationCofinalitySelectorDecodeEncodeBHist continuation)
            (finiteObservationCofinalitySelectorDecodeEncodeBHist provenance)
            (finiteObservationCofinalitySelectorDecodeEncodeBHist localNameCert))

private theorem finiteObservationCofinalitySelectorToEventFlow_injective
    {x y : FiniteObservationCofinalitySelectorUp} :
    finiteObservationCofinalitySelectorToEventFlow x =
      finiteObservationCofinalitySelectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteObservationCofinalitySelectorFromEventFlow
          (finiteObservationCofinalitySelectorToEventFlow x) =
        finiteObservationCofinalitySelectorFromEventFlow
          (finiteObservationCofinalitySelectorToEventFlow y) :=
    congrArg finiteObservationCofinalitySelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteObservationCofinalitySelector_round_trip x).symm
      (Eq.trans hread (finiteObservationCofinalitySelector_round_trip y)))

private theorem finiteObservationCofinalitySelector_field_faithful :
    ∀ x y : FiniteObservationCofinalitySelectorUp,
      finiteObservationCofinalitySelectorFields x =
        finiteObservationCofinalitySelectorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk budget request windows dyadic regular endpoint transport continuation provenance
      localNameCert =>
      cases y with
      | mk budget' request' windows' dyadic' regular' endpoint' transport' continuation'
          provenance' localNameCert' =>
          cases hfields
          rfl

instance finiteObservationCofinalitySelectorBHistCarrier :
    BHistCarrier FiniteObservationCofinalitySelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteObservationCofinalitySelectorToEventFlow
  fromEventFlow := finiteObservationCofinalitySelectorFromEventFlow

instance finiteObservationCofinalitySelectorChapterTasteGate :
    ChapterTasteGate FiniteObservationCofinalitySelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteObservationCofinalitySelectorFromEventFlow
        (finiteObservationCofinalitySelectorToEventFlow x) = some x
    exact finiteObservationCofinalitySelector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteObservationCofinalitySelectorToEventFlow_injective heq)

instance finiteObservationCofinalitySelectorFieldFaithful :
    FieldFaithful FiniteObservationCofinalitySelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteObservationCofinalitySelectorFields
  field_faithful := finiteObservationCofinalitySelector_field_faithful

instance finiteObservationCofinalitySelectorNontrivial :
    Nontrivial FiniteObservationCofinalitySelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteObservationCofinalitySelectorUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      FiniteObservationCofinalitySelectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteObservationCofinalitySelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteObservationCofinalitySelectorChapterTasteGate

theorem FiniteObservationCofinalitySelectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteObservationCofinalitySelectorDecodeBHist
        (finiteObservationCofinalitySelectorEncodeBHist h) = h) ∧
      finiteObservationCofinalitySelectorEncodeBHist (BHist.e0 BHist.Empty) =
        [BMark.b0] ∧
        (∀ x : FiniteObservationCofinalitySelectorUp,
          finiteObservationCofinalitySelectorFromEventFlow
            (finiteObservationCofinalitySelectorToEventFlow x) = some x) ∧
          Nonempty (ChapterTasteGate FiniteObservationCofinalitySelectorUp) ∧
            Nonempty (FieldFaithful FiniteObservationCofinalitySelectorUp) ∧
              Nonempty (Nontrivial FiniteObservationCofinalitySelectorUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨finiteObservationCofinalitySelectorDecodeEncodeBHist, rfl,
      finiteObservationCofinalitySelector_round_trip,
      ⟨finiteObservationCofinalitySelectorChapterTasteGate⟩,
      ⟨finiteObservationCofinalitySelectorFieldFaithful⟩,
      ⟨finiteObservationCofinalitySelectorNontrivial⟩⟩

end BEDC.Derived.FiniteObservationCofinalitySelectorUp.TasteGate

namespace BEDC.Derived.FiniteObservationCofinalitySelectorUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.FiniteObservationCofinalitySelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.FiniteObservationCofinalitySelectorUp
