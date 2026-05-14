import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FableMachineBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FableMachineBoundaryUp : Type where
  | mk :
      (history emptyBoundary ledger selector witness clock transport route provenance name :
        BHist) →
      FableMachineBoundaryUp
  deriving DecidableEq

def fableMachineBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fableMachineBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fableMachineBoundaryEncodeBHist h

def fableMachineBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fableMachineBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fableMachineBoundaryDecodeBHist tail)

private theorem fableMachineBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem fableMachineBoundary_mk_congr
    {history history' emptyBoundary emptyBoundary' ledger ledger' selector selector'
      witness witness' clock clock' transport transport' route route'
      provenance provenance' name name' : BHist}
    (hHistory : history' = history)
    (hEmptyBoundary : emptyBoundary' = emptyBoundary)
    (hLedger : ledger' = ledger)
    (hSelector : selector' = selector)
    (hWitness : witness' = witness)
    (hClock : clock' = clock)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    FableMachineBoundaryUp.mk history' emptyBoundary' ledger' selector' witness' clock'
        transport' route' provenance' name' =
      FableMachineBoundaryUp.mk history emptyBoundary ledger selector witness clock transport
        route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hHistory
  cases hEmptyBoundary
  cases hLedger
  cases hSelector
  cases hWitness
  cases hClock
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def fableMachineBoundaryToEventFlow : FableMachineBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FableMachineBoundaryUp.mk history emptyBoundary ledger selector witness clock transport
      route provenance name =>
      [[BMark.b0],
        fableMachineBoundaryEncodeBHist history,
        [BMark.b1, BMark.b0],
        fableMachineBoundaryEncodeBHist emptyBoundary,
        [BMark.b1, BMark.b1, BMark.b0],
        fableMachineBoundaryEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fableMachineBoundaryEncodeBHist selector,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fableMachineBoundaryEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fableMachineBoundaryEncodeBHist clock,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        fableMachineBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        fableMachineBoundaryEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        fableMachineBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fableMachineBoundaryEncodeBHist name]

def fableMachineBoundaryFromEventFlow :
    EventFlow → Option FableMachineBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | history :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | emptyBoundary :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | ledger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | selector :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | witness :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | clock :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | route :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | name :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (FableMachineBoundaryUp.mk
                                                                                          (fableMachineBoundaryDecodeBHist history)
                                                                                          (fableMachineBoundaryDecodeBHist emptyBoundary)
                                                                                          (fableMachineBoundaryDecodeBHist ledger)
                                                                                          (fableMachineBoundaryDecodeBHist selector)
                                                                                          (fableMachineBoundaryDecodeBHist witness)
                                                                                          (fableMachineBoundaryDecodeBHist clock)
                                                                                          (fableMachineBoundaryDecodeBHist transport)
                                                                                          (fableMachineBoundaryDecodeBHist route)
                                                                                          (fableMachineBoundaryDecodeBHist provenance)
                                                                                          (fableMachineBoundaryDecodeBHist name))
                                                                                  | _ :: _ => none

private theorem fableMachineBoundary_round_trip :
    ∀ x : FableMachineBoundaryUp,
      fableMachineBoundaryFromEventFlow (fableMachineBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk history emptyBoundary ledger selector witness clock transport route provenance name =>
      change
        some
          (FableMachineBoundaryUp.mk
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist history))
            (fableMachineBoundaryDecodeBHist
              (fableMachineBoundaryEncodeBHist emptyBoundary))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist ledger))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist selector))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist witness))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist clock))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist transport))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist route))
            (fableMachineBoundaryDecodeBHist
              (fableMachineBoundaryEncodeBHist provenance))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist name))) =
          some
            (FableMachineBoundaryUp.mk history emptyBoundary ledger selector witness clock
              transport route provenance name)
      exact
        congrArg some
          (fableMachineBoundary_mk_congr
            (fableMachineBoundaryDecode_encode_bhist history)
            (fableMachineBoundaryDecode_encode_bhist emptyBoundary)
            (fableMachineBoundaryDecode_encode_bhist ledger)
            (fableMachineBoundaryDecode_encode_bhist selector)
            (fableMachineBoundaryDecode_encode_bhist witness)
            (fableMachineBoundaryDecode_encode_bhist clock)
            (fableMachineBoundaryDecode_encode_bhist transport)
            (fableMachineBoundaryDecode_encode_bhist route)
            (fableMachineBoundaryDecode_encode_bhist provenance)
            (fableMachineBoundaryDecode_encode_bhist name))

private theorem fableMachineBoundaryToEventFlow_injective
    {x y : FableMachineBoundaryUp} :
    fableMachineBoundaryToEventFlow x = fableMachineBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fableMachineBoundaryFromEventFlow (fableMachineBoundaryToEventFlow x) =
        fableMachineBoundaryFromEventFlow (fableMachineBoundaryToEventFlow y) :=
    congrArg fableMachineBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fableMachineBoundary_round_trip x).symm
      (Eq.trans hread (fableMachineBoundary_round_trip y)))

instance fableMachineBoundaryBHistCarrier : BHistCarrier FableMachineBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fableMachineBoundaryToEventFlow
  fromEventFlow := fableMachineBoundaryFromEventFlow

instance fableMachineBoundaryChapterTasteGate :
    ChapterTasteGate FableMachineBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fableMachineBoundaryFromEventFlow (fableMachineBoundaryToEventFlow x) = some x
    exact fableMachineBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fableMachineBoundaryToEventFlow_injective heq)

instance fableMachineBoundaryFieldFaithful : FieldFaithful FableMachineBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | FableMachineBoundaryUp.mk history emptyBoundary ledger selector witness clock
        transport route provenance name =>
        [history, emptyBoundary, ledger, selector, witness, clock, transport, route,
          provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk history₁ emptyBoundary₁ ledger₁ selector₁ witness₁ clock₁ transport₁ route₁
        provenance₁ name₁ =>
        cases y with
        | mk history₂ emptyBoundary₂ ledger₂ selector₂ witness₂ clock₂ transport₂ route₂
            provenance₂ name₂ =>
            simp only [] at h
            injection h with hHistory hRest₁
            injection hRest₁ with hEmptyBoundary hRest₂
            injection hRest₂ with hLedger hRest₃
            injection hRest₃ with hSelector hRest₄
            injection hRest₄ with hWitness hRest₅
            injection hRest₅ with hClock hRest₆
            injection hRest₆ with hTransport hRest₇
            injection hRest₇ with hRoute hRest₈
            injection hRest₈ with hProvenance hRest₉
            injection hRest₉ with hName _
            subst hHistory
            subst hEmptyBoundary
            subst hLedger
            subst hSelector
            subst hWitness
            subst hClock
            subst hTransport
            subst hRoute
            subst hProvenance
            subst hName
            rfl

theorem FableMachineBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist h) = h) ∧
      (∀ x : FableMachineBoundaryUp,
        fableMachineBoundaryFromEventFlow (fableMachineBoundaryToEventFlow x) = some x) ∧
        (∀ x y : FableMachineBoundaryUp,
          fableMachineBoundaryToEventFlow x = fableMachineBoundaryToEventFlow y → x = y) ∧
          fableMachineBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact fableMachineBoundaryDecode_encode_bhist
  · constructor
    · exact fableMachineBoundary_round_trip
    · constructor
      · intro x y heq
        exact fableMachineBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.FableMachineBoundaryUp
