import BEDC.Derived.RHRoute.HaltingBoundary

namespace BEDC.Derived.RHRoute.CounterexampleSafety

abbrev TraceEvent := BEDC.Derived.RHRoute.HaltingBoundary.TraceEvent

structure CounterexampleCandidate where
  index : Nat
  precision : Nat

inductive SearchOutcome where
  | found : CounterexampleCandidate -> SearchOutcome
  | exhausted : SearchOutcome

inductive CounterAccepted : Bool -> Type where
  | yes : CounterAccepted true

inductive CounterRejected : Bool -> Type where
  | no : CounterRejected false

def acceptedOfEqTrue : {flag : Bool} -> flag = true -> CounterAccepted flag
  | true, _eq => CounterAccepted.yes

def rejectedOfEqFalse : {flag : Bool} -> flag = false -> CounterRejected flag
  | false, _eq => CounterRejected.no

theorem accepted_rejected_disjoint {flag : Bool} :
    CounterAccepted flag -> CounterRejected flag -> False := by
  intro accepted rejected
  cases accepted
  cases rejected

def CounterexampleSearch (acceptsCounter : CounterexampleCandidate -> Bool) :
    Nat -> List CounterexampleCandidate -> SearchOutcome
  | 0, _window => SearchOutcome.exhausted
  | Nat.succ _fuel, [] => SearchOutcome.exhausted
  | Nat.succ fuel, candidate :: rest =>
      match acceptsCounter candidate with
      | true => SearchOutcome.found candidate
      | false => CounterexampleSearch acceptsCounter fuel rest

-- `InFuelWindow candidate fuel window` 记录候选项落在已搜索的有限前缀中。
inductive InFuelWindow :
    CounterexampleCandidate -> Nat -> List CounterexampleCandidate -> Type where
  | here {fuel : Nat} {candidate : CounterexampleCandidate}
      {rest : List CounterexampleCandidate} :
      InFuelWindow candidate (Nat.succ fuel) (candidate :: rest)
  | tail {fuel : Nat} {candidate head : CounterexampleCandidate}
      {rest : List CounterexampleCandidate} :
      InFuelWindow candidate fuel rest ->
        InFuelWindow candidate (Nat.succ fuel) (head :: rest)

def SafetyCert (acceptsCounter : CounterexampleCandidate -> Bool) :
    Nat -> List CounterexampleCandidate -> Type
  | 0, _window => Unit
  | Nat.succ _fuel, [] => Unit
  | Nat.succ fuel, candidate :: rest =>
      Prod (CounterRejected (acceptsCounter candidate))
        (SafetyCert acceptsCounter fuel rest)

def fuelExtend : Nat -> Nat -> Nat
  | fuel, 0 => fuel
  | fuel, Nat.succ extra => Nat.succ (fuelExtend fuel extra)

def search_found_in_fuel {acceptsCounter : CounterexampleCandidate -> Bool} :
    ∀ {fuel : Nat} {window : List CounterexampleCandidate}
      {witness : CounterexampleCandidate},
      CounterexampleSearch acceptsCounter fuel window =
        SearchOutcome.found witness ->
        InFuelWindow witness fuel window
  | 0, _window, _witness, foundEq => by
      cases foundEq
  | Nat.succ _fuel, [], _witness, foundEq => by
      cases foundEq
  | Nat.succ fuel, candidate :: rest, witness, foundEq => by
      unfold CounterexampleSearch at foundEq
      cases acceptedEq : acceptsCounter candidate with
      | true =>
          rw [acceptedEq] at foundEq
          cases foundEq
          exact InFuelWindow.here
      | false =>
          rw [acceptedEq] at foundEq
          exact InFuelWindow.tail (search_found_in_fuel foundEq)

def search_found_accepts {acceptsCounter : CounterexampleCandidate -> Bool} :
    ∀ {fuel : Nat} {window : List CounterexampleCandidate}
      {witness : CounterexampleCandidate},
      CounterexampleSearch acceptsCounter fuel window =
        SearchOutcome.found witness ->
        CounterAccepted (acceptsCounter witness)
  | 0, _window, _witness, foundEq => by
      cases foundEq
  | Nat.succ _fuel, [], _witness, foundEq => by
      cases foundEq
  | Nat.succ fuel, candidate :: rest, witness, foundEq => by
      unfold CounterexampleSearch at foundEq
      cases acceptedEq : acceptsCounter candidate with
      | true =>
          rw [acceptedEq] at foundEq
          cases foundEq
          exact acceptedOfEqTrue acceptedEq
      | false =>
          rw [acceptedEq] at foundEq
          exact search_found_accepts foundEq

theorem search_found_invalidates_cert
    {acceptsCounter : CounterexampleCandidate -> Bool} :
    ∀ {fuel : Nat} {window : List CounterexampleCandidate}
      {witness : CounterexampleCandidate},
      CounterexampleSearch acceptsCounter fuel window =
        SearchOutcome.found witness ->
        SafetyCert acceptsCounter fuel window -> False
  | 0, _window, _witness, foundEq, _cert => by
      cases foundEq
  | Nat.succ _fuel, [], _witness, foundEq, _cert => by
      cases foundEq
  | Nat.succ fuel, candidate :: rest, witness, foundEq, cert => by
      unfold CounterexampleSearch at foundEq
      cases acceptedEq : acceptsCounter candidate with
      | true =>
          rw [acceptedEq] at foundEq
          cases foundEq
          exact accepted_rejected_disjoint
            (acceptedOfEqTrue acceptedEq) cert.fst
      | false =>
          rw [acceptedEq] at foundEq
          exact search_found_invalidates_cert foundEq cert.snd

def search_empty_safety {acceptsCounter : CounterexampleCandidate -> Bool} :
    ∀ {fuel : Nat} {window : List CounterexampleCandidate},
      CounterexampleSearch acceptsCounter fuel window =
        SearchOutcome.exhausted ->
        SafetyCert acceptsCounter fuel window
  | 0, _window, _emptyEq => Unit.unit
  | Nat.succ _fuel, [], _emptyEq => Unit.unit
  | Nat.succ fuel, candidate :: rest, emptyEq => by
      unfold CounterexampleSearch at emptyEq
      cases acceptedEq : acceptsCounter candidate with
      | true =>
          rw [acceptedEq] at emptyEq
          cases emptyEq
      | false =>
          rw [acceptedEq] at emptyEq
          exact Prod.mk (rejectedOfEqFalse acceptedEq)
            (search_empty_safety emptyEq)

structure SearchSound (acceptsCounter : CounterexampleCandidate -> Bool)
    (fuel : Nat) (window : List CounterexampleCandidate) : Type where
  foundInvalid :
    (witness : CounterexampleCandidate) ->
      CounterexampleSearch acceptsCounter fuel window =
        SearchOutcome.found witness ->
        SafetyCert acceptsCounter fuel window -> False
  exhaustedSafe :
    CounterexampleSearch acceptsCounter fuel window =
      SearchOutcome.exhausted ->
      SafetyCert acceptsCounter fuel window

def search_sound
    {acceptsCounter : CounterexampleCandidate -> Bool}
    {fuel : Nat} {window : List CounterexampleCandidate} :
    SearchSound acceptsCounter fuel window where
  foundInvalid := by
    intro witness foundEq cert
    exact search_found_invalidates_cert foundEq cert
  exhaustedSafe := by
    intro emptyEq
    exact search_empty_safety emptyEq

def safety_flow_monotone_succ
    {acceptsCounter : CounterexampleCandidate -> Bool} :
    ∀ {fuel : Nat} {window : List CounterexampleCandidate},
      SafetyCert acceptsCounter (Nat.succ fuel) window ->
        SafetyCert acceptsCounter fuel window
  | 0, _window, _cert => Unit.unit
  | Nat.succ _fuel, [], _cert => Unit.unit
  | Nat.succ _fuel, _candidate :: _rest, cert =>
      Prod.mk cert.fst (safety_flow_monotone_succ cert.snd)

def safety_flow_monotone
    {acceptsCounter : CounterexampleCandidate -> Bool} :
    ∀ {fuel extra : Nat} {window : List CounterexampleCandidate},
      SafetyCert acceptsCounter (fuelExtend fuel extra) window ->
        SafetyCert acceptsCounter fuel window
  | _fuel, 0, _window, cert => cert
  | fuel, Nat.succ extra, window, cert =>
      safety_flow_monotone
        (fuel := fuel)
        (extra := extra)
        (window := window)
        (safety_flow_monotone_succ cert)

end BEDC.Derived.RHRoute.CounterexampleSafety
