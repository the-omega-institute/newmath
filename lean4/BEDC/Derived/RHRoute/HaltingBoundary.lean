import BEDC.Derived.RHRoute.RecursiveTower

namespace BEDC.Derived.RHRoute.HaltingBoundary

universe u v

abbrev TraceEvent := BEDC.Derived.RHRoute.RecursiveTower.TraceEvent

-- 有限路由步只给出下一状态或当前有限步的终止结果。
inductive RouteStep (State : Type u) (Result : Type v) where
  | advance : TraceEvent -> State -> RouteStep State Result
  | terminate : TraceEvent -> Result -> RouteStep State Result

inductive RunStatus (State : Type u) (Result : Type v) where
  | running : State -> RunStatus State Result
  | halted : Result -> RunStatus State Result

structure FuelBoundedRoute (State : Type u) (Result : Type v) where
  step : State -> RouteStep State Result

structure FuelRun (State : Type u) (Result : Type v) where
  status : RunStatus State Result
  trace : List TraceEvent

def runStatus {State : Type u} {Result : Type v}
    (route : FuelBoundedRoute State Result) :
    Nat -> State -> RunStatus State Result
  | 0, seed => RunStatus.running seed
  | Nat.succ fuel, seed =>
      match route.step seed with
      | RouteStep.advance _ next => runStatus route fuel next
      | RouteStep.terminate _ result => RunStatus.halted result

def runTrace {State : Type u} {Result : Type v}
    (route : FuelBoundedRoute State Result) :
    Nat -> State -> List TraceEvent
  | 0, _seed => []
  | Nat.succ fuel, seed =>
      match route.step seed with
      | RouteStep.advance event next => event :: runTrace route fuel next
      | RouteStep.terminate event _result => [event]

def runWithFuel {State : Type u} {Result : Type v}
    (route : FuelBoundedRoute State Result) (fuel : Nat) (seed : State) :
    FuelRun State Result :=
  {
    status := runStatus route fuel seed
    trace := runTrace route fuel seed
  }

def Halts {State : Type u} {Result : Type v}
    (route : FuelBoundedRoute State Result) (seed : State) (fuel : Nat) :
    Prop :=
  ∃ result, runStatus route fuel seed = RunStatus.halted result

-- 这是 fuel 层的仍在运行，不是无界不终止断言。
def StillRunningAtFuel {State : Type u} {Result : Type v}
    (route : FuelBoundedRoute State Result) (seed : State) (fuel : Nat) :
    Prop :=
  ∃ state, runStatus route fuel seed = RunStatus.running state

def haltsBool {State : Type u} {Result : Type v}
    (route : FuelBoundedRoute State Result) (seed : State) (fuel : Nat) :
    Bool :=
  match runStatus route fuel seed with
  | RunStatus.halted _ => true
  | RunStatus.running _ => false

def stillRunningBool {State : Type u} {Result : Type v}
    (route : FuelBoundedRoute State Result) (seed : State) (fuel : Nat) :
    Bool :=
  match runStatus route fuel seed with
  | RunStatus.halted _ => false
  | RunStatus.running _ => true

def haltsDecidable {State : Type u} {Result : Type v}
    (route : FuelBoundedRoute State Result) (seed : State) (fuel : Nat) :
    Decidable (Halts route seed fuel) :=
  match h : runStatus route fuel seed with
  | RunStatus.halted result => Decidable.isTrue ⟨result, h⟩
  | RunStatus.running _state =>
      Decidable.isFalse (by
        intro halted
        cases halted with
        | intro result resultEq =>
            rw [h] at resultEq
            cases resultEq)

def stillRunningDecidable {State : Type u} {Result : Type v}
    (route : FuelBoundedRoute State Result) (seed : State) (fuel : Nat) :
    Decidable (StillRunningAtFuel route seed fuel) :=
  match h : runStatus route fuel seed with
  | RunStatus.halted _result =>
      Decidable.isFalse (by
        intro running
        cases running with
        | intro state stateEq =>
            rw [h] at stateEq
            cases stateEq)
  | RunStatus.running state => Decidable.isTrue ⟨state, h⟩

theorem haltsBool_true_halts {State : Type u} {Result : Type v}
    {route : FuelBoundedRoute State Result} {seed : State} {fuel : Nat} :
    haltsBool route seed fuel = true -> Halts route seed fuel := by
  intro h
  unfold haltsBool at h
  cases statusEq : runStatus route fuel seed with
  | halted result =>
      exact ⟨result, statusEq⟩
  | running _state =>
      rw [statusEq] at h
      cases h

theorem haltsBool_of_halts {State : Type u} {Result : Type v}
    {route : FuelBoundedRoute State Result} {seed : State} {fuel : Nat} :
    Halts route seed fuel -> haltsBool route seed fuel = true := by
  intro halted
  cases halted with
  | intro result resultEq =>
      unfold haltsBool
      rw [resultEq]

theorem stillRunningBool_true_running {State : Type u} {Result : Type v}
    {route : FuelBoundedRoute State Result} {seed : State} {fuel : Nat} :
    stillRunningBool route seed fuel = true ->
      StillRunningAtFuel route seed fuel := by
  intro h
  unfold stillRunningBool at h
  cases statusEq : runStatus route fuel seed with
  | halted _result =>
      rw [statusEq] at h
      cases h
  | running state =>
      exact ⟨state, statusEq⟩

theorem stillRunningBool_of_running {State : Type u} {Result : Type v}
    {route : FuelBoundedRoute State Result} {seed : State} {fuel : Nat} :
    StillRunningAtFuel route seed fuel ->
      stillRunningBool route seed fuel = true := by
  intro running
  cases running with
  | intro state stateEq =>
      unfold stillRunningBool
      rw [stateEq]

theorem halting_timeout_disjoint {State : Type u} {Result : Type v}
    {route : FuelBoundedRoute State Result} {seed : State} {fuel : Nat} :
    Halts route seed fuel -> StillRunningAtFuel route seed fuel -> False := by
  intro halted running
  cases halted with
  | intro result resultEq =>
      cases running with
      | intro state stateEq =>
          rw [stateEq] at resultEq
          cases resultEq

theorem fuel_status_exhaustive {State : Type u} {Result : Type v}
    (route : FuelBoundedRoute State Result) (seed : State) (fuel : Nat) :
    Halts route seed fuel ∨ StillRunningAtFuel route seed fuel := by
  cases statusEq : runStatus route fuel seed with
  | halted result =>
      exact Or.inl ⟨result, statusEq⟩
  | running state =>
      exact Or.inr ⟨state, statusEq⟩

theorem halting_monotone_succ {State : Type u} {Result : Type v}
    (route : FuelBoundedRoute State Result) :
    ∀ (fuel : Nat) (seed : State) (result : Result),
      runStatus route fuel seed = RunStatus.halted result ->
        runStatus route (Nat.succ fuel) seed = RunStatus.halted result
  | 0, _seed, _result, haltedAtZero => by
      cases haltedAtZero
  | Nat.succ fuel, seed, result, haltedAtFuel => by
      unfold runStatus at haltedAtFuel ⊢
      cases stepEq : route.step seed with
      | advance _event next =>
          rw [stepEq] at haltedAtFuel
          exact halting_monotone_succ route fuel next result haltedAtFuel
      | terminate _event stopped =>
          rw [stepEq] at haltedAtFuel
          cases haltedAtFuel
          rfl

theorem halting_monotone_result {State : Type u} {Result : Type v}
    (route : FuelBoundedRoute State Result) (fuel extra : Nat)
    (seed : State) (result : Result) :
    runStatus route fuel seed = RunStatus.halted result ->
      runStatus route (fuel + extra) seed = RunStatus.halted result := by
  intro haltedAtFuel
  induction extra with
  | zero =>
      exact haltedAtFuel
  | succ extra ih =>
      change
        runStatus route (Nat.succ (fuel + extra)) seed =
          RunStatus.halted result
      exact halting_monotone_succ route (fuel + extra) seed result ih

theorem halting_monotone {State : Type u} {Result : Type v}
    (route : FuelBoundedRoute State Result) (seed : State)
    (fuel extra : Nat) :
    Halts route seed fuel -> Halts route seed (fuel + extra) := by
  intro halted
  cases halted with
  | intro result resultEq =>
      exact ⟨result,
        halting_monotone_result route fuel extra seed result resultEq⟩

theorem halted_result_unique {State : Type u} {Result : Type v}
    {route : FuelBoundedRoute State Result} {seed : State} {fuel : Nat}
    {left right : Result} :
    runStatus route fuel seed = RunStatus.halted left ->
      runStatus route fuel seed = RunStatus.halted right ->
        left = right := by
  intro leftEq rightEq
  rw [leftEq] at rightEq
  cases rightEq
  rfl

theorem boundary {State : Type u} {Result : Type v}
    (route : FuelBoundedRoute State Result) (seed : State) (fuel : Nat) :
    (Halts route seed fuel ∨ StillRunningAtFuel route seed fuel) ∧
      (Halts route seed fuel -> StillRunningAtFuel route seed fuel -> False) := by
  constructor
  · exact fuel_status_exhaustive route seed fuel
  · exact halting_timeout_disjoint

theorem fuel_halting_boundary {State : Type u} {Result : Type v}
    (route : FuelBoundedRoute State Result) (seed : State) (fuel : Nat) :
    (Halts route seed fuel ∨ StillRunningAtFuel route seed fuel) ∧
      (Halts route seed fuel -> StillRunningAtFuel route seed fuel -> False) :=
  boundary route seed fuel

end BEDC.Derived.RHRoute.HaltingBoundary
