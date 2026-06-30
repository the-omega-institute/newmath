import BEDC.Derived.RHRoute.RecursiveTower
import BEDC.Derived.RHRoute.ChannelNormalForm

namespace BEDC.Derived.RHRoute.RouteClosureSeparation

abbrev TraceEvent := BEDC.Derived.RHRoute.RecursiveTower.TraceEvent

-- 有限路由层只记录有限 trace 与显式目标关闭事件。
inductive RouteStep : Type where
  | trace : TraceEvent -> RouteStep
  | closeTarget : Nat -> RouteStep

def natEqBool : Nat -> Nat -> Bool
  | 0, 0 => true
  | 0, Nat.succ _ => false
  | Nat.succ _, 0 => false
  | Nat.succ a, Nat.succ b => natEqBool a b

theorem natEqBool_refl (n : Nat) : natEqBool n n = true := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      exact ih

theorem natEqBool_true_eq {a b : Nat} : natEqBool a b = true -> a = b := by
  intro h
  induction a generalizing b with
  | zero =>
      cases b with
      | zero =>
          rfl
      | succ _ =>
          cases h
  | succ a ih =>
      cases b with
      | zero =>
          cases h
      | succ b =>
          exact congrArg Nat.succ (ih h)

theorem natEqBool_eq_true {a b : Nat} : a = b -> natEqBool a b = true := by
  intro h
  cases h
  exact natEqBool_refl a

theorem natEqBool_false_ne {a b : Nat} : natEqBool a b = false -> a ≠ b := by
  intro h eq
  have ht : natEqBool a b = true := natEqBool_eq_true eq
  rw [ht] at h
  cases h

theorem natEqBool_ne_false {a b : Nat} : a ≠ b -> natEqBool a b = false := by
  intro hne
  induction a generalizing b with
  | zero =>
      cases b with
      | zero =>
          exact False.elim (hne rfl)
      | succ _ =>
          rfl
  | succ a ih =>
      cases b with
      | zero =>
          rfl
      | succ b =>
          exact ih (fun hab => hne (congrArg Nat.succ hab))

def routeStepCloses (target : Nat) : RouteStep -> Bool
  | RouteStep.trace _ => false
  | RouteStep.closeTarget n => natEqBool target n

-- 证书必须指向有限列表中的显式 closeTarget 事件。
inductive RouteClosureCert (target : Nat) : List RouteStep -> Prop where
  | here (tail : List RouteStep) :
      RouteClosureCert target (RouteStep.closeTarget target :: tail)
  | skip (step : RouteStep) {tail : List RouteStep} :
      RouteClosureCert target tail -> RouteClosureCert target (step :: tail)

def routeClosureDecide (target : Nat) : List RouteStep -> Bool
  | [] => false
  | step :: rest =>
      match routeStepCloses target step with
      | true => true
      | false => routeClosureDecide target rest

theorem routeStepCloses_true_cert
    {target : Nat} {step : RouteStep} {tail : List RouteStep} :
    routeStepCloses target step = true ->
      RouteClosureCert target (step :: tail) := by
  intro h
  cases step with
  | trace _ =>
      cases h
  | closeTarget n =>
      unfold routeStepCloses at h
      have htn : target = n := natEqBool_true_eq h
      cases htn
      exact RouteClosureCert.here tail

theorem routeClosureDecide_true_cert {target : Nat} :
    ∀ {steps : List RouteStep},
      routeClosureDecide target steps = true -> RouteClosureCert target steps
  | [], h => by
      cases h
  | step :: rest, h => by
      unfold routeClosureDecide at h
      cases hs : routeStepCloses target step with
      | false =>
          rw [hs] at h
          exact RouteClosureCert.skip step (routeClosureDecide_true_cert h)
      | true =>
          exact routeStepCloses_true_cert (tail := rest) hs

theorem routeClosureDecide_of_cert {target : Nat} {steps : List RouteStep} :
    RouteClosureCert target steps -> routeClosureDecide target steps = true := by
  intro cert
  induction cert with
  | here tail =>
      unfold routeClosureDecide routeStepCloses
      change
        (match natEqBool target target with
        | true => true
        | false => routeClosureDecide target tail) = true
      rw [natEqBool_refl target]
  | skip step cert ih =>
      unfold routeClosureDecide
      cases routeStepCloses target step with
      | false =>
          exact ih
      | true =>
          rfl

theorem routeClosureDecide_false_no_cert
    {target : Nat} {steps : List RouteStep} :
    routeClosureDecide target steps = false -> Not (RouteClosureCert target steps) := by
  intro h cert
  have ht : routeClosureDecide target steps = true := routeClosureDecide_of_cert cert
  rw [ht] at h
  cases h

theorem routeClosureDecide_false_of_no_cert
    {target : Nat} {steps : List RouteStep} :
    Not (RouteClosureCert target steps) -> routeClosureDecide target steps = false := by
  intro hcert
  cases h : routeClosureDecide target steps with
  | false =>
      rfl
  | true =>
      exact False.elim (hcert (routeClosureDecide_true_cert h))

def routeClosureCertDecidable
    (target : Nat) (steps : List RouteStep) :
    Decidable (RouteClosureCert target steps) :=
  match h : routeClosureDecide target steps with
  | true => Decidable.isTrue (routeClosureDecide_true_cert h)
  | false => Decidable.isFalse (routeClosureDecide_false_no_cert h)

def RouteClosureDecisionBoundary : Prop :=
  ∀ target steps,
    (routeClosureDecide target steps = true -> RouteClosureCert target steps) ∧
      (RouteClosureCert target steps -> routeClosureDecide target steps = true) ∧
        (routeClosureDecide target steps = false -> Not (RouteClosureCert target steps)) ∧
          (Not (RouteClosureCert target steps) -> routeClosureDecide target steps = false)

theorem finite_route_closure_decidable_boundary :
    RouteClosureDecisionBoundary := by
  intro target steps
  constructor
  · exact routeClosureDecide_true_cert
  · constructor
    · exact routeClosureDecide_of_cert
    · constructor
      · exact routeClosureDecide_false_no_cert
      · exact routeClosureDecide_false_of_no_cert

structure FixedStatement (α : Type u) where
  target : α
  predicate : α -> Prop

def FixedStatement.Holds {α : Type u} (statement : FixedStatement α) : Prop :=
  statement.predicate statement.target

def RouteClosureToFixedUniform : Prop :=
  ∀ (statement : FixedStatement Nat) (target : Nat) (steps : List RouteStep),
    RouteClosureCert target steps -> statement.Holds

def FixedToRouteClosureUniform : Prop :=
  ∀ (statement : FixedStatement Nat) (target : Nat) (steps : List RouteStep),
    statement.Holds -> RouteClosureCert target steps

def closedZeroRoute : List RouteStep :=
  [RouteStep.closeTarget 0]

theorem closedZeroRoute_has_cert : RouteClosureCert 0 closedZeroRoute :=
  RouteClosureCert.here []

theorem emptyRoute_has_no_cert : Not (RouteClosureCert 0 []) := by
  intro cert
  cases cert

theorem route_closure_not_fixed_statement_uniform :
    Not RouteClosureToFixedUniform := by
  intro h
  let impossibleStatement : FixedStatement Nat :=
    { target := 0, predicate := fun _ => False }
  exact h impossibleStatement 0 closedZeroRoute closedZeroRoute_has_cert

theorem fixed_statement_not_route_closure_uniform :
    Not FixedToRouteClosureUniform := by
  intro h
  let reflexiveStatement : FixedStatement Nat :=
    { target := 0, predicate := fun n => n = n }
  have holds : reflexiveStatement.Holds := rfl
  exact emptyRoute_has_no_cert (h reflexiveStatement 0 [] holds)

theorem route_closure_fixed_statement_separation :
    RouteClosureDecisionBoundary ∧
      Not RouteClosureToFixedUniform ∧
        Not FixedToRouteClosureUniform := by
  constructor
  · exact finite_route_closure_decidable_boundary
  · constructor
    · exact route_closure_not_fixed_statement_uniform
    · exact fixed_statement_not_route_closure_uniform

end BEDC.Derived.RHRoute.RouteClosureSeparation
