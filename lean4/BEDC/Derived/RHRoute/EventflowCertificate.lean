import BEDC.Derived.RHRoute.RecursiveTower
import BEDC.Derived.RHRoute.UnitaryBalance

namespace BEDC.Derived.RHRoute.EventflowCertificate

open BEDC.Derived.RHRoute.RecursiveTower
open BEDC.Derived.RHRoute.UnitaryBalance
open BEDC.Derived.RationalUp

universe u

structure EventflowStep (α : Type u) (P : α -> Prop) where
  source : α
  target : α
  events : List TraceEvent
  inherit_cert : P source -> P target

namespace EventflowStep

def certifiedReturn {α : Type u} {P : α -> Prop}
    (step : EventflowStep α P) (sourceCert : P step.source) :
    CertifiedReturn α P :=
  { value := step.target
    cert := step.inherit_cert sourceCert
    trace := step.events }

theorem certifiedReturn_sound {α : Type u} {P : α -> Prop}
    (step : EventflowStep α P) (sourceCert : P step.source) :
    P (step.certifiedReturn sourceCert).value :=
  (step.certifiedReturn sourceCert).cert

end EventflowStep

inductive FlowLinked {α : Type u} {P : α -> Prop} :
    α -> List (EventflowStep α P) -> Prop where
  | nil {seed : α} : FlowLinked seed []
  | cons {current : α} {step : EventflowStep α P}
      {rest : List (EventflowStep α P)} :
      step.source = current -> FlowLinked step.target rest ->
        FlowLinked current (step :: rest)

def flowTarget {α : Type u} {P : α -> Prop} :
    α -> List (EventflowStep α P) -> α
  | seed, [] => seed
  | _seed, step :: rest => flowTarget step.target rest

def flowTrace {α : Type u} {P : α -> Prop} :
    List (EventflowStep α P) -> List TraceEvent
  | [] => []
  | step :: rest => step.events ++ flowTrace rest

def flowCert {α : Type u} {P : α -> Prop} :
    {seed : α} -> {steps : List (EventflowStep α P)} ->
      P seed -> FlowLinked (P := P) seed steps -> P (flowTarget seed steps)
  | _seed, [], seedCert, FlowLinked.nil => seedCert
  | _seed, step :: rest, seedCert, linked => by
      cases linked with
      | cons sourceEq restLinked =>
          have sourceCert : P step.source := sourceEq.symm ▸ seedCert
          exact flowCert (seed := step.target) (steps := rest)
            (step.inherit_cert sourceCert) restLinked

structure CertificateFlow (α : Type u) (P : α -> Prop) where
  seed : α
  seed_cert : P seed
  steps : List (EventflowStep α P)
  linked : FlowLinked (P := P) seed steps

def flowCertifiedReturn {α : Type u} {P : α -> Prop}
    (flow : CertificateFlow α P) : CertifiedReturn α P :=
  { value := flowTarget flow.seed flow.steps
    cert := flowCert flow.seed_cert flow.linked
    trace := flowTrace flow.steps }

theorem flow_certificate_sound {α : Type u} {P : α -> Prop}
    (flow : CertificateFlow α P) :
    P (flowCertifiedReturn flow).value :=
  (flowCertifiedReturn flow).cert

theorem flow_certificate_trace {α : Type u} {P : α -> Prop}
    (flow : CertificateFlow α P) :
    (flowCertifiedReturn flow).trace = flowTrace flow.steps :=
  rfl

structure SkewBalanceRow where
  left_weight : RatNum
  right_weight : RatNum

def rowSkew (row : SkewBalanceRow) : RatNum :=
  ratAdd row.left_weight (ratNeg row.right_weight)

def finiteBalanceSkew (rows : List SkewBalanceRow) : RatNum :=
  ratListSum (List.map rowSkew rows)

def zero_skew (rows : List SkewBalanceRow) : Prop :=
  RatEq (finiteBalanceSkew rows) ratZero

abbrev ZeroSkewState := List SkewBalanceRow

abbrev ZeroSkewFlow := CertificateFlow ZeroSkewState zero_skew

def zero_skew_eventflow (flow : ZeroSkewFlow) :
    CertifiedReturn ZeroSkewState zero_skew :=
  flowCertifiedReturn flow

theorem zero_skew_eventflow_sound (flow : ZeroSkewFlow) :
    zero_skew (zero_skew_eventflow flow).value :=
  (zero_skew_eventflow flow).cert

theorem zero_skew_is_finite_balance_equation
    {rows : List SkewBalanceRow} :
    zero_skew rows -> RatEq (finiteBalanceSkew rows) ratZero := by
  intro rowsZero
  exact rowsZero

theorem zero_skew_nil : zero_skew [] := by
  unfold zero_skew finiteBalanceSkew
  exact RatEq_refl ratZero

end BEDC.Derived.RHRoute.EventflowCertificate
