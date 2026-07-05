namespace BEDC.Derived.RHRoute.NewmanUnitCriterion

universe u

inductive Reaches {α : Type u} (step : α → α → Prop) : α → α → Prop where
  | refl (a : α) : Reaches step a a
  | tail {a b c : α} : step a b → Reaches step b c → Reaches step a c

def NormalForm {α : Type u} (step : α → α → Prop) (a : α) : Prop :=
  ∀ b : α, step a b → False

def Joinable {α : Type u} (step : α → α → Prop) (a b : α) : Prop :=
  ∃ c : α, Reaches step a c ∧ Reaches step b c

def LocalConfluent {α : Type u} (step : α → α → Prop) : Prop :=
  ∀ {a b c : α}, step a b → step a c → Joinable step b c

def Confluent {α : Type u} (step : α → α → Prop) : Prop :=
  ∀ {a b c : α}, Reaches step a b → Reaches step a c → Joinable step b c

def InvStep {α : Type u} (step : α → α → Prop) (next current : α) : Prop :=
  step current next

def Terminates {α : Type u} (step : α → α → Prop) : Prop :=
  ∀ a : α, Acc (InvStep step) a

def Normalizing {α : Type u} (step : α → α → Prop) : Prop :=
  ∀ a : α, ∃ n : α, Reaches step a n ∧ NormalForm step n

def HasUniqueNormalForm {α : Type u} (step : α → α → Prop) (a : α) : Prop :=
  ∃ n : α,
    Reaches step a n ∧
      NormalForm step n ∧
        ∀ m : α, Reaches step a m → NormalForm step m → m = n

structure DescentSelector {α : Type u} (step : α → α → Prop) where
  next : α → Option α
  next_step : ∀ {a b : α}, next a = some b → step a b
  none_normal : ∀ {a : α}, next a = none → NormalForm step a

namespace Reaches

theorem single {α : Type u} {step : α → α → Prop} {a b : α}
    (h : step a b) : Reaches step a b :=
  Reaches.tail h (Reaches.refl b)

theorem trans {α : Type u} {step : α → α → Prop} :
    ∀ {a b c : α}, Reaches step a b → Reaches step b c → Reaches step a c := by
  intro a b c hab hbc
  induction hab with
  | refl _ =>
      exact hbc
  | tail hstep htail ih =>
      exact Reaches.tail hstep (ih hbc)

theorem eq_of_normal_left {α : Type u} {step : α → α → Prop}
    {a b : α} (hreach : Reaches step a b) (hnormal : NormalForm step a) :
    a = b := by
  cases hreach with
  | refl _ =>
      rfl
  | tail hstep _ =>
      exact False.elim (hnormal _ hstep)

end Reaches

private theorem newman_confluence_acc {α : Type u} {step : α → α → Prop}
    (hlocal : LocalConfluent step) {a : α} (ha : Acc (InvStep step) a) :
    ∀ {b c : α}, Reaches step a b → Reaches step a c → Joinable step b c := by
  induction ha with
  | intro x _children ih =>
      intro b c hxb hxc
      cases hxb with
      | refl _ =>
          exact ⟨c, hxc, Reaches.refl c⟩
      | tail hxy hyb =>
          cases hxc with
          | refl _ =>
              exact ⟨b, Reaches.refl b, Reaches.tail hxy hyb⟩
          | tail hxz hzc =>
              obtain ⟨j, hyj, hzj⟩ := hlocal hxy hxz
              obtain ⟨m, hjm, hcm⟩ := ih _ hxz hzj hzc
              obtain ⟨d, hbd, hmd⟩ := ih _ hxy hyb (Reaches.trans hyj hjm)
              exact ⟨d, hbd, Reaches.trans hcm hmd⟩

theorem newman_confluence {α : Type u} {step : α → α → Prop}
    (hterm : Terminates step) (hlocal : LocalConfluent step) :
    Confluent step := by
  intro a b c hab hac
  exact newman_confluence_acc hlocal (hterm a) hab hac

theorem normal_forms_equal_of_confluent {α : Type u} {step : α → α → Prop}
    (hconf : Confluent step) {a n m : α}
    (han : Reaches step a n) (ham : Reaches step a m)
    (hn : NormalForm step n) (hm : NormalForm step m) :
    n = m := by
  obtain ⟨d, hnd, hmd⟩ := hconf han ham
  have hndEq : n = d := Reaches.eq_of_normal_left hnd hn
  have hmdEq : m = d := Reaches.eq_of_normal_left hmd hm
  exact Eq.trans hndEq hmdEq.symm

theorem normalizing_of_descent_selector {α : Type u} {step : α → α → Prop}
    (hterm : Terminates step) (selector : DescentSelector step) :
    Normalizing step := by
  intro a
  induction hterm a with
  | intro x _children ih =>
      cases hnext : selector.next x with
      | none =>
          exact ⟨x, Reaches.refl x, selector.none_normal hnext⟩
      | some y =>
          have hxy : step x y := selector.next_step hnext
          obtain ⟨n, hyn, hnormal⟩ := ih y hxy
          exact ⟨n, Reaches.tail hxy hyn, hnormal⟩

theorem newman_unit_criterion {α : Type u} {step : α → α → Prop}
    (hterm : Terminates step) (hnorm : Normalizing step)
    (hlocal : LocalConfluent step) :
    ∀ a : α, HasUniqueNormalForm step a := by
  intro a
  obtain ⟨n, han, hnormal⟩ := hnorm a
  have hconf : Confluent step := newman_confluence hterm hlocal
  exact
    ⟨n, han, hnormal, by
      intro m ham hm
      exact normal_forms_equal_of_confluent hconf ham han hm hnormal⟩

theorem newman_unit_criterion_of_descent_selector
    {α : Type u} {step : α → α → Prop}
    (hterm : Terminates step) (selector : DescentSelector step)
    (hlocal : LocalConfluent step) :
    ∀ a : α, HasUniqueNormalForm step a := by
  exact
    newman_unit_criterion hterm
      (normalizing_of_descent_selector hterm selector) hlocal

end BEDC.Derived.RHRoute.NewmanUnitCriterion
