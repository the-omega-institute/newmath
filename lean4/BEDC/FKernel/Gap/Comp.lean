import BEDC.FKernel.Gap.Core

namespace BEDC.FKernel.Gap

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ext
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Sig

variable [AskSetup] [PackageSetup] [G : DomainSetup]
def CompGap {Source Inter Final : Type}
    (firstGap : Inter → Source → Prop)
    (secondGap : Final → Inter → Prop)
    (z : Final) (x : Source) : Prop :=
  ∃ y : Inter, firstGap y x ∧ secondGap z y

theorem compGap_iff_exists
    {Source Inter Final : Type}
    {firstGap : Inter -> Source -> Prop}
    {secondGap : Final -> Inter -> Prop}
    {z : Final} {x : Source} :
    CompGap firstGap secondGap z x <->
      exists y : Inter, firstGap y x /\ secondGap z y := by
  rfl

theorem compGap_intro
    {Source Inter Final : Type}
    {firstGap : Inter -> Source -> Prop}
    {secondGap : Final -> Inter -> Prop}
    {z : Final} {x : Source} {y : Inter} :
    firstGap y x -> secondGap z y -> CompGap firstGap secondGap z x := by
  intro hfirst hsecond
  exact Exists.intro y (And.intro hfirst hsecond)

theorem compGap_inversion
    {Source Inter Final : Type}
    {firstGap : Inter -> Source -> Prop}
    {secondGap : Final -> Inter -> Prop}
    {z : Final} {x : Source} :
    CompGap firstGap secondGap z x ->
      exists y : Inter, firstGap y x /\ secondGap z y := by
  intro h
  exact h

theorem composite_gap_ledger_witnesses
    {Source Inter Final : Type}
    {firstGap : Inter → Source → Prop}
    {secondGap : Final → Inter → Prop}
    {z : Final} {x : Source} :
    CompGap firstGap secondGap z x → ∃ y : Inter, firstGap y x ∧ secondGap z y := by
  intro h
  exact h

theorem ledger_composition_principle
    {A B C D : Type} {first : B → A → Prop} {second : C → B → Prop}
    {third : D → C → Prop} {z : D} {x : A} :
    CompGap (fun c a => CompGap first second c a) third z x →
      ∃ b : B, ∃ c : C, first b x ∧ second c b ∧ third z c := by
  intro h
  cases h with
  | intro c outer =>
      cases outer with
      | intro inner hthird =>
          cases inner with
          | intro b firstSecond =>
              cases firstSecond with
              | intro hfirst hsecond =>
                  exact Exists.intro b
                    (Exists.intro c
                      (And.intro hfirst
                        (And.intro hsecond hthird)))

theorem ledger_composition_principle_inverse
    {A B C D : Type} {first : B -> A -> Prop} {second : C -> B -> Prop}
    {third : D -> C -> Prop} {z : D} {x : A} :
    (exists b : B, exists c : C, first b x /\ second c b /\ third z c) ->
      CompGap (fun c a => CompGap first second c a) third z x := by
  intro witnesses
  cases witnesses with
  | intro b rest =>
      cases rest with
      | intro c data =>
          cases data with
          | intro hfirst tail =>
              cases tail with
              | intro hsecond hthird =>
                  exact Exists.intro c
                    (And.intro
                      (Exists.intro b (And.intro hfirst hsecond))
                      hthird)

theorem compGap_left_witness
    {Source Inter Final : Type}
    {firstGap : Inter → Source → Prop}
    {secondGap : Final → Inter → Prop}
    {z : Final} {x : Source} :
    CompGap firstGap secondGap z x → ∃ y : Inter, firstGap y x := by
  intro h
  cases h with
  | intro y data =>
      exact Exists.intro y data.left

theorem compGap_right_witness
    {Source Inter Final : Type}
    {firstGap : Inter → Source → Prop}
    {secondGap : Final → Inter → Prop}
    {z : Final} {x : Source} :
    CompGap firstGap secondGap z x → ∃ y : Inter, secondGap z y := by
  intro h
  cases h with
  | intro y data =>
      exact Exists.intro y data.right
end BEDC.FKernel.Gap
