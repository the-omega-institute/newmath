import BEDC.FKernel.Gap.Comp

namespace BEDC.FKernel.Gap

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ext
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Sig

variable [AskSetup] [PackageSetup] [G : DomainSetup]
theorem compGap_assoc
    {A B C D : Type}
    {first : B → A → Prop}
    {second : C → B → Prop}
    {third : D → C → Prop}
    {z : D} {x : A} :
    CompGap (fun c a => CompGap first second c a) third z x ↔
      CompGap first (fun z b => CompGap second third z b) z x := by
  constructor
  · intro left
    cases left with
    | intro c cData =>
        cases cData with
        | intro firstSecond thirdWitness =>
            cases firstSecond with
            | intro b bData =>
                cases bData with
                | intro firstWitness secondWitness =>
                    exact Exists.intro b
                      (And.intro firstWitness
                        (Exists.intro c (And.intro secondWitness thirdWitness)))
  · intro right
    cases right with
    | intro b bData =>
        cases bData with
        | intro firstWitness secondThird =>
            cases secondThird with
            | intro c cData =>
                cases cData with
                | intro secondWitness thirdWitness =>
                    exact Exists.intro c
                      (And.intro
                        (Exists.intro b (And.intro firstWitness secondWitness))
                        thirdWitness)

theorem compGap_assoc_forward
    {A B C Final : Type}
    {first : B → A → Prop}
    {second : C → B → Prop}
    {third : Final → C → Prop}
    {z : Final} {x : A} :
    CompGap (fun c a => CompGap first second c a) third z x →
      CompGap first (fun z b => CompGap second third z b) z x := by
  intro left
  cases left with
  | intro c cData =>
      cases cData with
      | intro firstSecond thirdWitness =>
          cases firstSecond with
          | intro b bData =>
              cases bData with
              | intro firstWitness secondWitness =>
                  exact Exists.intro b
                    (And.intro firstWitness
                      (Exists.intro c (And.intro secondWitness thirdWitness)))

theorem compGap_right_nested_witnesses
    {Source Inter Final Top : Type}
    {firstGap : Inter -> Source -> Prop}
    {secondGap : Final -> Inter -> Prop}
    {thirdGap : Top -> Final -> Prop}
    {z : Top} {x : Source} :
    CompGap firstGap (CompGap secondGap thirdGap) z x ->
      exists y : Inter, exists w : Final,
        firstGap y x /\ secondGap w y /\ thirdGap z w := by
  intro h
  cases h with
  | intro y outer =>
      cases outer with
      | intro firstWitness nested =>
          cases nested with
          | intro w nestedData =>
              cases nestedData with
              | intro secondWitness thirdWitness =>
                  exact Exists.intro y
                    (Exists.intro w
                      (And.intro firstWitness
                        (And.intro secondWitness thirdWitness)))

theorem compGap_witnesses_to_right_nested
    {Source Inter Final Top : Type}
    {firstGap : Inter → Source → Prop}
    {secondGap : Final → Inter → Prop}
    {thirdGap : Top → Final → Prop}
    {z : Top} {x : Source} :
    (∃ y : Inter, ∃ w : Final, firstGap y x ∧ secondGap w y ∧ thirdGap z w) →
      CompGap firstGap (CompGap secondGap thirdGap) z x := by
  intro witnesses
  cases witnesses with
  | intro y rest =>
      cases rest with
      | intro w data =>
          cases data with
          | intro firstWitness tail =>
              cases tail with
              | intro secondWitness thirdWitness =>
                  exact Exists.intro y
                    (And.intro firstWitness
                      (Exists.intro w (And.intro secondWitness thirdWitness)))

theorem compGap_right_nested_iff_witnesses
    {Source Inter Final Top : Type}
    {firstGap : Inter → Source → Prop}
    {secondGap : Final → Inter → Prop}
    {thirdGap : Top → Final → Prop}
    {z : Top} {x : Source} :
    CompGap firstGap (CompGap secondGap thirdGap) z x ↔
      ∃ y : Inter, ∃ w : Final, firstGap y x ∧ secondGap w y ∧ thirdGap z w := by
  constructor
  · exact compGap_right_nested_witnesses
  · exact compGap_witnesses_to_right_nested

theorem compGap_left_nested_witnesses
    {Source Inter Final Top : Type}
    {firstGap : Inter → Source → Prop}
    {secondGap : Final → Inter → Prop}
    {thirdGap : Top → Final → Prop}
    {z : Top} {x : Source} :
    CompGap (fun w x => CompGap firstGap secondGap w x) thirdGap z x →
      ∃ y : Inter, ∃ w : Final, firstGap y x ∧ secondGap w y ∧ thirdGap z w := by
  intro h
  cases h with
  | intro w outer =>
      cases outer with
      | intro nested thirdWitness =>
          cases nested with
          | intro y nestedData =>
              cases nestedData with
              | intro firstWitness secondWitness =>
                  exact Exists.intro y
                    (Exists.intro w
                      (And.intro firstWitness
                        (And.intro secondWitness thirdWitness)))

theorem compGap_three_witnesses_iff
    {Source Inter Final Top : Type}
    {firstGap : Inter -> Source -> Prop}
    {secondGap : Final -> Inter -> Prop}
    {thirdGap : Top -> Final -> Prop}
    {z : Top} {x : Source} :
    CompGap (fun w x => CompGap firstGap secondGap w x) thirdGap z x <->
      (exists y : Inter, exists w : Final,
        firstGap y x /\ secondGap w y /\ thirdGap z w) := by
  constructor
  · intro h
    cases h with
    | intro w outer =>
        cases outer with
        | intro nested thirdWitness =>
            cases nested with
            | intro y nestedData =>
                cases nestedData with
                | intro firstWitness secondWitness =>
                    exact Exists.intro y
                      (Exists.intro w
                        (And.intro firstWitness
                          (And.intro secondWitness thirdWitness)))
  · intro witnesses
    cases witnesses with
    | intro y rest =>
        cases rest with
        | intro w data =>
            cases data with
            | intro firstWitness restData =>
                cases restData with
                | intro secondWitness thirdWitness =>
                    exact Exists.intro w
                      (And.intro
                        (Exists.intro y (And.intro firstWitness secondWitness))
                        thirdWitness)

omit [AskSetup] [PackageSetup] G in
theorem compGap_four_witnesses_iff
    {A B C D E : Type}
    {first : B → A → Prop}
    {second : C → B → Prop}
    {third : D → C → Prop}
    {fourth : E → D → Prop}
    {z : E} {x : A} :
    CompGap (fun d a => CompGap (fun c a => CompGap first second c a) third d a)
        fourth z x ↔
      ∃ b : B, ∃ c : C, ∃ d : D,
        first b x ∧ second c b ∧ third d c ∧ fourth z d := by
  constructor
  · intro left
    cases left with
    | intro d dData =>
        cases dData with
        | intro firstThree fourthWitness =>
            cases firstThree with
            | intro c cData =>
                cases cData with
                | intro firstSecond thirdWitness =>
                    cases firstSecond with
                    | intro b bData =>
                        cases bData with
                        | intro firstWitness secondWitness =>
                            exact Exists.intro b
                              (Exists.intro c
                                (Exists.intro d
                                  (And.intro firstWitness
                                    (And.intro secondWitness
                                      (And.intro thirdWitness fourthWitness)))))
  · intro witnesses
    cases witnesses with
    | intro b rest =>
        cases rest with
        | intro c restData =>
            cases restData with
            | intro d data =>
                cases data with
                | intro firstWitness tail =>
                    cases tail with
                    | intro secondWitness tailData =>
                        cases tailData with
                        | intro thirdWitness fourthWitness =>
                            exact Exists.intro d
                              (And.intro
                                (Exists.intro c
                                  (And.intro
                                    (Exists.intro b
                                      (And.intro firstWitness secondWitness))
                                    thirdWitness))
                                fourthWitness)

theorem compGap_assoc_witnesses
    {A B C D : Type}
    {first : B → A → Prop}
    {second : C → B → Prop}
    {third : D → C → Prop}
    {z : D} {x : A} :
    CompGap (fun c a => CompGap first second c a) third z x →
      ∃ b : B, ∃ c : C, first b x ∧ second c b ∧ third z c := by
  intro left
  cases left with
  | intro c cData =>
      cases cData with
      | intro firstSecond thirdWitness =>
          cases firstSecond with
          | intro b bData =>
              cases bData with
              | intro firstWitness secondWitness =>
                  exact Exists.intro b
                    (Exists.intro c
                      (And.intro firstWitness
                        (And.intro secondWitness thirdWitness)))

theorem compGap_assoc_iff_witnesses
    {A B C D : Type}
    {first : B -> A -> Prop}
    {second : C -> B -> Prop}
    {third : D -> C -> Prop}
    {z : D} {x : A} :
    (CompGap (fun c a => CompGap first second c a) third z x ↔
      ∃ b : B, ∃ c : C, first b x ∧ second c b ∧ third z c) ∧
    (CompGap first (fun z b => CompGap second third z b) z x ↔
      ∃ b : B, ∃ c : C, first b x ∧ second c b ∧ third z c) := by
  constructor
  · constructor
    · intro left
      cases left with
      | intro c cData =>
          cases cData with
          | intro firstSecond thirdWitness =>
              cases firstSecond with
              | intro b bData =>
                  cases bData with
                  | intro firstWitness secondWitness =>
                      exact Exists.intro b
                        (Exists.intro c
                          (And.intro firstWitness
                            (And.intro secondWitness thirdWitness)))
    · intro witnesses
      cases witnesses with
      | intro b rest =>
          cases rest with
          | intro c data =>
              cases data with
              | intro firstWitness restData =>
                  cases restData with
                  | intro secondWitness thirdWitness =>
                      exact Exists.intro c
                        (And.intro
                          (Exists.intro b (And.intro firstWitness secondWitness))
                          thirdWitness)
  · constructor
    · intro right
      cases right with
      | intro b bData =>
          cases bData with
          | intro firstWitness secondThird =>
              cases secondThird with
              | intro c cData =>
                  cases cData with
                  | intro secondWitness thirdWitness =>
                      exact Exists.intro b
                        (Exists.intro c
                          (And.intro firstWitness
                            (And.intro secondWitness thirdWitness)))
    · intro witnesses
      cases witnesses with
      | intro b rest =>
          cases rest with
          | intro c data =>
              cases data with
              | intro firstWitness restData =>
                  cases restData with
                  | intro secondWitness thirdWitness =>
                      exact Exists.intro b
                        (And.intro firstWitness
                          (Exists.intro c
                            (And.intro secondWitness thirdWitness)))

theorem compGap_assoc_backward
    {A B C Final : Type}
    {first : B → A → Prop}
    {second : C → B → Prop}
    {third : Final → C → Prop}
    {z : Final} {x : A} :
    CompGap first (fun z b => CompGap second third z b) z x →
      CompGap (fun c a => CompGap first second c a) third z x := by
  intro right
  cases right with
  | intro b bData =>
      cases bData with
      | intro firstWitness secondThird =>
          cases secondThird with
          | intro c cData =>
              cases cData with
              | intro secondWitness thirdWitness =>
                  exact Exists.intro c
                    (And.intro
                      (Exists.intro b (And.intro firstWitness secondWitness))
                      thirdWitness)

theorem ledger_composition_principle_iff
    {A B C D : Type}
    {first : B → A → Prop}
    {second : C → B → Prop}
    {third : D → C → Prop}
    {z : D} {x : A} :
    CompGap (fun c a => CompGap first second c a) third z x ↔
      ∃ b : B, ∃ c : C, first b x ∧ second c b ∧ third z c := by
  constructor
  · intro left
    cases left with
    | intro c cData =>
        cases cData with
        | intro firstSecond thirdWitness =>
            cases firstSecond with
            | intro b bData =>
                cases bData with
                | intro firstWitness secondWitness =>
                    exact Exists.intro b
                      (Exists.intro c
                        (And.intro firstWitness
                          (And.intro secondWitness thirdWitness)))
  · intro witnesses
    cases witnesses with
    | intro b rest =>
        cases rest with
        | intro c data =>
            cases data with
            | intro firstWitness tail =>
                cases tail with
                | intro secondWitness thirdWitness =>
                    exact Exists.intro c
                      (And.intro
                        (Exists.intro b (And.intro firstWitness secondWitness))
                        thirdWitness)
end BEDC.FKernel.Gap
