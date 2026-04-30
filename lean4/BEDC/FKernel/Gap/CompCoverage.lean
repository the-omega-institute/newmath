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
omit [AskSetup] [PackageSetup] in
theorem composite_coverage {Mid Final : Type} {D : Domain}
    {firstGap : Mid -> BHist -> Prop} {secondGap : Final -> Mid -> Prop}
    (firstCoverage : forall {h : BHist}, InDom D h -> exists y : Mid, firstGap y h)
    (secondCoverage :
      forall {y : Mid},
        (exists h : BHist, InDom D h ∧ firstGap y h) ->
          exists z : Final, secondGap z y)
    {h : BHist} :
    InDom D h -> exists z : Final, exists y : Mid, firstGap y h ∧ secondGap z y := by
  intro hIn
  cases firstCoverage hIn with
  | intro y hy =>
      have ySource : exists h0 : BHist, InDom D h0 ∧ firstGap y h0 :=
        Exists.intro h (And.intro hIn hy)
      cases secondCoverage ySource with
      | intro z hz =>
          exact Exists.intro z (Exists.intro y (And.intro hy hz))

theorem compGap_coverage_from_layers
    {Source Inter Final : Type}
    {SourceOk : Source -> Prop} {InterOk : Inter -> Prop}
    {CGap : Inter -> Source -> Prop} {DGap : Final -> Inter -> Prop}
    (cCoverage :
      forall {h : Source}, SourceOk h -> exists y : Inter, And (CGap y h) (InterOk y))
    (dCoverage : forall {y : Inter}, InterOk y -> exists z : Final, DGap z y)
    {h : Source} :
    SourceOk h -> exists z : Final, exists y : Inter, And (CGap y h) (DGap z y) := by
  intro sourceOk
  cases cCoverage sourceOk with
  | intro y cData =>
      cases cData with
      | intro cGap interOk =>
          cases dCoverage interOk with
          | intro z dGap =>
              exact Exists.intro z (Exists.intro y (And.intro cGap dGap))

theorem compGap_coverage_exact
    {Source Inter Final : Type}
    {firstGap : Inter -> Source -> Prop}
    {secondGap : Final -> Inter -> Prop}
    (firstCoverage : forall x : Source, exists y : Inter, firstGap y x)
    (secondCoverage : forall y : Inter, exists z : Final, secondGap z y)
    (x : Source) :
    exists z : Final, CompGap firstGap secondGap z x := by
  cases firstCoverage x with
  | intro y firstWitness =>
      cases secondCoverage y with
      | intro z secondWitness =>
          exact Exists.intro z
            (Exists.intro y (And.intro firstWitness secondWitness))

theorem compGap_composite_coverage_witness
    {Source Inter Final : Type}
    {SourceOk : Source -> Prop}
    {firstGap : Inter -> Source -> Prop}
    {secondGap : Final -> Inter -> Prop}
    (firstCoverage : forall {x : Source}, SourceOk x -> exists y : Inter, firstGap y x)
    (secondCoverage :
      forall {x : Source} {y : Inter},
        SourceOk x -> firstGap y x -> exists z : Final, secondGap z y)
    {x : Source} :
    SourceOk x -> exists z : Final, CompGap firstGap secondGap z x := by
  intro hx
  cases firstCoverage hx with
  | intro y hy =>
      cases secondCoverage hx hy with
      | intro z hz =>
          exact Exists.intro z (compGap_intro (y := y) hy hz)

omit [AskSetup] [PackageSetup] G in
theorem compGap_coverage_from_sourced_layers
    {Source Inter Final : Type}
    {SourceOk : Source → Prop}
    {firstGap : Inter → Source → Prop}
    {secondGap : Final → Inter → Prop}
    (firstCoverage : ∀ {x : Source}, SourceOk x → ∃ y : Inter, firstGap y x)
    (secondCoverage :
      ∀ {y : Inter},
        (∃ x : Source, SourceOk x ∧ firstGap y x) → ∃ z : Final, secondGap z y)
    {x : Source} :
    SourceOk x → ∃ z : Final, CompGap firstGap secondGap z x := by
  intro sourceOk
  cases firstCoverage sourceOk with
  | intro y firstWitness =>
      have sourced : ∃ x0 : Source, SourceOk x0 ∧ firstGap y x0 :=
        Exists.intro x (And.intro sourceOk firstWitness)
      cases secondCoverage sourced with
      | intro z secondWitness =>
          exact Exists.intro z (Exists.intro y (And.intro firstWitness secondWitness))

theorem compGap_witness_from_layers
    {Source Inter Final : Type}
    {SourceOk : Source → Prop} {InterOk : Inter → Prop}
    {CGap : Inter → Source → Prop} {DGap : Final → Inter → Prop}
    (cCoverage :
      ∀ {x : Source}, SourceOk x → ∃ y : Inter, CGap y x ∧ InterOk y)
    (dCoverage : ∀ {y : Inter}, InterOk y → ∃ z : Final, DGap z y)
    {x : Source} :
    SourceOk x → ∃ z : Final, CompGap CGap DGap z x := by
  intro sourceOk
  cases cCoverage sourceOk with
  | intro y cData =>
      cases cData with
      | intro cGap interOk =>
          cases dCoverage interOk with
          | intro z dGap =>
              exact Exists.intro z (Exists.intro y (And.intro cGap dGap))

theorem compGap_coverage_with_intermediate
    {Source Inter Final : Type}
    {SourceOk : Source -> Prop} {InterOk : Inter -> Prop}
    {CGap : Inter -> Source -> Prop} {DGap : Final -> Inter -> Prop}
    (cCoverage : forall {x : Source}, SourceOk x -> exists y : Inter, CGap y x /\ InterOk y)
    (dCoverage : forall {y : Inter}, InterOk y -> exists z : Final, DGap z y)
    {x : Source} :
    SourceOk x -> exists y : Inter, CGap y x /\ exists z : Final, CompGap CGap DGap z x := by
  intro sourceOk
  cases cCoverage sourceOk with
  | intro y cData =>
      cases cData with
      | intro cGap interOk =>
          cases dCoverage interOk with
          | intro z dGap =>
              exact Exists.intro y
                (And.intro cGap
                  (Exists.intro z
                    (Exists.intro y (And.intro cGap dGap))))

theorem compGap_coverage_intermediate_and_final
    {Source Inter Final : Type}
    {SourceOk : Source -> Prop}
    {CGap : Inter -> Source -> Prop} {DGap : Final -> Inter -> Prop}
    (cCoverage : forall {x : Source}, SourceOk x -> exists y : Inter, CGap y x)
    (dCoverage : forall {y : Inter}, exists z : Final, DGap z y)
    {x : Source} :
    SourceOk x -> Exists (fun y : Inter => And (CGap y x)
      (Exists (fun z : Final => CompGap CGap DGap z x))) := by
  intro sourceOk
  cases cCoverage sourceOk with
  | intro y cGap =>
      cases dCoverage (y := y) with
      | intro z dGap =>
          exact Exists.intro y
            (And.intro cGap
              (Exists.intro z
                (Exists.intro y (And.intro cGap dGap))))

theorem compGap_coverage_with_intermediate_ok
    {Source Inter Final : Type}
    {SourceOk : Source -> Prop} {InterOk : Inter -> Prop}
    {CGap : Inter -> Source -> Prop} {DGap : Final -> Inter -> Prop}
    (cCoverage :
      forall {x : Source}, SourceOk x -> exists y : Inter, CGap y x /\ InterOk y)
    (dCoverage : forall {y : Inter}, InterOk y -> exists z : Final, DGap z y)
    {x : Source} :
    SourceOk x ->
      exists y : Inter,
        CGap y x /\ InterOk y /\ exists z : Final, CompGap CGap DGap z x := by
  intro sourceOk
  cases cCoverage sourceOk with
  | intro y cData =>
      cases cData with
      | intro cGap interOk =>
          cases dCoverage interOk with
          | intro z dGap =>
              exact Exists.intro y
                (And.intro cGap
                  (And.intro interOk
                    (Exists.intro z
                      (Exists.intro y (And.intro cGap dGap)))))

omit [AskSetup] [PackageSetup] G in
theorem compGap_coverage_with_source_and_intermediate
    {Source Inter Final : Type}
    {SourceOk : Source → Prop} {InterOk : Inter → Prop}
    {firstGap : Inter → Source → Prop} {secondGap : Final → Inter → Prop}
    (firstCoverage :
      ∀ {x : Source}, SourceOk x → ∃ y : Inter, firstGap y x ∧ InterOk y)
    (secondCoverage : ∀ {y : Inter}, InterOk y → ∃ z : Final, secondGap z y)
    {x : Source} :
    SourceOk x →
      ∃ z : Final, ∃ y : Inter,
        firstGap y x ∧ InterOk y ∧ secondGap z y ∧
          CompGap firstGap secondGap z x := by
  intro sourceOk
  cases firstCoverage sourceOk with
  | intro y firstData =>
      cases firstData with
      | intro firstWitness interOk =>
          cases secondCoverage interOk with
          | intro z secondWitness =>
              exact Exists.intro z
                (Exists.intro y
                  (And.intro firstWitness
                    (And.intro interOk
                      (And.intro secondWitness
                        (Exists.intro y
                          (And.intro firstWitness secondWitness))))))

omit [AskSetup] [PackageSetup] G in
theorem hardening_composite_coverage
    {Source Inter Final : Type}
    {SourceOk : Source -> Prop}
    {firstGap : Inter -> Source -> Prop}
    {secondGap : Final -> Inter -> Prop}
    (firstCoverage : forall {x : Source}, SourceOk x -> exists y : Inter, firstGap y x)
    (secondCoverage :
      forall {x : Source} {y : Inter},
        SourceOk x -> firstGap y x -> exists z : Final, secondGap z y)
    {x : Source} :
    SourceOk x -> exists z : Final, CompGap firstGap secondGap z x := by
  intro sourceOk
  cases firstCoverage sourceOk with
  | intro y firstWitness =>
      cases secondCoverage sourceOk firstWitness with
      | intro z secondWitness =>
          exact Exists.intro z (Exists.intro y (And.intro firstWitness secondWitness))

theorem compGap_coverage : True := True.intro
end BEDC.FKernel.Gap
