import BEDC.FKernel.Mark
import BEDC.FKernel.Hist

/-! Asking events emit internal marks together with evidence tokens. -/
namespace BEDC.FKernel.Ask

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist

class AskSetup where
  ProbeName : Type
  Evidence : Type
  Ask : ProbeName → BHist → BMark → Evidence → Prop

variable [S : AskSetup]

abbrev ProbeName : Type := S.ProbeName
abbrev Evidence : Type := S.Evidence
abbrev Ask : ProbeName → BHist → BMark → Evidence → Prop := S.Ask

structure AskEvent (pi : ProbeName) (h : BHist) : Type where
  mark : BMark
  evidence : Evidence
  event : Ask pi h mark evidence

omit S in
theorem askEvent_witness [AskSetup] {pi : ProbeName} {h : BHist} :
    AskEvent pi h -> ∃ m : BMark, ∃ delta : Evidence, Ask pi h m delta := by
  intro ev
  cases ev with
  | mk mark evidence event =>
      exact Exists.intro mark (Exists.intro evidence event)

omit S in
theorem askEvent_evidence_witness [AskSetup] {pi : ProbeName} {h : BHist} :
    AskEvent pi h -> Nonempty Evidence := by
  intro ev
  cases ev with
  | mk _ evidence _ =>
      exact Nonempty.intro evidence

structure AskPolicy (D : BHist → Prop) : Prop where
  total :
    ∀ {π : ProbeName} {h : BHist}, D h → ∃ m : BMark, ∃ δ : Evidence, Ask π h m δ
  deterministic :
    ∀ {π : ProbeName} {h : BHist} {m n : BMark} {δ θ : Evidence},
      Ask π h m δ → Ask π h n θ → msame m n
  respectsHistory :
    ∀ {π : ProbeName} {h k : BHist} {m n : BMark} {δ θ : Evidence},
      hsame h k → Ask π h m δ → Ask π k n θ → msame m n

theorem ask_total_from_policy {D : BHist → Prop} (policy : AskPolicy D)
    {π : ProbeName} {h : BHist} :
    D h → ∃ m : BMark, ∃ δ : Evidence, Ask π h m δ := by
  intro hd
  exact policy.total hd

theorem ask_total {D : BHist → Prop} (policy : AskPolicy D)
    {π : ProbeName} {h : BHist} :
    D h → ∃ m : BMark, ∃ δ : Evidence, Ask π h m δ := by
  intro hD
  exact policy.total hD

theorem ask_deterministic {D : BHist → Prop} (policy : AskPolicy D)
    {π : ProbeName} {h : BHist} {m n : BMark} {δ θ : Evidence} :
    Ask π h m δ → Ask π h n θ → msame m n := by
  intro left right
  exact policy.deterministic left right

theorem asking_determinacy {D : BHist → Prop} (policy : AskPolicy D)
    {pi : ProbeName} {h : BHist} {m n : BMark} {delta theta : Evidence} :
    Ask pi h m delta → Ask pi h n theta → msame m n := by
  intro hm hn
  exact policy.deterministic hm hn

omit S in
theorem asking_determinacy_field [AskSetup] {D : BHist -> Prop} (policy : AskPolicy D) :
    (forall {pi : ProbeName} {h : BHist} {m n : BMark} {delta theta : Evidence},
      Ask pi h m delta -> Ask pi h n theta -> msame m n) := by
  intro pi h m n delta theta left right
  exact policy.deterministic left right

theorem ask_respects_history {D : BHist → Prop} (policy : AskPolicy D)
    {pi : ProbeName} {h k : BHist} {m n : BMark} {delta theta : Evidence} :
    hsame h k → Ask pi h m delta → Ask pi k n theta → msame m n := by
  intro same left right
  exact policy.respectsHistory same left right

omit S in
theorem ask_policy_fields [AskSetup] {D : BHist → Prop} (policy : AskPolicy D) :
    (∀ {π : ProbeName} {h : BHist}, D h → ∃ m : BMark, ∃ δ : Evidence, Ask π h m δ) ∧
    (∀ {π : ProbeName} {h : BHist} {m n : BMark} {δ θ : Evidence},
      Ask π h m δ → Ask π h n θ → msame m n) ∧
    (∀ {π : ProbeName} {h k : BHist} {m n : BMark} {δ θ : Evidence},
      hsame h k → Ask π h m δ → Ask π k n θ → msame m n) := by
  constructor
  · intro π h hD
    exact policy.total hD
  · constructor
    · intro π h m n δ θ left right
      exact policy.deterministic left right
    · intro π h k m n δ θ same left right
      exact policy.respectsHistory same left right

omit S in
theorem AskPolicy_iff_fields [AskSetup] {D : BHist → Prop} :
    AskPolicy D ↔
      ((∀ {π : ProbeName} {h : BHist}, D h → ∃ m : BMark, ∃ δ : Evidence, Ask π h m δ) ∧
      (∀ {π : ProbeName} {h : BHist} {m n : BMark} {δ θ : Evidence},
        Ask π h m δ → Ask π h n θ → msame m n) ∧
      (∀ {π : ProbeName} {h k : BHist} {m n : BMark} {δ θ : Evidence},
        hsame h k → Ask π h m δ → Ask π k n θ → msame m n)) := by
  constructor
  · intro policy
    exact ask_policy_fields policy
  · intro fields
    cases fields with
    | intro total rest =>
        cases rest with
        | intro deterministic respectsHistory =>
            exact AskPolicy.mk total deterministic respectsHistory

def MinimalAskSetup : AskSetup where
  ProbeName := Unit
  Evidence := Unit
  Ask := fun _ _ _ _ => True

end BEDC.FKernel.Ask
