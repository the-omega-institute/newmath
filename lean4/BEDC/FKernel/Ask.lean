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

structure AskPolicy (D : BHist → Prop) : Prop where
  total :
    ∀ {π : ProbeName} {h : BHist}, D h → ∃ m : BMark, ∃ δ : Evidence, Ask π h m δ
  deterministic :
    ∀ {π : ProbeName} {h : BHist} {m n : BMark} {δ θ : Evidence},
      Ask π h m δ → Ask π h n θ → msame m n
  respectsHistory :
    ∀ {π : ProbeName} {h k : BHist} {m n : BMark} {δ θ : Evidence},
      hsame h k → Ask π h m δ → Ask π k n θ → msame m n

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

def MinimalAskSetup : AskSetup where
  ProbeName := Unit
  Evidence := Unit
  Ask := fun _ _ _ _ => True

end BEDC.FKernel.Ask
