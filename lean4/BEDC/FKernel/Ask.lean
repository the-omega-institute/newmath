import BEDC.FKernel.Mark
import BEDC.FKernel.Hist

/-! Asking events emit internal marks together with evidence tokens. -/
namespace BEDC.FKernel.Ask

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist


axiom ProbeName : Type
axiom Evidence : Type
axiom Ask : ProbeName → BHist → BMark → Evidence → Prop

structure AskPolicy (D : BHist → Prop) : Prop where
  total :
    ∀ {π : ProbeName} {h : BHist}, D h → ∃ m : BMark, ∃ δ : Evidence, Ask π h m δ
  deterministic :
    ∀ {π : ProbeName} {h : BHist} {m n : BMark} {δ θ : Evidence},
      Ask π h m δ → Ask π h n θ → msame m n
  respectsHistory :
    ∀ {π : ProbeName} {h k : BHist} {m n : BMark} {δ θ : Evidence},
      hsame h k → Ask π h m δ → Ask π k n θ → msame m n

end BEDC.FKernel.Ask
