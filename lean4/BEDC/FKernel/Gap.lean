import BEDC.FKernel.Package

/-! Gap ledgers record which admitted histories fall under visible package tokens. -/
namespace BEDC.FKernel.Gap

open BEDC.FKernel.Hist
open BEDC.FKernel.Package


axiom Domain : Type
axiom InDom : Domain → BHist → Prop
axiom InGapSig : Pi → Domain → Pkg → BHist → Prop

structure GapPolicy (P : Pi) (D : Domain) : Prop where
  generation : ∀ {p : Pkg} {h : BHist}, InGapSig P D p h → ∃ s : BHist, TokIntro P s p
  coverage : ∀ {h : BHist}, InDom D h → ∃ p : Pkg, InGapSig P D p h
  separation : ∀ {h : BHist} {p q : Pkg}, InDom D h → InGapSig P D p h → InGapSig P D q h → psame p q

theorem gap_coverage :
    ∀ {P : Pi} {D : Domain} {h : BHist},
      GapPolicy P D → InDom D h → ∃ p : Pkg, InGapSig P D p h := by
  sorry

theorem gap_separation :
    ∀ {P : Pi} {D : Domain} {h : BHist} {p q : Pkg},
      GapPolicy P D → InDom D h → InGapSig P D p h → InGapSig P D q h → psame p q := by
  sorry

-- Placeholder: source did not give a concrete shape. v0.2 will specify.
theorem compGap_coverage : True := True.intro

end BEDC.FKernel.Gap
