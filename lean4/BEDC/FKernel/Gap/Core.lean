import BEDC.FKernel.Package

namespace BEDC.FKernel.Gap

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ext
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Sig

class DomainSetup where
  Domain : Type
  InDom : Domain → BHist → Prop

variable [AskSetup] [PackageSetup] [G : DomainSetup]

abbrev Domain : Type := G.Domain
abbrev InDom : Domain → BHist → Prop := G.InDom

omit [AskSetup] [PackageSetup] in
theorem InDom_iff_setup_field {D : Domain} {h : BHist} : InDom D h ↔ G.InDom D h := by
  rfl

structure DomainPolicy (D : Domain) : Prop where
  transport : ∀ {h k : BHist}, InDom D h → hsame h k → InDom D k

def InGapSig (bundle : ProbeBundle ProbeName) (D : Domain) (p : Pkg) (h : BHist) : Prop :=
  InDom D h ∧ ∃ s : BHist, SigRel bundle h s ∧ TokIntro bundle s p

def MinimalDomainSetup : DomainSetup where
  Domain := Unit
  InDom := fun _ _ => True
end BEDC.FKernel.Gap
