import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_root_filterbase_admission [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name
      admitted filterbaseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter windows admitted →
        Cont admitted tolerance filterbaseRead →
          PkgSig bundle filterbaseRead pkg →
            UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
              UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory admitted ∧
                UnaryHistory filterbaseRead ∧ Cont filter windows tolerance ∧
                  Cont filter windows admitted ∧ Cont admitted tolerance filterbaseRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle filterbaseRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet filterWindowsAdmitted admittedToleranceFilterbase filterbasePkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindowsTolerance,
    _toleranceReadbackSeal, _transportReplayProvenance, provenancePkg, _namePkg⟩ := packet
  have admittedUnary : UnaryHistory admitted :=
    unary_cont_closed filterUnary windowsUnary filterWindowsAdmitted
  have filterbaseUnary : UnaryHistory filterbaseRead :=
    unary_cont_closed admittedUnary toleranceUnary admittedToleranceFilterbase
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, admittedUnary,
      filterbaseUnary, filterWindowsTolerance, filterWindowsAdmitted,
      admittedToleranceFilterbase, provenancePkg, filterbasePkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
