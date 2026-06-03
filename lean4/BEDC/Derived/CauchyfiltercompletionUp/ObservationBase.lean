import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_observation_base [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name
      observationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter windows observationRead →
        PkgSig bundle observationRead pkg →
          UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
            UnaryHistory readback ∧ UnaryHistory observationRead ∧
              Cont filter windows tolerance ∧ Cont filter windows observationRead ∧
                Cont tolerance readback sealRow ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle observationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet filterWindowsObservation observationPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed filterUnary windowsUnary filterWindowsObservation
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, observationUnary,
      filterWindows, filterWindowsObservation, toleranceReadback, provenancePkg,
      observationPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
