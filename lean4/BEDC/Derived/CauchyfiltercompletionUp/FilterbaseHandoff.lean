import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_filterbase_handoff [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name filterbaseRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter windows filterbaseRead →
        Cont filterbaseRead readback completionRead →
          PkgSig bundle completionRead pkg →
            UnaryHistory filterbaseRead ∧ UnaryHistory completionRead ∧
              Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                Cont filter windows filterbaseRead ∧
                  Cont filterbaseRead readback completionRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet filterbaseRoute completionRoute completionPkg
  obtain ⟨filterUnary, windowsUnary, _toleranceUnary, readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have filterbaseUnary : UnaryHistory filterbaseRead :=
    unary_cont_closed filterUnary windowsUnary filterbaseRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed filterbaseUnary readbackUnary completionRoute
  exact
    ⟨filterbaseUnary, completionUnary, filterWindows, toleranceReadback, filterbaseRoute,
      completionRoute, provenancePkg, completionPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
