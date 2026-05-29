import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPublicExport [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name rootRead
      completionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter readback rootRead →
        Cont rootRead sealRow completionRead →
          Cont completionRead provenance publicRead →
            PkgSig bundle publicRead pkg →
              UnaryHistory rootRead ∧ UnaryHistory completionRead ∧ UnaryHistory publicRead ∧
                Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                  Cont filter readback rootRead ∧ Cont rootRead sealRow completionRead ∧
                    Cont completionRead provenance publicRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory PkgSig
  intro packet rootRoute completionRoute publicRoute publicPkg
  obtain ⟨filterUnary, _windowsUnary, _toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed filterUnary readbackUnary rootRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed rootUnary sealUnary completionRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed completionUnary provenanceUnary publicRoute
  exact
    ⟨rootUnary, completionUnary, publicUnary, filterWindows, toleranceReadback, rootRoute,
      completionRoute, publicRoute, provenancePkg, publicPkg⟩

theorem CauchyFilterCompletionFilterbaseWindowExhaustion [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name filterbase windowRead
      exhausted : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter windows filterbase →
        Cont filterbase tolerance windowRead →
          Cont windowRead readback exhausted →
            PkgSig bundle exhausted pkg →
              UnaryHistory filterbase ∧ UnaryHistory windowRead ∧ UnaryHistory exhausted ∧
                Cont filter windows filterbase ∧ Cont filterbase tolerance windowRead ∧
                  Cont windowRead readback exhausted ∧ Cont tolerance readback sealRow ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle exhausted pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory PkgSig
  intro packet filterbaseRoute windowRoute exhaustionRoute exhaustedPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have filterbaseUnary : UnaryHistory filterbase :=
    unary_cont_closed filterUnary windowsUnary filterbaseRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed filterbaseUnary toleranceUnary windowRoute
  have exhaustedUnary : UnaryHistory exhausted :=
    unary_cont_closed windowUnary readbackUnary exhaustionRoute
  exact
    ⟨filterbaseUnary, windowUnary, exhaustedUnary, filterbaseRoute, windowRoute, exhaustionRoute,
      toleranceReadback, provenancePkg, exhaustedPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
