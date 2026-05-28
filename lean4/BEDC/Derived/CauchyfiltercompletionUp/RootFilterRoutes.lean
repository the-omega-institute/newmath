import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionRootFilterScopeClosure [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name rootRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter readback rootRead →
        Cont rootRead sealRow completionRead →
          PkgSig bundle completionRead pkg →
            UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
              UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
                UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                  UnaryHistory rootRead ∧ UnaryHistory completionRead ∧
                    Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                      Cont transport replay provenance ∧ Cont filter readback rootRead ∧
                        Cont rootRead sealRow completionRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet rootRoute completionRoute completionPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    transportUnary, replayUnary, provenanceUnary, nameUnary, filterWindows,
    toleranceReadback, transportReplay, provenancePkg, namePkg⟩ := packet
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed filterUnary readbackUnary rootRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed rootUnary sealUnary completionRoute
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, transportUnary,
      replayUnary, provenanceUnary, nameUnary, rootUnary, completionUnary, filterWindows,
      toleranceReadback, transportReplay, rootRoute, completionRoute, provenancePkg, namePkg,
      completionPkg⟩

theorem CauchyFilterCompletionRootRealSealRoute [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      hsame sealRow sealRead →
        PkgSig bundle sealRead pkg →
          UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
            UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory sealRead ∧
              Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro packet sameSeal sealPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, transportReplay, provenancePkg, namePkg⟩ := packet
  have sealReadUnary : UnaryHistory sealRead :=
    unary_transport sealUnary sameSeal
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, sealReadUnary,
      filterWindows, toleranceReadback, transportReplay, provenancePkg, namePkg, sealPkg⟩

theorem CauchyFilterCompletionRootFilterbaseSourceCoverageObligation [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name sourceRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter windows sourceRead →
        Cont sourceRead tolerance sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
              UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory sourceRead ∧
                UnaryHistory sealRead ∧ Cont filter windows tolerance ∧
                  Cont tolerance readback sealRow ∧ Cont filter windows sourceRead ∧
                    Cont sourceRead tolerance sealRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet sourceRoute sealRoute sealPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed filterUnary windowsUnary sourceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sourceUnary toleranceUnary sealRoute
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, sourceUnary,
      sealReadUnary, filterWindows, toleranceReadback, sourceRoute, sealRoute, provenancePkg,
      sealPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
