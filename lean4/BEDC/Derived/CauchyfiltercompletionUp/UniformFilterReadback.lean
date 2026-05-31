import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_uniform_filter_readback [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name uniformRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont windows readback uniformRead →
        PkgSig bundle uniformRead pkg →
          UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
            UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory uniformRead ∧
              Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                Cont windows readback uniformRead ∧ Cont transport replay provenance ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet uniformRoute uniformPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, transportReplay, provenancePkg, _namePkg⟩ := packet
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed windowsUnary readbackUnary uniformRoute
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, uniformUnary,
      filterWindows, toleranceReadback, uniformRoute, transportReplay, provenancePkg,
      uniformPkg⟩

theorem CauchyFilterCompletionPacket_separated_completion_boundary [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name separatedSeal
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      hsame sealRow separatedSeal →
        Cont separatedSeal transport boundaryRead →
          PkgSig bundle boundaryRead pkg →
            UnaryHistory separatedSeal ∧ UnaryHistory boundaryRead ∧
              Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                Cont transport replay provenance ∧ Cont separatedSeal transport boundaryRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro packet sameSeal boundaryRoute boundaryPkg
  obtain ⟨_filterUnary, _windowsUnary, _toleranceUnary, _readbackUnary, sealUnary,
    transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, transportReplay, provenancePkg, _namePkg⟩ := packet
  have separatedUnary : UnaryHistory separatedSeal :=
    unary_transport sealUnary sameSeal
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed separatedUnary transportUnary boundaryRoute
  exact
    ⟨separatedUnary, boundaryUnary, filterWindows, toleranceReadback, transportReplay,
      boundaryRoute, provenancePkg, boundaryPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
