import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_filterbase_window_minimality [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name windowRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      hsame windows windowRead →
        UnaryHistory filter ∧ UnaryHistory windowRead ∧ UnaryHistory tolerance ∧
          UnaryHistory readback ∧ UnaryHistory sealRow ∧ Cont filter windows tolerance ∧
            Cont tolerance readback sealRow ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro packet sameWindow
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, namePkg⟩ := packet
  have windowReadUnary : UnaryHistory windowRead :=
    unary_transport windowsUnary sameWindow
  exact
    ⟨filterUnary, windowReadUnary, toleranceUnary, readbackUnary, sealUnary, filterWindows,
      toleranceReadback, provenancePkg, namePkg⟩

theorem CauchyFilterCompletionPacket_tail_readback_admission [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont readback sealRow tailRead →
        PkgSig bundle tailRead pkg →
          UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
            UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory tailRead ∧
              Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                Cont readback sealRow tailRead ∧ Cont transport replay provenance ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle tailRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet tailRoute tailPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, transportReplay, provenancePkg, namePkg⟩ := packet
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed readbackUnary sealUnary tailRoute
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, tailReadUnary,
      filterWindows, toleranceReadback, tailRoute, transportReplay, provenancePkg, namePkg,
      tailPkg⟩

theorem CauchyFilterCompletionPacket_window_readback_transport [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name readback' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      hsame readback readback' →
        UnaryHistory readback' ∧ Cont filter windows tolerance ∧
          Cont tolerance readback sealRow ∧ Cont transport replay provenance ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro packet sameReadback
  obtain ⟨_filterUnary, _windowsUnary, _toleranceUnary, readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, transportReplay, provenancePkg, _namePkg⟩ := packet
  exact
    ⟨unary_transport readbackUnary sameReadback, filterWindows, toleranceReadback,
      transportReplay, provenancePkg⟩

theorem CauchyFilterCompletionPacket_basis_readback_route [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name basisRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont windows tolerance basisRead →
        PkgSig bundle basisRead pkg →
          UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
            UnaryHistory readback ∧ UnaryHistory basisRead ∧ Cont filter windows tolerance ∧
              Cont windows tolerance basisRead ∧ Cont tolerance readback sealRow ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle basisRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet windowsTolerance basisPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have basisReadUnary : UnaryHistory basisRead :=
    unary_cont_closed windowsUnary toleranceUnary windowsTolerance
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, basisReadUnary,
      filterWindows, windowsTolerance, toleranceReadback, provenancePkg, basisPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
