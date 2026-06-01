import BEDC.Derived.CauchyfiltercompletionUp.WindowToleranceExactness

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_regular_readback_totality [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name windowRead
      readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont windows tolerance windowRead →
        Cont windowRead readback readbackRead →
          hsame sealRow sealRead →
            PkgSig bundle readbackRead pkg →
              PkgSig bundle sealRead pkg →
                UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                  Cont windows tolerance windowRead ∧ Cont windowRead readback readbackRead ∧
                    Cont tolerance readback sealRow ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle readbackRead pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro packet windowsTolerance windowReadback sealSame readbackPkg sealPkg
  have windowExact :=
    CauchyFilterCompletionPacket_window_tolerance_exactness
      (filter := filter) (windows := windows) (tolerance := tolerance)
      (readback := readback) (sealRow := sealRow) (transport := transport)
      (replay := replay) (provenance := provenance) (name := name)
      (windowRead := windowRead) (readbackRead := readbackRead)
      (bundle := bundle) (pkg := pkg)
      packet windowsTolerance windowReadback readbackPkg
  obtain ⟨_windowUnary, readbackReadUnary, windowsToleranceRow, windowReadbackRow,
    toleranceReadback, provenancePkg, readbackReadPkg⟩ := windowExact
  obtain ⟨_filterUnary, _windowsUnary, _toleranceUnary, _readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _filterWindows,
    _packetToleranceReadback, _transportReplay, _packetProvenancePkg, _namePkg⟩ := packet
  have sealReadUnary : UnaryHistory sealRead :=
    unary_transport sealUnary sealSame
  exact
    ⟨readbackReadUnary, sealReadUnary, windowsToleranceRow, windowReadbackRow,
      toleranceReadback, provenancePkg, readbackReadPkg, sealPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
