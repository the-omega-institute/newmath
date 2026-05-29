import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_basis_real_seal [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name basisRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont windows tolerance basisRead →
        Cont readback sealRow sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
              UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory basisRead ∧
                UnaryHistory sealRead ∧ Cont filter windows tolerance ∧
                  Cont windows tolerance basisRead ∧ Cont tolerance readback sealRow ∧
                    Cont readback sealRow sealRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet windowsToleranceBasis readbackSeal sealPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed windowsUnary toleranceUnary windowsToleranceBasis
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary sealUnary readbackSeal
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, basisUnary,
      sealReadUnary, filterWindows, windowsToleranceBasis, toleranceReadback, readbackSeal,
      provenancePkg, sealPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
