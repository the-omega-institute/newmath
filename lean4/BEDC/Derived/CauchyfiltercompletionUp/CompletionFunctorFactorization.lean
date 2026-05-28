import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionCompletionFunctorFactorization [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name
      functorRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont readback sealRow functorRoute →
        PkgSig bundle functorRoute pkg →
          UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
            UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory functorRoute ∧
              Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                Cont readback sealRow functorRoute ∧ Cont transport replay provenance ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle functorRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet readbackSealFunctor functorPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, transportReplay, provenancePkg, _namePkg⟩ := packet
  have functorUnary : UnaryHistory functorRoute :=
    unary_cont_closed readbackUnary sealUnary readbackSealFunctor
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, functorUnary,
      filterWindows, toleranceReadback, readbackSealFunctor, transportReplay, provenancePkg,
      functorPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
