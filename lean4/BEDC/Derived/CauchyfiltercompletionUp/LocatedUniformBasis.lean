import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_located_uniform_basis [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name locatedWindow
      locatedRead uniformWindow uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter windows locatedWindow →
        Cont locatedWindow tolerance locatedRead →
          Cont filter windows uniformWindow →
            Cont uniformWindow tolerance uniformRead →
              PkgSig bundle locatedRead pkg →
                PkgSig bundle uniformRead pkg →
                  UnaryHistory locatedRead ∧ UnaryHistory uniformRead ∧
                    Cont filter windows locatedWindow ∧
                      Cont locatedWindow tolerance locatedRead ∧
                        Cont filter windows uniformWindow ∧
                          Cont uniformWindow tolerance uniformRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle locatedRead pkg ∧
                                PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet filterLocated locatedTolerance filterUniform uniformTolerance locatedPkg
    uniformPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, _readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _filterWindows,
    _toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have locatedWindowUnary : UnaryHistory locatedWindow :=
    unary_cont_closed filterUnary windowsUnary filterLocated
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed locatedWindowUnary toleranceUnary locatedTolerance
  have uniformWindowUnary : UnaryHistory uniformWindow :=
    unary_cont_closed filterUnary windowsUnary filterUniform
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed uniformWindowUnary toleranceUnary uniformTolerance
  exact
    ⟨locatedUnary, uniformUnary, filterLocated, locatedTolerance, filterUniform,
      uniformTolerance, provenancePkg, locatedPkg, uniformPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
