import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_uniform_limit_compatibility [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name uniformLimit
      separatedSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont windows readback uniformLimit →
        Cont uniformLimit sealRow separatedSeal →
          PkgSig bundle uniformLimit pkg →
            PkgSig bundle separatedSeal pkg →
              UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                UnaryHistory sealRow ∧ UnaryHistory uniformLimit ∧
                  UnaryHistory separatedSeal ∧ Cont filter windows tolerance ∧
                    Cont windows readback uniformLimit ∧
                      Cont uniformLimit sealRow separatedSeal ∧
                        Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle separatedSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet limitRoute sealRoute _limitPkg sealPkg
  obtain ⟨filterUnary, windowsUnary, _toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    _toleranceReadback, transportReplay, provenancePkg, _namePkg⟩ := packet
  have limitUnary : UnaryHistory uniformLimit :=
    unary_cont_closed windowsUnary readbackUnary limitRoute
  have separatedUnary : UnaryHistory separatedSeal :=
    unary_cont_closed limitUnary sealUnary sealRoute
  exact
    ⟨filterUnary, windowsUnary, readbackUnary, sealUnary, limitUnary, separatedUnary,
      filterWindows, limitRoute, sealRoute, transportReplay, provenancePkg, sealPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
