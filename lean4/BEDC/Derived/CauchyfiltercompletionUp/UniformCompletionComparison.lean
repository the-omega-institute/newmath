import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_uniform_completion_comparison [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name uniformRead
      comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont sealRow provenance uniformRead →
        Cont uniformRead name comparisonRead →
          PkgSig bundle comparisonRead pkg →
            UnaryHistory uniformRead ∧ UnaryHistory comparisonRead ∧
              Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                Cont sealRow provenance uniformRead ∧
                  Cont uniformRead name comparisonRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle comparisonRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet sealProvenanceUniform uniformNameComparison comparisonPkg
  obtain ⟨_filterUnary, _windowsUnary, _toleranceUnary, _readbackUnary, sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed sealUnary provenanceUnary sealProvenanceUniform
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed uniformUnary nameUnary uniformNameComparison
  exact
    ⟨uniformUnary, comparisonUnary, filterWindows, toleranceReadback, sealProvenanceUniform,
      uniformNameComparison, provenancePkg, comparisonPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
