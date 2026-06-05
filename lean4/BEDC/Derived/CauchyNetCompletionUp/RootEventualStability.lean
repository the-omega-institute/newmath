import BEDC.Derived.CauchyNetCompletionUp.DirectedWindowTerminality

namespace BEDC.Derived.CauchyNetCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyNetCompletionRootEventualStability [AskSetup] [PackageSetup]
    {directed window request mooreSmith uniform separated readback realSeal transport replay
      provenance name retainedWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCompletionCarrier directed window request mooreSmith uniform separated readback
        realSeal transport replay provenance name bundle pkg →
      Cont window retainedWindow request →
        UnaryHistory retainedWindow →
          ∃ stableRead : BHist,
            UnaryHistory stableRead ∧ hsame stableRead (append retainedWindow separated) ∧
              Cont window retainedWindow request ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: CauchyNetCompletionCarrier BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro carrier retainedRoute retainedUnary
  obtain ⟨_unaryDirected, _unaryWindow, _unaryRequest, _unaryMooreSmith, _unaryUniform,
    unarySeparated, _unaryReadback, _unaryRealSeal, _unaryTransport, _unaryReplay,
      _unaryProvenance, _unaryName, _directedWindowRoute, _requestMooreRoute,
        _uniformSeparatedRoute, _sealRoute, provenancePkg, _namePkg⟩ := carrier
  refine ⟨append retainedWindow separated, ?_, ?_, retainedRoute, provenancePkg⟩
  · exact unary_append_closed retainedUnary unarySeparated
  · exact hsame_refl (append retainedWindow separated)

end BEDC.Derived.CauchyNetCompletionUp
