import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionRootCarrierAdmissionObligation [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name row : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨ hsame row readback ∨
        hsame row sealRow ∨ hsame row transport ∨ hsame row replay ∨
          hsame row provenance ∨ hsame row name) →
        UnaryHistory row := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame
  intro packet rowMember
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    transportUnary, replayUnary, provenanceUnary, nameUnary, _filterWindows,
    _toleranceReadback, _transportReplay, _provenancePkg, _namePkg⟩ := packet
  cases rowMember with
  | inl sameFilter =>
      exact unary_transport filterUnary (hsame_symm sameFilter)
  | inr rest =>
      cases rest with
      | inl sameWindows =>
          exact unary_transport windowsUnary (hsame_symm sameWindows)
      | inr rest =>
          cases rest with
          | inl sameTolerance =>
              exact unary_transport toleranceUnary (hsame_symm sameTolerance)
          | inr rest =>
              cases rest with
              | inl sameReadback =>
                  exact unary_transport readbackUnary (hsame_symm sameReadback)
              | inr rest =>
                  cases rest with
                  | inl sameSeal =>
                      exact unary_transport sealUnary (hsame_symm sameSeal)
                  | inr rest =>
                      cases rest with
                      | inl sameTransport =>
                          exact unary_transport transportUnary (hsame_symm sameTransport)
                      | inr rest =>
                          cases rest with
                          | inl sameReplay =>
                              exact unary_transport replayUnary (hsame_symm sameReplay)
                          | inr rest =>
                              cases rest with
                              | inl sameProvenance =>
                                  exact
                                    unary_transport provenanceUnary
                                      (hsame_symm sameProvenance)
                              | inr sameName =>
                                  exact unary_transport nameUnary (hsame_symm sameName)

end BEDC.Derived.CauchyfiltercompletionUp
