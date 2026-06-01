import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_non_choice_boundary [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name refused : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      hsame refused filter ∨ hsame refused windows ∨ hsame refused tolerance ∨
        hsame refused readback ∨ hsame refused sealRow ∨ hsame refused transport ∨
          hsame refused replay ∨ hsame refused provenance ∨ hsame refused name →
        UnaryHistory refused ∧ (PkgSig bundle provenance pkg ∨ PkgSig bundle name pkg) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame PkgSig
  intro packet displayedRow
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    transportUnary, replayUnary, provenanceUnary, nameUnary, _filterWindows,
    _toleranceReadback, _transportReplay, provenancePkg, namePkg⟩ := packet
  cases displayedRow with
  | inl sameFilter =>
      exact ⟨unary_transport filterUnary (hsame_symm sameFilter), Or.inl provenancePkg⟩
  | inr rest =>
      cases rest with
      | inl sameWindows =>
          exact ⟨unary_transport windowsUnary (hsame_symm sameWindows), Or.inl provenancePkg⟩
      | inr rest =>
          cases rest with
          | inl sameTolerance =>
              exact
                ⟨unary_transport toleranceUnary (hsame_symm sameTolerance),
                  Or.inl provenancePkg⟩
          | inr rest =>
              cases rest with
              | inl sameReadback =>
                  exact
                    ⟨unary_transport readbackUnary (hsame_symm sameReadback),
                      Or.inl provenancePkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameSeal =>
                      exact
                        ⟨unary_transport sealUnary (hsame_symm sameSeal),
                          Or.inl provenancePkg⟩
                  | inr rest =>
                      cases rest with
                      | inl sameTransport =>
                          exact
                            ⟨unary_transport transportUnary (hsame_symm sameTransport),
                              Or.inl provenancePkg⟩
                      | inr rest =>
                          cases rest with
                          | inl sameReplay =>
                              exact
                                ⟨unary_transport replayUnary (hsame_symm sameReplay),
                                  Or.inl provenancePkg⟩
                          | inr rest =>
                              cases rest with
                              | inl sameProvenance =>
                                  exact
                                    ⟨unary_transport provenanceUnary
                                        (hsame_symm sameProvenance),
                                      Or.inl provenancePkg⟩
                              | inr sameName =>
                                  exact
                                    ⟨unary_transport nameUnary (hsame_symm sameName),
                                      Or.inr namePkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
