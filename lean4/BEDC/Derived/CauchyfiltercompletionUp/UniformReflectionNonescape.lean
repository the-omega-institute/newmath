import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_uniform_reflection_nonescape [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name uniformRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont sealRow provenance uniformRead →
        Cont uniformRead name publicRead →
          PkgSig bundle publicRead pkg →
            SemanticNameCert
              (fun row : BHist => hsame row uniformRead ∨ hsame row publicRead)
              (fun _row : BHist =>
                Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                  Cont sealRow provenance uniformRead ∧ Cont uniformRead name publicRead)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet sealProvenanceUniform uniformNamePublic publicPkg
  obtain ⟨_filterUnary, _windowsUnary, _toleranceUnary, _readbackUnary, sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, nameUnary, filterWindows,
    toleranceReadback, _transportReplay, _provenancePkg, _namePkg⟩ := packet
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed sealUnary provenanceUnary sealProvenanceUniform
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed uniformUnary nameUnary uniformNamePublic
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∨ hsame row publicRead) uniformRead := by
    exact Or.inl (hsame_refl uniformRead)
  exact {
    core := {
      carrier_inhabited := Exists.intro uniformRead sourceUniform
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows source
        cases source with
        | inl sameUniform =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameUniform)
        | inr samePublic =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) samePublic)
    }
    pattern_sound := by
      intro _row _source
      exact
        ⟨filterWindows, toleranceReadback, sealProvenanceUniform, uniformNamePublic⟩
    ledger_sound := by
      intro row source
      cases source with
      | inl sameUniform =>
          exact ⟨unary_transport uniformUnary (hsame_symm sameUniform), publicPkg⟩
      | inr samePublic =>
          exact ⟨unary_transport publicUnary (hsame_symm samePublic), publicPkg⟩
  }

end BEDC.Derived.CauchyfiltercompletionUp
