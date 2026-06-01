import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_completion_scope [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name
      scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter readback scopeRead →
        PkgSig bundle scopeRead pkg →
          SemanticNameCert
            (fun row : BHist =>
              CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport
                  replay provenance name bundle pkg ∧
                (hsame row filter ∨ hsame row windows ∨ hsame row readback ∨
                  hsame row sealRow ∨ hsame row scopeRead))
            (fun _row : BHist =>
              Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                Cont filter readback scopeRead ∧ PkgSig bundle provenance pkg)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle scopeRead pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet filterReadbackScope scopePkg
  have packetWhole := packet
  obtain ⟨filterUnary, windowsUnary, _toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed filterUnary readbackUnary filterReadbackScope
  have sourceFilter :
      (fun row : BHist =>
        CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
            provenance name bundle pkg ∧
          (hsame row filter ∨ hsame row windows ∨ hsame row readback ∨
            hsame row sealRow ∨ hsame row scopeRead)) filter := by
    exact ⟨packetWhole, Or.inl (hsame_refl filter)⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro filter sourceFilter
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
        | intro sourcePacket sourceRows =>
            constructor
            · exact sourcePacket
            · cases sourceRows with
              | inl sameFilter =>
                  exact Or.inl (hsame_trans (hsame_symm sameRows) sameFilter)
              | inr rest =>
                  cases rest with
                  | inl sameWindows =>
                      exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameWindows))
                  | inr rest =>
                      cases rest with
                      | inl sameReadback =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) sameReadback)))
                      | inr rest =>
                          cases rest with
                          | inl sameSeal =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl (hsame_trans (hsame_symm sameRows) sameSeal))))
                          | inr sameScope =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (hsame_trans (hsame_symm sameRows) sameScope))))
    }
    pattern_sound := by
      intro _row _source
      exact ⟨filterWindows, toleranceReadback, filterReadbackScope, provenancePkg⟩
    ledger_sound := by
      intro row source
      cases source with
      | intro _sourcePacket sourceRows =>
          cases sourceRows with
          | inl sameFilter =>
              exact ⟨unary_transport filterUnary (hsame_symm sameFilter), scopePkg⟩
          | inr rest =>
              cases rest with
              | inl sameWindows =>
                  exact ⟨unary_transport windowsUnary (hsame_symm sameWindows), scopePkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameReadback =>
                      exact ⟨unary_transport readbackUnary (hsame_symm sameReadback), scopePkg⟩
                  | inr rest =>
                      cases rest with
                      | inl sameSeal =>
                          exact ⟨unary_transport sealUnary (hsame_symm sameSeal), scopePkg⟩
                      | inr sameScope =>
                          exact ⟨unary_transport scopeUnary (hsame_symm sameScope), scopePkg⟩
  }

end BEDC.Derived.CauchyfiltercompletionUp
