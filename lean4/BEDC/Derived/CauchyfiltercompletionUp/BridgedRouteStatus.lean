import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_bridged_route [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name bridgeRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont readback sealRow bridgeRead →
        PkgSig bundle bridgeRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport
                    replay provenance name bundle pkg ∧
                  (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                    hsame row readback ∨ hsame row sealRow ∨ hsame row bridgeRead))
              (fun _row : BHist =>
                Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                  Cont readback sealRow bridgeRead ∧ Cont transport replay provenance ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeRead pkg)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle bridgeRead pkg)
              hsame ∧
            UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle PkgSig SemanticNameCert hsame
  intro packet readbackSealBridge bridgePkg
  have packetWhole := packet
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, transportReplay, provenancePkg, _namePkg⟩ := packet
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed readbackUnary sealUnary readbackSealBridge
  have sourceFilter :
      (fun row : BHist =>
        CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
            provenance name bundle pkg ∧
          (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
            hsame row readback ∨ hsame row sealRow ∨ hsame row bridgeRead)) filter := by
    exact ⟨packetWhole, Or.inl (hsame_refl filter)⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport
                replay provenance name bundle pkg ∧
              (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                hsame row readback ∨ hsame row sealRow ∨ hsame row bridgeRead))
          (fun _row : BHist =>
            Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
              Cont readback sealRow bridgeRead ∧ Cont transport replay provenance ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeRead pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle bridgeRead pkg)
          hsame := {
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
                      | inl sameTolerance =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) sameTolerance)))
                      | inr rest =>
                          cases rest with
                          | inl sameReadback =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows) sameReadback))))
                          | inr rest =>
                              cases rest with
                              | inl sameSeal =>
                                  exact
                                    Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                      Or.inl (hsame_trans (hsame_symm sameRows) sameSeal)
                              | inr sameBridge =>
                                  exact
                                    Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                      Or.inr
                                        (hsame_trans (hsame_symm sameRows) sameBridge)
    }
    pattern_sound := by
      intro _row _source
      exact
        ⟨filterWindows, toleranceReadback, readbackSealBridge, transportReplay,
          provenancePkg, bridgePkg⟩
    ledger_sound := by
      intro row source
      cases source with
      | intro _sourcePacket sourceRows =>
          cases sourceRows with
          | inl sameFilter =>
              exact ⟨unary_transport filterUnary (hsame_symm sameFilter), bridgePkg⟩
          | inr rest =>
              cases rest with
              | inl sameWindows =>
                  exact ⟨unary_transport windowsUnary (hsame_symm sameWindows), bridgePkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameTolerance =>
                      exact
                        ⟨unary_transport toleranceUnary (hsame_symm sameTolerance),
                          bridgePkg⟩
                  | inr rest =>
                      cases rest with
                      | inl sameReadback =>
                          exact
                            ⟨unary_transport readbackUnary (hsame_symm sameReadback),
                              bridgePkg⟩
                      | inr rest =>
                          cases rest with
                          | inl sameSeal =>
                              exact
                                ⟨unary_transport sealUnary (hsame_symm sameSeal),
                                  bridgePkg⟩
                          | inr sameBridge =>
                              exact
                                ⟨unary_transport bridgeUnary (hsame_symm sameBridge),
                                  bridgePkg⟩
  }
  exact ⟨cert, bridgeUnary⟩

end BEDC.Derived.CauchyfiltercompletionUp
