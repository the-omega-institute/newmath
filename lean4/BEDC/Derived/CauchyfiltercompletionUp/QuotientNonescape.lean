import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_quotient_nonescape [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
              provenance name bundle pkg ∧
            (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row transport ∨
                hsame row replay ∨ hsame row provenance ∨ hsame row name))
        (fun _row : BHist =>
          Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
            Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg)
        (fun row : BHist =>
          UnaryHistory row ∧
            (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row transport ∨
                hsame row replay ∨ hsame row provenance ∨ hsame row name))
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet
  have packetWhole := packet
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    transportUnary, replayUnary, provenanceUnary, nameUnary, filterWindows,
    toleranceReadback, transportReplay, provenancePkg, namePkg⟩ := packet
  have sourceFilter :
      (fun row : BHist =>
        CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
            provenance name bundle pkg ∧
          (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
            hsame row readback ∨ hsame row sealRow ∨ hsame row transport ∨
              hsame row replay ∨ hsame row provenance ∨ hsame row name)) filter := by
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
                      | inl sameTolerance =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) sameTolerance)))
                      | inr rest =>
                          cases rest with
                          | inl sameReadback =>
                              exact
                                Or.inr <| Or.inr <| Or.inr <|
                                  Or.inl (hsame_trans (hsame_symm sameRows) sameReadback)
                          | inr rest =>
                              cases rest with
                              | inl sameSeal =>
                                  exact
                                    Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                      Or.inl (hsame_trans (hsame_symm sameRows) sameSeal)
                              | inr rest =>
                                  cases rest with
                                  | inl sameTransport =>
                                      exact
                                        Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                          Or.inr <|
                                            Or.inl
                                              (hsame_trans (hsame_symm sameRows) sameTransport)
                                  | inr rest =>
                                      cases rest with
                                      | inl sameReplay =>
                                          exact
                                            Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                              Or.inr <| Or.inr <|
                                                Or.inl
                                                  (hsame_trans (hsame_symm sameRows) sameReplay)
                                      | inr rest =>
                                          cases rest with
                                          | inl sameProvenance =>
                                              exact
                                                Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                                  Or.inr <| Or.inr <| Or.inr <|
                                                    Or.inl
                                                      (hsame_trans (hsame_symm sameRows)
                                                        sameProvenance)
                                          | inr sameName =>
                                              exact
                                                Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                                  Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                                    hsame_trans (hsame_symm sameRows) sameName
    }
    pattern_sound := by
      intro _row _source
      exact ⟨filterWindows, toleranceReadback, transportReplay, provenancePkg, namePkg⟩
    ledger_sound := by
      intro row source
      cases source with
      | intro _sourcePacket sourceRows =>
          cases sourceRows with
          | inl sameFilter =>
              exact
                ⟨unary_transport filterUnary (hsame_symm sameFilter),
                  Or.inl sameFilter⟩
          | inr rest =>
              cases rest with
              | inl sameWindows =>
                  exact
                    ⟨unary_transport windowsUnary (hsame_symm sameWindows),
                      Or.inr (Or.inl sameWindows)⟩
              | inr rest =>
                  cases rest with
                  | inl sameTolerance =>
                      exact
                        ⟨unary_transport toleranceUnary (hsame_symm sameTolerance),
                          Or.inr (Or.inr (Or.inl sameTolerance))⟩
                  | inr rest =>
                      cases rest with
                      | inl sameReadback =>
                          exact
                            ⟨unary_transport readbackUnary (hsame_symm sameReadback),
                              Or.inr (Or.inr (Or.inr (Or.inl sameReadback)))⟩
                      | inr rest =>
                          cases rest with
                          | inl sameSeal =>
                              exact
                                ⟨unary_transport sealUnary (hsame_symm sameSeal),
                                  Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                    Or.inl sameSeal⟩
                          | inr rest =>
                              cases rest with
                              | inl sameTransport =>
                                  exact
                                    ⟨unary_transport transportUnary (hsame_symm sameTransport),
                                      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                        Or.inl sameTransport⟩
                              | inr rest =>
                                  cases rest with
                                  | inl sameReplay =>
                                      exact
                                        ⟨unary_transport replayUnary (hsame_symm sameReplay),
                                          Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                            Or.inr <| Or.inl sameReplay⟩
                                  | inr rest =>
                                      cases rest with
                                      | inl sameProvenance =>
                                          exact
                                            ⟨unary_transport provenanceUnary
                                                (hsame_symm sameProvenance),
                                              Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                                Or.inr <| Or.inr <| Or.inr <|
                                                  Or.inl sameProvenance⟩
                                      | inr sameName =>
                                          exact
                                            ⟨unary_transport nameUnary (hsame_symm sameName),
                                              Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                                Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                                  sameName⟩
  }

end BEDC.Derived.CauchyfiltercompletionUp
