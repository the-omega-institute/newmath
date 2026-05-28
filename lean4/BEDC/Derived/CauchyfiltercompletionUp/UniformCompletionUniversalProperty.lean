import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionUniformCompletionUniversalProperty [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name uniformRequest
      uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont windows tolerance uniformRequest →
        Cont uniformRequest sealRow uniformRead →
          PkgSig bundle uniformRead pkg →
            SemanticNameCert
              (fun row : BHist =>
                CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport
                    replay provenance name bundle pkg ∧
                  (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                    hsame row readback ∨ hsame row sealRow ∨ hsame row uniformRequest ∨
                      hsame row uniformRead))
              (fun _row : BHist =>
                Cont filter windows tolerance ∧ Cont windows tolerance uniformRequest ∧
                  Cont uniformRequest sealRow uniformRead ∧ Cont transport replay provenance ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle uniformRead pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet windowsTolerance uniformRoute uniformPkg
  have packetWhole := packet
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    _toleranceReadback, transportReplay, provenancePkg, _namePkg⟩ := packet
  have uniformRequestUnary : UnaryHistory uniformRequest :=
    unary_cont_closed windowsUnary toleranceUnary windowsTolerance
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed uniformRequestUnary sealUnary uniformRoute
  have sourceFilter :
      (fun row : BHist =>
        CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
            provenance name bundle pkg ∧
          (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
            hsame row readback ∨ hsame row sealRow ∨ hsame row uniformRequest ∨
              hsame row uniformRead)) filter := by
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
                              | inr rest =>
                                  cases rest with
                                  | inl sameUniformRequest =>
                                      exact
                                        Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                          Or.inr <|
                                            Or.inl
                                              (hsame_trans (hsame_symm sameRows)
                                                sameUniformRequest)
                                  | inr sameUniformRead =>
                                      exact
                                        Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                          Or.inr <| Or.inr <|
                                            hsame_trans (hsame_symm sameRows) sameUniformRead
    }
    pattern_sound := by
      intro _row _source
      exact ⟨filterWindows, windowsTolerance, uniformRoute, transportReplay, provenancePkg,
        uniformPkg⟩
    ledger_sound := by
      intro row source
      cases source with
      | intro _sourcePacket sourceRows =>
          cases sourceRows with
          | inl sameFilter =>
              exact ⟨unary_transport filterUnary (hsame_symm sameFilter), uniformPkg⟩
          | inr rest =>
              cases rest with
              | inl sameWindows =>
                  exact ⟨unary_transport windowsUnary (hsame_symm sameWindows), uniformPkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameTolerance =>
                      exact
                        ⟨unary_transport toleranceUnary (hsame_symm sameTolerance),
                          uniformPkg⟩
                  | inr rest =>
                      cases rest with
                      | inl sameReadback =>
                          exact
                            ⟨unary_transport readbackUnary (hsame_symm sameReadback),
                              uniformPkg⟩
                      | inr rest =>
                          cases rest with
                          | inl sameSeal =>
                              exact
                                ⟨unary_transport sealUnary (hsame_symm sameSeal),
                                  uniformPkg⟩
                          | inr rest =>
                              cases rest with
                              | inl sameUniformRequest =>
                                  exact
                                    ⟨unary_transport uniformRequestUnary
                                        (hsame_symm sameUniformRequest),
                                      uniformPkg⟩
                              | inr sameUniformRead =>
                                  exact
                                    ⟨unary_transport uniformReadUnary
                                        (hsame_symm sameUniformRead),
                                      uniformPkg⟩
  }

end BEDC.Derived.CauchyfiltercompletionUp
