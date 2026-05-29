import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_basis_real_seal [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name basisRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont windows tolerance basisRead →
        Cont readback sealRow sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
              UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory basisRead ∧
                UnaryHistory sealRead ∧ Cont filter windows tolerance ∧
                  Cont windows tolerance basisRead ∧ Cont tolerance readback sealRow ∧
                    Cont readback sealRow sealRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet windowsToleranceBasis readbackSeal sealPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed windowsUnary toleranceUnary windowsToleranceBasis
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary sealUnary readbackSeal
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, basisUnary,
      sealReadUnary, filterWindows, windowsToleranceBasis, toleranceReadback, readbackSeal,
      provenancePkg, sealPkg⟩

theorem CauchyFilterCompletionPacket_real_seal_basis_exhaustion [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name basisRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont windows tolerance basisRead →
        Cont basisRead sealRow completionRead →
          PkgSig bundle completionRead pkg →
            SemanticNameCert
              (fun row : BHist =>
                CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport
                    replay provenance name bundle pkg ∧
                  (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                    hsame row readback ∨ hsame row sealRow ∨ hsame row basisRead ∨
                      hsame row completionRead))
              (fun _row : BHist =>
                Cont filter windows tolerance ∧ Cont windows tolerance basisRead ∧
                  Cont basisRead sealRow completionRead ∧ Cont transport replay provenance ∧
                    PkgSig bundle provenance pkg)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle completionRead pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet windowsToleranceBasis basisSealCompletion completionPkg
  have packetWhole := packet
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    _toleranceReadback, transportReplay, provenancePkg, _namePkg⟩ := packet
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed windowsUnary toleranceUnary windowsToleranceBasis
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed basisUnary sealUnary basisSealCompletion
  have sourceFilter :
      (fun row : BHist =>
        CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
            provenance name bundle pkg ∧
          (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
            hsame row readback ∨ hsame row sealRow ∨ hsame row basisRead ∨
              hsame row completionRead)) filter := by
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
                                  | inl sameBasis =>
                                      exact
                                        Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                          Or.inr <|
                                            Or.inl
                                              (hsame_trans (hsame_symm sameRows) sameBasis)
                                  | inr sameCompletion =>
                                      exact
                                        Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                          Or.inr <| Or.inr <|
                                            hsame_trans (hsame_symm sameRows) sameCompletion
    }
    pattern_sound := by
      intro _row _source
      exact
        ⟨filterWindows, windowsToleranceBasis, basisSealCompletion, transportReplay,
          provenancePkg⟩
    ledger_sound := by
      intro row source
      cases source with
      | intro _sourcePacket sourceRows =>
          cases sourceRows with
          | inl sameFilter =>
              exact ⟨unary_transport filterUnary (hsame_symm sameFilter), completionPkg⟩
          | inr rest =>
              cases rest with
              | inl sameWindows =>
                  exact ⟨unary_transport windowsUnary (hsame_symm sameWindows), completionPkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameTolerance =>
                      exact
                        ⟨unary_transport toleranceUnary (hsame_symm sameTolerance),
                          completionPkg⟩
                  | inr rest =>
                      cases rest with
                      | inl sameReadback =>
                          exact
                            ⟨unary_transport readbackUnary (hsame_symm sameReadback),
                              completionPkg⟩
                      | inr rest =>
                          cases rest with
                          | inl sameSeal =>
                              exact
                                ⟨unary_transport sealUnary (hsame_symm sameSeal),
                                  completionPkg⟩
                          | inr rest =>
                              cases rest with
                              | inl sameBasis =>
                                  exact
                                    ⟨unary_transport basisUnary (hsame_symm sameBasis),
                                      completionPkg⟩
                              | inr sameCompletion =>
                                  exact
                                    ⟨unary_transport completionUnary
                                        (hsame_symm sameCompletion),
                                      completionPkg⟩
  }

end BEDC.Derived.CauchyfiltercompletionUp
