import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionRootUnblockCarrier_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
              provenance name bundle pkg ∧
            (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row transport ∨
                hsame row replay ∨ hsame row provenance ∨ hsame row name))
        (fun row : BHist =>
          hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
            hsame row readback ∨ hsame row sealRow ∨ hsame row transport ∨
              hsame row replay ∨ hsame row provenance ∨ hsame row name)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame SemanticNameCert
  intro packet
  have packetWhole := packet
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    transportUnary, replayUnary, provenanceUnary, nameUnary, _filterWindows,
    _toleranceReadback, _transportReplay, provenancePkg, namePkg⟩ := packet
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
        intro _row _other sameRows source
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
                                                  Or.inr <| Or.inr <| Or.inr <|
                                                    Or.inr
                                                      (hsame_trans (hsame_symm sameRows)
                                                        sameName)
    }
    pattern_sound := by
      intro _row source
      exact source.right
    ledger_sound := by
      intro row source
      cases source with
      | intro _sourcePacket sourceRows =>
          cases sourceRows with
          | inl sameFilter =>
              exact
                ⟨unary_transport filterUnary (hsame_symm sameFilter), provenancePkg, namePkg⟩
          | inr rest =>
              cases rest with
              | inl sameWindows =>
                  exact
                    ⟨unary_transport windowsUnary (hsame_symm sameWindows), provenancePkg,
                      namePkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameTolerance =>
                      exact
                        ⟨unary_transport toleranceUnary (hsame_symm sameTolerance),
                          provenancePkg, namePkg⟩
                  | inr rest =>
                      cases rest with
                      | inl sameReadback =>
                          exact
                            ⟨unary_transport readbackUnary (hsame_symm sameReadback),
                              provenancePkg, namePkg⟩
                      | inr rest =>
                          cases rest with
                          | inl sameSeal =>
                              exact
                                ⟨unary_transport sealUnary (hsame_symm sameSeal),
                                  provenancePkg, namePkg⟩
                          | inr rest =>
                              cases rest with
                              | inl sameTransport =>
                                  exact
                                    ⟨unary_transport transportUnary (hsame_symm sameTransport),
                                      provenancePkg, namePkg⟩
                              | inr rest =>
                                  cases rest with
                                  | inl sameReplay =>
                                      exact
                                        ⟨unary_transport replayUnary (hsame_symm sameReplay),
                                          provenancePkg, namePkg⟩
                                  | inr rest =>
                                      cases rest with
                                      | inl sameProvenance =>
                                          exact
                                            ⟨unary_transport provenanceUnary
                                                (hsame_symm sameProvenance),
                                              provenancePkg, namePkg⟩
                                      | inr sameName =>
                                          exact
                                            ⟨unary_transport nameUnary (hsame_symm sameName),
                                              provenancePkg, namePkg⟩
  }

theorem CauchyFilterCompletionRootObligationSurface [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name rootRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter windows rootRead →
        Cont rootRead readback sealRead →
          PkgSig bundle sealRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row rootRead ∨ hsame row sealRead) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                    hsame row readback ∨ hsame row sealRow ∨ hsame row transport ∨
                      hsame row replay ∨ hsame row provenance ∨ hsame row name ∨
                        hsame row rootRead ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont filter windows rootRead ∧
                    Cont rootRead readback sealRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle sealRead pkg)
                hsame ∧
              UnaryHistory rootRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet rootRoute sealRoute sealPkg
  obtain ⟨filterUnary, windowsUnary, _toleranceUnary, readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _filterWindows,
    _toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed filterUnary windowsUnary rootRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rootUnary readbackUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row rootRead ∨ hsame row sealRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row transport ∨
                hsame row replay ∨ hsame row provenance ∨ hsame row name ∨
                  hsame row rootRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont filter windows rootRead ∧
              Cont rootRead readback sealRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro rootRead ⟨Or.inl (hsame_refl rootRead), rootUnary⟩
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
        intro _row _other sameRows source
        constructor
        · cases source.left with
          | inl sameRoot =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameRoot)
          | inr sameSeal =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameSeal)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameRoot =>
          exact
            Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
              Or.inr <| Or.inr <| Or.inr <| Or.inl sameRoot
      | inr sameSeal =>
          exact
            Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
              Or.inr <| Or.inr <| Or.inr <| Or.inr sameSeal
    ledger_sound := by
      intro _row source
      exact ⟨source.right, rootRoute, sealRoute, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, rootUnary, sealUnary⟩

end BEDC.Derived.CauchyfiltercompletionUp
