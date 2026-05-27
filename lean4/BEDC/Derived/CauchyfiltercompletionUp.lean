import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyFilterCompletionPacket [AskSetup] [PackageSetup]
    (filter windows tolerance readback sealRow transport replay provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
    UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
          Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle name pkg

theorem CauchyFilterCompletionPacket_source_exactness [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
        UnaryHistory readback ∧ UnaryHistory sealRow ∧ Cont filter windows tolerance ∧
          Cont tolerance readback sealRow ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, filterWindows,
      toleranceReadback, provenancePkg⟩

theorem CauchyFilterCompletionPacket_ledger_exhaustion [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
        UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
          UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
            Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
              Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    transportUnary, replayUnary, provenanceUnary, nameUnary, filterWindows,
    toleranceReadback, transportReplay, provenancePkg, namePkg⟩ := packet
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, transportUnary,
      replayUnary, provenanceUnary, nameUnary, filterWindows, toleranceReadback, transportReplay,
      provenancePkg, namePkg⟩

theorem CauchyFilterCompletionPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
              provenance name bundle pkg ∧
            (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
              hsame row readback ∨ hsame row sealRow))
        (fun _row : BHist =>
          Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
            Cont transport replay provenance ∧ PkgSig bundle provenance pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet
  have packetWhole := packet
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, transportReplay, provenancePkg, _namePkg⟩ := packet
  have sourceFilter :
      (fun row : BHist =>
        CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
            provenance name bundle pkg ∧
          (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
            hsame row readback ∨ hsame row sealRow)) filter := by
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
                          | inr sameSeal =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (hsame_trans (hsame_symm sameRows) sameSeal))))
    }
    pattern_sound := by
      intro _row source
      exact ⟨filterWindows, toleranceReadback, transportReplay, provenancePkg⟩
    ledger_sound := by
      intro row source
      cases source with
      | intro _sourcePacket sourceRows =>
          cases sourceRows with
          | inl sameFilter =>
              exact ⟨unary_transport filterUnary (hsame_symm sameFilter), provenancePkg⟩
          | inr rest =>
              cases rest with
              | inl sameWindows =>
                  exact ⟨unary_transport windowsUnary (hsame_symm sameWindows), provenancePkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameTolerance =>
                      exact
                        ⟨unary_transport toleranceUnary (hsame_symm sameTolerance),
                          provenancePkg⟩
                  | inr rest =>
                      cases rest with
                      | inl sameReadback =>
                          exact
                            ⟨unary_transport readbackUnary (hsame_symm sameReadback),
                              provenancePkg⟩
                      | inr sameSeal =>
                          exact
                            ⟨unary_transport sealUnary (hsame_symm sameSeal), provenancePkg⟩
  }

theorem CauchyFilterCompletionRootWindowExposure [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name exposure : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg ->
      Cont windows tolerance exposure ->
        PkgSig bundle exposure pkg ->
          UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
            UnaryHistory readback ∧ UnaryHistory exposure ∧ Cont filter windows tolerance ∧
              Cont windows tolerance exposure ∧ Cont tolerance readback sealRow ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle exposure pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet windowsToleranceExposure exposurePkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have exposureUnary : UnaryHistory exposure :=
    unary_cont_closed windowsUnary toleranceUnary windowsToleranceExposure
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, exposureUnary, filterWindows,
      windowsToleranceExposure, toleranceReadback, provenancePkg, exposurePkg⟩

theorem CauchyFilterCompletionRootSurface_semantic_name_certificate [AskSetup] [PackageSetup]
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
        (fun _row : BHist =>
          Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
            Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg)
        (fun row : BHist =>
          UnaryHistory row ∧ (PkgSig bundle provenance pkg ∨ PkgSig bundle name pkg))
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet
  have packetWhole := packet
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    transportUnary, replayUnary, provenanceUnary, nameUnary, filterWindows, toleranceReadback,
    transportReplay, provenancePkg, namePkg⟩ := packet
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
                ⟨unary_transport filterUnary (hsame_symm sameFilter), Or.inl provenancePkg⟩
          | inr rest =>
              cases rest with
              | inl sameWindows =>
                  exact
                    ⟨unary_transport windowsUnary (hsame_symm sameWindows), Or.inl provenancePkg⟩
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
  }

theorem CauchyFilterCompletion_basis_real_seal_transport [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      hsame sealRow sealRead →
        UnaryHistory sealRead ∧ Cont filter windows tolerance ∧
          Cont tolerance readback sealRow ∧ Cont transport replay provenance ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro packet sameSeal
  obtain ⟨_filterUnary, _windowsUnary, _toleranceUnary, _readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, transportReplay, provenancePkg, _namePkg⟩ := packet
  exact
    ⟨unary_transport sealUnary sameSeal, filterWindows, toleranceReadback, transportReplay,
      provenancePkg⟩

theorem CauchyFilterCompletionPacket_basis_totality [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name basisRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      PkgSig bundle basisRead pkg →
        SemanticNameCert
          (fun row : BHist =>
            CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
                provenance name bundle pkg ∧
              (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                hsame row readback ∨ hsame row sealRow))
          (fun _row : BHist =>
            Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
              Cont transport replay provenance ∧ PkgSig bundle provenance pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle basisRead pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet basisPkg
  have packetWhole := packet
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, transportReplay, provenancePkg, _namePkg⟩ := packet
  have sourceFilter :
      (fun row : BHist =>
        CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
            provenance name bundle pkg ∧
          (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
            hsame row readback ∨ hsame row sealRow)) filter := by
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
                          | inr sameSeal =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (hsame_trans (hsame_symm sameRows) sameSeal))))
    }
    pattern_sound := by
      intro _row _source
      exact ⟨filterWindows, toleranceReadback, transportReplay, provenancePkg⟩
    ledger_sound := by
      intro row source
      cases source with
      | intro _sourcePacket sourceRows =>
          cases sourceRows with
          | inl sameFilter =>
              exact ⟨unary_transport filterUnary (hsame_symm sameFilter), basisPkg⟩
          | inr rest =>
              cases rest with
              | inl sameWindows =>
                  exact ⟨unary_transport windowsUnary (hsame_symm sameWindows), basisPkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameTolerance =>
                      exact
                        ⟨unary_transport toleranceUnary (hsame_symm sameTolerance),
                          basisPkg⟩
                  | inr rest =>
                      cases rest with
                      | inl sameReadback =>
                          exact
                            ⟨unary_transport readbackUnary (hsame_symm sameReadback),
                              basisPkg⟩
                      | inr sameSeal =>
                          exact ⟨unary_transport sealUnary (hsame_symm sameSeal), basisPkg⟩
  }

end BEDC.Derived.CauchyfiltercompletionUp
