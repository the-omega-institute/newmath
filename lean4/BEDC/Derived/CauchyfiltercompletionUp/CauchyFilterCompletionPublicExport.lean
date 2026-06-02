import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPublicExport [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name rootRead
      completionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter readback rootRead →
        Cont rootRead sealRow completionRead →
          Cont completionRead provenance publicRead →
            PkgSig bundle publicRead pkg →
              UnaryHistory rootRead ∧ UnaryHistory completionRead ∧ UnaryHistory publicRead ∧
                Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                  Cont filter readback rootRead ∧ Cont rootRead sealRow completionRead ∧
                    Cont completionRead provenance publicRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory PkgSig
  intro packet rootRoute completionRoute publicRoute publicPkg
  obtain ⟨filterUnary, _windowsUnary, _toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed filterUnary readbackUnary rootRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed rootUnary sealUnary completionRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed completionUnary provenanceUnary publicRoute
  exact
    ⟨rootUnary, completionUnary, publicUnary, filterWindows, toleranceReadback, rootRoute,
      completionRoute, publicRoute, provenancePkg, publicPkg⟩

theorem CauchyFilterCompletionPublicExportPackage [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name rootRead
      completionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter readback rootRead →
        Cont rootRead sealRow completionRead →
          Cont completionRead provenance publicRead →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row rootRead ∨ hsame row completionRead ∨ hsame row publicRead) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                      hsame row readback ∨ hsame row sealRow ∨ hsame row provenance ∨
                        hsame row rootRead ∨ hsame row completionRead ∨ hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont filter readback rootRead ∧
                      Cont rootRead sealRow completionRead ∧
                        Cont completionRead provenance publicRead ∧
                          PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory rootRead ∧ UnaryHistory completionRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet rootRoute completionRoute publicRoute publicPkg
  obtain ⟨filterUnary, _windowsUnary, _toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, _nameUnary, _filterWindows,
    _toleranceReadback, _transportReplay, _provenancePkg, _namePkg⟩ := packet
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed filterUnary readbackUnary rootRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed rootUnary sealUnary completionRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed completionUnary provenanceUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row rootRead ∨ hsame row completionRead ∨ hsame row publicRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row provenance ∨
                hsame row rootRead ∨ hsame row completionRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont filter readback rootRead ∧
              Cont rootRead sealRow completionRead ∧
                Cont completionRead provenance publicRead ∧ PkgSig bundle publicRead pkg)
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
          | inr rest =>
              cases rest with
              | inl sameCompletion =>
                  exact
                    Or.inr
                      (Or.inl (hsame_trans (hsame_symm sameRows) sameCompletion))
              | inr samePublic =>
                  exact
                    Or.inr
                      (Or.inr (hsame_trans (hsame_symm sameRows) samePublic))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameRoot =>
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl sameRoot
      | inr rest =>
          cases rest with
          | inl sameCompletion =>
              exact
                Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                  Or.inr <| Or.inl sameCompletion
          | inr samePublic =>
              exact
                Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                  Or.inr <| Or.inr samePublic
    ledger_sound := by
      intro _row source
      exact ⟨source.right, rootRoute, completionRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, rootUnary, completionUnary, publicUnary⟩

theorem CauchyFilterCompletionFilterbaseWindowExhaustion [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name filterbase windowRead
      exhausted : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter windows filterbase →
        Cont filterbase tolerance windowRead →
          Cont windowRead readback exhausted →
            PkgSig bundle exhausted pkg →
              UnaryHistory filterbase ∧ UnaryHistory windowRead ∧ UnaryHistory exhausted ∧
                Cont filter windows filterbase ∧ Cont filterbase tolerance windowRead ∧
                  Cont windowRead readback exhausted ∧ Cont tolerance readback sealRow ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle exhausted pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory PkgSig
  intro packet filterbaseRoute windowRoute exhaustionRoute exhaustedPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have filterbaseUnary : UnaryHistory filterbase :=
    unary_cont_closed filterUnary windowsUnary filterbaseRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed filterbaseUnary toleranceUnary windowRoute
  have exhaustedUnary : UnaryHistory exhausted :=
    unary_cont_closed windowUnary readbackUnary exhaustionRoute
  exact
    ⟨filterbaseUnary, windowUnary, exhaustedUnary, filterbaseRoute, windowRoute, exhaustionRoute,
      toleranceReadback, provenancePkg, exhaustedPkg⟩

theorem CauchyFilterCompletionPublicBasisCompletionRoute [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name basisRead sealRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter windows basisRead →
        Cont basisRead tolerance readback →
          Cont readback sealRow sealRead →
            Cont sealRead provenance publicRead →
              PkgSig bundle publicRead pkg →
                UnaryHistory basisRead ∧ UnaryHistory sealRead ∧ UnaryHistory publicRead ∧
                  Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                    Cont transport replay provenance ∧ Cont filter windows basisRead ∧
                      Cont basisRead tolerance readback ∧ Cont readback sealRow sealRead ∧
                        Cont sealRead provenance publicRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory PkgSig
  intro packet basisRoute basisReadbackRoute sealRoute publicRoute publicPkg
  obtain ⟨filterUnary, windowsUnary, _toleranceUnary, readbackUnary, sealUnary,
    transportUnary, replayUnary, provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, transportReplay, provenancePkg, _namePkg⟩ := packet
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed filterUnary windowsUnary basisRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary sealUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary provenanceUnary publicRoute
  exact
    ⟨basisUnary, sealReadUnary, publicUnary, filterWindows, toleranceReadback,
      transportReplay, basisRoute, basisReadbackRoute, sealRoute, publicRoute, provenancePkg,
      publicPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
