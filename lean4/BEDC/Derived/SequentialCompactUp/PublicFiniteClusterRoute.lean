import BEDC.Derived.SequentialCompactUp.RootObligationSurface

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactPublicFiniteClusterRoute [AskSetup] [PackageSetup]
    {K B S W R E H C P N baireRead streamRead windowRead readbackRead sealRead namedRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont K B baireRead ->
        Cont baireRead S streamRead ->
          Cont streamRead W windowRead ->
            Cont windowRead R readbackRead ->
              Cont readbackRead E sealRead ->
                Cont sealRead N namedRead ->
                  Cont namedRead P publicRead ->
                    PkgSig bundle publicRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
                              hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                                hsame row P ∨ hsame row N ∨ hsame row publicRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont K B baireRead ∧
                              Cont baireRead S streamRead ∧ Cont streamRead W windowRead ∧
                                Cont windowRead R readbackRead ∧
                                  Cont readbackRead E sealRead ∧
                                    Cont sealRead N namedRead ∧
                                      Cont namedRead P publicRead ∧
                                        PkgSig bundle publicRead pkg)
                          hsame ∧
                        UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier baireRoute streamRoute windowRoute readbackRoute sealRoute namedRoute
    publicRoute publicPkg
  obtain ⟨unaryK, unaryB, unaryS, unaryW, unaryR, unaryE, _unaryH, _unaryC, unaryP,
    unaryN, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, _provenancePkg⟩ := carrier
  have baireUnary : UnaryHistory baireRead :=
    unary_cont_closed unaryK unaryB baireRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed baireUnary unaryS streamRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed streamUnary unaryW windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary unaryR readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary unaryE sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary unaryN namedRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed namedUnary unaryP publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K B baireRead ∧ Cont baireRead S streamRead ∧
              Cont streamRead W windowRead ∧ Cont windowRead R readbackRead ∧
                Cont readbackRead E sealRead ∧ Cont sealRead N namedRead ∧
                  Cont namedRead P publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, baireRoute, streamRoute, windowRoute, readbackRoute, sealRoute,
          namedRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

theorem SequentialCompactPublicClusterExport [AskSetup] [PackageSetup]
    {K B S W R E H C P N clusterRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont W R clusterRead -> Cont clusterRead E publicRead -> PkgSig bundle publicRead pkg ->
        SemanticNameCert (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row clusterRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R clusterRead ∧ Cont clusterRead E publicRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
          hsame ∧ UnaryHistory clusterRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier clusterRoute publicRoute publicPkg
  obtain ⟨_kUnary, _bUnary, _sUnary, unaryW, unaryR, unaryE, _hUnary, _cUnary,
    _pUnary, _nUnary, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, provenancePkg⟩ := carrier
  have clusterUnary : UnaryHistory clusterRead :=
    unary_cont_closed unaryW unaryR clusterRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed clusterUnary unaryE publicRoute
  have cert :
      SemanticNameCert (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
            hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
              hsame row clusterRead ∨ hsame row publicRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont W R clusterRead ∧ Cont clusterRead E publicRead ∧
            PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, clusterRoute, publicRoute, provenancePkg, publicPkg⟩
  }
  exact ⟨cert, clusterUnary, publicUnary⟩

end BEDC.Derived.SequentialCompactUp
