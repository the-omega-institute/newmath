import BEDC.Derived.HeineBorelIntervalUp.MeshRefinement

namespace BEDC.Derived.HeineBorelIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HeineBorelIntervalCarrier [AskSetup] [PackageSetup]
    (A B K M Z F T S R E Q C P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory K ∧ UnaryHistory M ∧
    UnaryHistory Z ∧ UnaryHistory F ∧ UnaryHistory T ∧ UnaryHistory S ∧
      UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory Q ∧ UnaryHistory C ∧
        UnaryHistory P ∧ UnaryHistory N ∧ Cont A B K ∧ Cont K M Z ∧
          Cont F T S ∧ PkgSig bundle Q pkg ∧ PkgSig bundle N pkg

theorem HeineBorelIntervalCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {A B K M Z F T S R E Q C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HeineBorelIntervalCarrier A B K M Z F T S R E Q C P N bundle pkg →
      PkgSig bundle N pkg →
        SemanticNameCert
            (fun row : BHist => hsame row N ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row N ∨ hsame row A ∨ hsame row B ∨ hsame row K ∨
                hsame row M ∨ hsame row Z ∨ hsame row F ∨ hsame row T ∨
                  hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row Q ∨
                    hsame row C ∨ hsame row P)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont A B K ∧ Cont K M Z ∧ Cont F T S ∧
                PkgSig bundle Q pkg ∧ PkgSig bundle N pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier namePkg
  obtain ⟨_aUnary, _bUnary, _kUnary, _mUnary, _zUnary, _fUnary, _tUnary, _sUnary,
    _rUnary, _eUnary, _qUnary, _cUnary, _pUnary, nUnary, abkRoute, kmzRoute,
    ftsRoute, qPkg, _carrierNamePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, nUnary⟩
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
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, abkRoute, kmzRoute, ftsRoute, qPkg, namePkg⟩
  }

theorem HeineBorelIntervalNameCertObligationSurface [AskSetup] [PackageSetup]
    {A B K M Z F T S R E Q C P N net mesh coverageRead stableRead inductionRead sealRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HeineBorelIntervalCoverageRoute
        (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
        net mesh coverageRead bundle pkg →
      UnaryHistory T →
        UnaryHistory E →
          UnaryHistory N →
            Cont coverageRead T stableRead →
              HeineBorelIntervalFiniteNetInductionRoute
                  (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
                  stableRead inductionRead bundle pkg →
                Cont inductionRead E sealRead →
                  Cont sealRead N publicRead →
                    PkgSig bundle stableRead pkg →
                      PkgSig bundle sealRead pkg →
                        PkgSig bundle publicRead pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row coverageRead ∨ hsame row stableRead ∨
                                  hsame row inductionRead ∨ hsame row sealRead ∨
                                    hsame row publicRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont coverageRead T stableRead ∧
                                  Cont inductionRead E sealRead ∧
                                    Cont sealRead N publicRead ∧
                                      PkgSig bundle publicRead pkg)
                              hsame ∧
                            UnaryHistory stableRead ∧ UnaryHistory inductionRead ∧
                              UnaryHistory sealRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro coverageRoute tailUnary eUnary nUnary coverageTailStable inductionRoute
    inductionSeal sealPublic stablePkg _sealPkg publicPkg
  have coverageResult :
      SemanticNameCert
          (fun row : BHist => hsame row coverageRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row net ∨ hsame row mesh ∨ hsame row coverageRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont net mesh coverageRead ∧ PkgSig bundle coverageRead pkg)
          hsame ∧
        UnaryHistory coverageRead :=
    HeineBorelIntervalNetCoverage
      (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
      coverageRoute
  have coverageUnary : UnaryHistory coverageRead := coverageResult.right
  have stableUnary : UnaryHistory stableRead :=
    unary_cont_closed coverageUnary tailUnary coverageTailStable
  have refinementResult :
      SemanticNameCert
          (fun row : BHist => hsame row inductionRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row stableRead ∨ hsame row inductionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont coverageRead T stableRead ∧
              HeineBorelIntervalFiniteNetInductionRoute
                (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
                stableRead inductionRead bundle pkg)
          hsame ∧
        UnaryHistory inductionRead :=
    HeineBorelIntervalMeshRefinementFunctoriality
      coverageRoute tailUnary coverageTailStable stablePkg inductionRoute
  have inductionUnary : UnaryHistory inductionRead := refinementResult.right
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed inductionUnary eUnary inductionSeal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary nUnary sealPublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row coverageRead ∨ hsame row stableRead ∨ hsame row inductionRead ∨
              hsame row sealRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont coverageRead T stableRead ∧
              Cont inductionRead E sealRead ∧ Cont sealRead N publicRead ∧
                PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead
        ⟨hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, coverageTailStable, inductionSeal, sealPublic, publicPkg⟩
  }
  exact ⟨cert, stableUnary, inductionUnary, sealUnary, publicUnary⟩

end BEDC.Derived.HeineBorelIntervalUp
