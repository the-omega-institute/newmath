import BEDC.Derived.RealUniformStructureUp.LocatedCauchyFilterHandoff

namespace BEDC.Derived.RealUniformStructureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealUniformStructureRealEqualityFilterBoundary [AskSetup] [PackageSetup]
    {R M U F D S Q H C P N equalityRead filterRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg →
      Cont Q U equalityRead →
        Cont equalityRead F filterRead →
          Cont filterRead R sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory equalityRead ∧ UnaryHistory filterRead ∧ UnaryHistory sealRead ∧
                Cont Q U equalityRead ∧ Cont equalityRead F filterRead ∧
                  Cont filterRead R sealRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier equalityCont filterCont sealCont sealPkg
  have rUnary : UnaryHistory R := carrier.left
  have uUnary : UnaryHistory U := carrier.right.right.left
  have fUnary : UnaryHistory F := carrier.right.right.right.left
  have qUnary : UnaryHistory Q := carrier.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right
  have equalityUnary : UnaryHistory equalityRead :=
    unary_cont_closed qUnary uUnary equalityCont
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed equalityUnary fUnary filterCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed filterUnary rUnary sealCont
  exact
    ⟨equalityUnary, filterUnary, sealUnary, equalityCont, filterCont, sealCont, pPkg,
      sealPkg⟩

theorem RealUniformStructureLocatedEqualityFilterBoundary [AskSetup] [PackageSetup]
    {R M U F D S Q H C P N endpointRead radiusRead filterRead windowRead readbackRead
      locatedTail equalityRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg →
      Cont R M endpointRead →
        Cont endpointRead D radiusRead →
          Cont radiusRead U filterRead →
            Cont filterRead S windowRead →
              Cont windowRead Q readbackRead →
                Cont readbackRead F locatedTail →
                  Cont locatedTail Q equalityRead →
                    Cont equalityRead R sealRead →
                      PkgSig bundle locatedTail pkg →
                        PkgSig bundle sealRead pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row locatedTail ∨ hsame row Q ∨ hsame row R ∨
                                  hsame row sealRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont readbackRead F locatedTail ∧
                                  Cont locatedTail Q equalityRead ∧
                                    Cont equalityRead R sealRead ∧
                                      PkgSig bundle sealRead pkg)
                              hsame ∧
                            UnaryHistory locatedTail ∧ UnaryHistory equalityRead ∧
                              UnaryHistory sealRead ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle locatedTail pkg ∧
                                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: RealUniformStructureCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier endpointCont radiusCont filterCont windowCont readbackCont locatedCont
    equalityCont sealCont locatedPkg sealPkg
  obtain
    ⟨rUnary, _mUnary, _dUnary, _uUnary, _fUnary, _sUnary, qUnary, _endpointUnary,
      _radiusUnary, _filterUnary, _windowUnary, readbackUnary, locatedUnary,
      _endpointRoute, _radiusRoute, _filterRoute, _windowRoute, _readbackRoute,
      locatedRoute, pPkg, locatedPkgOut⟩ :=
        RealUniformStructureCarrier_located_cauchy_filter_handoff carrier endpointCont
          radiusCont filterCont windowCont readbackCont locatedCont locatedPkg
  have equalityUnary : UnaryHistory equalityRead :=
    unary_cont_closed locatedUnary qUnary equalityCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed equalityUnary rUnary sealCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row locatedTail ∨ hsame row Q ∨ hsame row R ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont readbackRead F locatedTail ∧
              Cont locatedTail Q equalityRead ∧ Cont equalityRead R sealRead ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, locatedRoute, equalityCont, sealCont, sealPkg⟩
  }
  exact ⟨cert, locatedUnary, equalityUnary, sealUnary, pPkg, locatedPkgOut, sealPkg⟩

end BEDC.Derived.RealUniformStructureUp
