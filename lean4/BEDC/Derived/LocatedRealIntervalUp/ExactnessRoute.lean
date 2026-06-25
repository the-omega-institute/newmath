import BEDC.Derived.LocatedRealIntervalUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.LocatedRealIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedRealIntervalCarrier_exactness_route
    {L U rho Delta Lambda M bracket endpointRead radiusRead dyadicIntervalRead
      locatorRead modulusRead bracketRead : BHist} :
    UnaryHistory L ->
      UnaryHistory U ->
        UnaryHistory rho ->
          UnaryHistory Delta ->
            UnaryHistory Lambda ->
              UnaryHistory M ->
                UnaryHistory bracket ->
                  Cont L U endpointRead ->
                    Cont endpointRead rho radiusRead ->
                      Cont radiusRead Delta dyadicIntervalRead ->
                        Cont dyadicIntervalRead Lambda locatorRead ->
                          Cont locatorRead M modulusRead ->
                            Cont modulusRead bracket bracketRead ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row bracketRead ∧
                                    UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row endpointRead ∨ hsame row radiusRead ∨
                                      hsame row dyadicIntervalRead ∨
                                        hsame row locatorRead ∨ hsame row modulusRead ∨
                                          hsame row bracketRead)
                                  (fun row : BHist =>
                                    hsame row bracketRead ∧
                                      Cont modulusRead bracket bracketRead)
                                  hsame ∧
                                UnaryHistory endpointRead ∧ UnaryHistory radiusRead ∧
                                  UnaryHistory dyadicIntervalRead ∧ UnaryHistory locatorRead ∧
                                    UnaryHistory modulusRead ∧ UnaryHistory bracketRead ∧
                                      Cont L U endpointRead ∧
                                        Cont endpointRead rho radiusRead ∧
                                          Cont radiusRead Delta dyadicIntervalRead ∧
                                            Cont dyadicIntervalRead Lambda locatorRead ∧
                                              Cont locatorRead M modulusRead ∧
                                                Cont modulusRead bracket bracketRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro unaryL unaryU unaryRho unaryDelta unaryLambda unaryM unaryBracket endpointRoute
    radiusRoute dyadicIntervalRoute locatorRoute modulusRoute bracketRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed unaryL unaryU endpointRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed endpointUnary unaryRho radiusRoute
  have dyadicIntervalUnary : UnaryHistory dyadicIntervalRead :=
    unary_cont_closed radiusUnary unaryDelta dyadicIntervalRoute
  have locatorUnary : UnaryHistory locatorRead :=
    unary_cont_closed dyadicIntervalUnary unaryLambda locatorRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed locatorUnary unaryM modulusRoute
  have bracketReadUnary : UnaryHistory bracketRead :=
    unary_cont_closed modulusUnary unaryBracket bracketRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bracketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row endpointRead ∨ hsame row radiusRead ∨ hsame row dyadicIntervalRead ∨
              hsame row locatorRead ∨ hsame row modulusRead ∨ hsame row bracketRead)
          (fun row : BHist => hsame row bracketRead ∧ Cont modulusRead bracket bracketRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bracketRead
        ⟨hsame_refl bracketRead, bracketReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, bracketRoute⟩
  }
  exact
    ⟨cert, endpointUnary, radiusUnary, dyadicIntervalUnary, locatorUnary, modulusUnary,
      bracketReadUnary, endpointRoute, radiusRoute, dyadicIntervalRoute, locatorRoute,
      modulusRoute, bracketRoute⟩

theorem LocatedRealIntervalCarrier_boundary_exactness_namecert_surface [AskSetup] [PackageSetup]
    {L U rho Delta Lambda M bracket F D W R E H C P N endpointRead radiusRead
      dyadicIntervalRead locatorRead modulusRead bracketRead sourceRead refusalRead dyadicRead
      readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L ->
      UnaryHistory U ->
        UnaryHistory rho ->
          UnaryHistory Delta ->
            UnaryHistory Lambda ->
              UnaryHistory M ->
                UnaryHistory bracket ->
                  BEDC.Derived.CauchyQuotientBoundaryUp.CauchyQuotientBoundaryCarrier
                      bracketRead bracket F D W R E H C P N bundle pkg ->
                    Cont L U endpointRead ->
                      Cont endpointRead rho radiusRead ->
                        Cont radiusRead Delta dyadicIntervalRead ->
                          Cont dyadicIntervalRead Lambda locatorRead ->
                            Cont locatorRead M modulusRead ->
                              Cont modulusRead bracket bracketRead ->
                                Cont bracketRead W sourceRead ->
                                  Cont sourceRead F refusalRead ->
                                    Cont refusalRead D dyadicRead ->
                                      Cont dyadicRead R readbackRead ->
                                        Cont readbackRead E sealRead ->
                                          PkgSig bundle sealRead pkg ->
                                            SemanticNameCert
                                                (fun row : BHist => hsame row bracketRead ∧
                                                  UnaryHistory row)
                                                (fun row : BHist =>
                                                  hsame row endpointRead ∨
                                                    hsame row radiusRead ∨
                                                      hsame row dyadicIntervalRead ∨
                                                        hsame row locatorRead ∨
                                                          hsame row modulusRead ∨
                                                            hsame row bracketRead)
                                                (fun row : BHist =>
                                                  hsame row bracketRead ∧
                                                    Cont modulusRead bracket bracketRead)
                                                hsame ∧
                                              UnaryHistory sourceRead ∧
                                                UnaryHistory refusalRead ∧
                                                  UnaryHistory dyadicRead ∧
                                                    UnaryHistory readbackRead ∧
                                                      UnaryHistory sealRead ∧
                                                        PkgSig bundle P pkg ∧
                                                          PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert UnaryHistory PkgSig
  intro unaryL unaryU unaryRho unaryDelta unaryLambda unaryM unaryBracket boundaryCarrier
    endpointRoute radiusRoute dyadicIntervalRoute locatorRoute modulusRoute bracketRoute
    sourceRoute refusalRoute dyadicRoute readbackRoute sealRoute sealPkg
  have exactnessSurface :=
    LocatedRealIntervalCarrier_exactness_route unaryL unaryU unaryRho unaryDelta unaryLambda
      unaryM unaryBracket endpointRoute radiusRoute dyadicIntervalRoute locatorRoute modulusRoute
      bracketRoute
  have boundarySurface :=
    LocatedRealIntervalCarrier_cauchy_quotient_boundary_route boundaryCarrier endpointRoute
      radiusRoute dyadicIntervalRoute locatorRoute modulusRoute bracketRoute sourceRoute
      refusalRoute dyadicRoute readbackRoute sealRoute sealPkg
  obtain ⟨cert, _endpointUnary, _radiusUnary, _dyadicIntervalUnary, _locatorUnary,
    _modulusUnary, _bracketReadUnary, _endpointRoute, _radiusRoute, _dyadicIntervalRoute,
    _locatorRoute, _modulusRoute, _bracketRoute⟩ := exactnessSurface
  obtain ⟨_endpointRoute', _radiusRoute', _dyadicIntervalRoute', _locatorRoute',
    _modulusRoute', _bracketRoute', sourceUnary, refusalUnary, dyadicUnary, readbackUnary,
    sealUnary, _sourceRoute, _refusalRoute, _dyadicRoute, _readbackRoute, _sealRoute,
    provenancePkg, sealPkgOut⟩ := boundarySurface
  exact
    ⟨cert, sourceUnary, refusalUnary, dyadicUnary, readbackUnary, sealUnary, provenancePkg,
      sealPkgOut⟩

end BEDC.Derived.LocatedRealIntervalUp
