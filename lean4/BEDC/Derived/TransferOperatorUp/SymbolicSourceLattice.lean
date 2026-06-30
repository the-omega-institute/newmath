import BEDC.Derived.TransferOperatorUp.NameCertObligations

namespace BEDC.Derived.TransferOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem TransferOperator_symbolic_source_lattice [AskSetup] [PackageSetup]
    {adjacency golden subshift fibonacci matrix classifier route provenance localName
      supportRead entryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TransferOperatorCarrier adjacency golden subshift fibonacci matrix classifier route provenance
        localName bundle pkg ->
      Cont adjacency golden supportRead ->
        Cont supportRead fibonacci entryRead ->
          PkgSig bundle entryRead pkg ->
            hsame adjacency route ∧ hsame golden route ∧ hsame fibonacci route ∧
              hsame matrix route ∧ hsame subshift route ∧ hsame supportRead route ∧
                hsame entryRead route ∧ Cont adjacency golden supportRead ∧
                  Cont supportRead fibonacci entryRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg ∧ PkgSig bundle entryRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame
  intro carrier supportRoute entryRoute entryPkg
  obtain ⟨_classifierSelf, matrixEmpty, goldenEmpty, fibonacciEmpty, routeEmpty, matrixRoute,
    adjacencyGolden, _subshiftFibonacci, provenancePkg, localNamePkg⟩ := carrier
  have adjacencyRoute : hsame adjacency route := by
    cases matrixEmpty
    cases routeEmpty
    exact matrixRoute
  have goldenRoute : hsame golden route := by
    cases routeEmpty
    exact goldenEmpty
  have fibonacciRoute : hsame fibonacci route := by
    cases routeEmpty
    exact fibonacciEmpty
  have matrixRouteSame : hsame matrix route := by
    cases routeEmpty
    exact matrixEmpty
  have subshiftRoute : hsame subshift route := by
    have subshiftAdjacency : hsame subshift adjacency := by
      cases goldenEmpty
      exact adjacencyGolden.trans (append_empty_right adjacency)
    exact hsame_trans subshiftAdjacency adjacencyRoute
  have supportReadRoute : hsame supportRead route := by
    have supportReadAdjacency : hsame supportRead adjacency := by
      cases goldenEmpty
      exact supportRoute.trans (append_empty_right adjacency)
    exact hsame_trans supportReadAdjacency adjacencyRoute
  have entryReadRoute : hsame entryRead route := by
    have entryReadSupport : hsame entryRead supportRead := by
      cases fibonacciEmpty
      exact entryRoute.trans (append_empty_right supportRead)
    exact hsame_trans entryReadSupport supportReadRoute
  exact
    ⟨adjacencyRoute, goldenRoute, fibonacciRoute, matrixRouteSame, subshiftRoute,
      supportReadRoute, entryReadRoute, supportRoute, entryRoute, provenancePkg,
      localNamePkg, entryPkg⟩

end BEDC.Derived.TransferOperatorUp
