import BEDC.Derived.TransferOperatorUp.NameCertObligations

namespace BEDC.Derived.TransferOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem TransferOperator_finite_window_ledger [AskSetup] [PackageSetup]
    {adjacency golden subshift fibonacci matrix classifier route provenance localName supportRead
      entryRead calculationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TransferOperatorCarrier adjacency golden subshift fibonacci matrix classifier route provenance
        localName bundle pkg →
      Cont adjacency golden supportRead →
        Cont supportRead fibonacci entryRead →
          Cont entryRead route calculationRead →
            PkgSig bundle calculationRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row calculationRead ∨ hsame row entryRead ∨ hsame row supportRead)
                  (fun row : BHist =>
                    hsame row adjacency ∨ hsame row golden ∨ hsame row subshift ∨
                      hsame row fibonacci ∨ hsame row matrix ∨ hsame row route ∨
                        hsame row calculationRead)
                  (fun _row : BHist =>
                    Cont adjacency golden supportRead ∧ Cont supportRead fibonacci entryRead ∧
                      Cont entryRead route calculationRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle localName pkg ∧ PkgSig bundle calculationRead pkg)
                  hsame ∧
                Cont adjacency golden supportRead ∧ Cont supportRead fibonacci entryRead ∧
                  Cont entryRead route calculationRead ∧ PkgSig bundle calculationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier supportRoute entryRoute calculationRoute calculationPkg
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
  have calculationReadEntry : hsame calculationRead entryRead := by
    cases routeEmpty
    exact calculationRoute.trans (append_empty_right entryRead)
  have calculationReadRoute : hsame calculationRead route :=
    hsame_trans calculationReadEntry entryReadRoute
  have sourceCalculation :
      (fun row : BHist =>
        hsame row calculationRead ∨ hsame row entryRead ∨ hsame row supportRead)
        calculationRead := by
    exact Or.inl (hsame_refl calculationRead)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row calculationRead ∨ hsame row entryRead ∨ hsame row supportRead)
          (fun row : BHist =>
            hsame row adjacency ∨ hsame row golden ∨ hsame row subshift ∨
              hsame row fibonacci ∨ hsame row matrix ∨ hsame row route ∨
                hsame row calculationRead)
          (fun _row : BHist =>
            Cont adjacency golden supportRead ∧ Cont supportRead fibonacci entryRead ∧
              Cont entryRead route calculationRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localName pkg ∧ PkgSig bundle calculationRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro calculationRead sourceCalculation
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
        | inl sameCalculation =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameCalculation)
        | inr rest =>
            cases rest with
            | inl sameEntry =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameEntry))
            | inr sameSupport =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameSupport))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameCalculation =>
          exact Or.inr
            (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inr sameCalculation)))))
      | inr rest =>
          cases rest with
          | inl sameEntry =>
              exact Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inl (hsame_trans sameEntry entryReadRoute))))))
          | inr sameSupport =>
              exact Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inl (hsame_trans sameSupport supportReadRoute))))))
    ledger_sound := by
      intro _row _source
      exact
        ⟨supportRoute, entryRoute, calculationRoute, provenancePkg, localNamePkg,
          calculationPkg⟩
  }
  exact ⟨cert, supportRoute, entryRoute, calculationRoute, calculationPkg⟩

end BEDC.Derived.TransferOperatorUp
