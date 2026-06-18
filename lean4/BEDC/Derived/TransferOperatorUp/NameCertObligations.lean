import BEDC.Derived.TransferOperatorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.TransferOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

def TransferOperatorCarrier [AskSetup] [PackageSetup]
    (adjacency golden subshift fibonacci matrix classifier route provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  hsame classifier classifier ∧ hsame matrix BHist.Empty ∧ hsame golden BHist.Empty ∧
    hsame fibonacci BHist.Empty ∧ hsame route BHist.Empty ∧ Cont matrix route adjacency ∧
      Cont adjacency golden subshift ∧ Cont subshift fibonacci matrix ∧
        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem TransferOperatorCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {adjacency golden subshift fibonacci matrix classifier route provenance localName entryRead
      supportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TransferOperatorCarrier adjacency golden subshift fibonacci matrix classifier route provenance
        localName bundle pkg ->
      Cont adjacency golden supportRead ->
        Cont supportRead fibonacci entryRead ->
          PkgSig bundle entryRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row adjacency ∨ hsame row golden ∨ hsame row subshift ∨
                    hsame row fibonacci ∨ hsame row matrix ∨ hsame row entryRead)
                (fun row : BHist =>
                  hsame row classifier ∨ hsame row route ∨ hsame row provenance ∨
                    hsame row localName)
                (fun _row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                    PkgSig bundle entryRead pkg)
                hsame ∧ Cont adjacency golden supportRead ∧
              Cont supportRead fibonacci entryRead ∧ PkgSig bundle entryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
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
  have sourceAdjacency :
      (fun row : BHist =>
        hsame row adjacency ∨ hsame row golden ∨ hsame row subshift ∨
          hsame row fibonacci ∨ hsame row matrix ∨ hsame row entryRead)
        adjacency := by
    exact Or.inl (hsame_refl adjacency)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row adjacency ∨ hsame row golden ∨ hsame row subshift ∨
              hsame row fibonacci ∨ hsame row matrix ∨ hsame row entryRead)
          (fun row : BHist =>
            hsame row classifier ∨ hsame row route ∨ hsame row provenance ∨
              hsame row localName)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
              PkgSig bundle entryRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro adjacency sourceAdjacency
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
          intro _row _other sameRows sourceRow
          cases sameRows
          exact sourceRow
      }
      pattern_sound := by
        intro row sourceRow
        cases sourceRow with
        | inl rowAdjacency =>
            exact Or.inr (Or.inl (hsame_trans rowAdjacency adjacencyRoute))
        | inr rest₁ =>
            cases rest₁ with
            | inl rowGolden =>
                exact Or.inr (Or.inl (hsame_trans rowGolden goldenRoute))
            | inr rest₂ =>
                cases rest₂ with
                | inl rowSubshift =>
                    exact Or.inr (Or.inl (hsame_trans rowSubshift subshiftRoute))
                | inr rest₃ =>
                    cases rest₃ with
                    | inl rowFibonacci =>
                        exact Or.inr (Or.inl (hsame_trans rowFibonacci fibonacciRoute))
                    | inr rest₄ =>
                        cases rest₄ with
                        | inl rowMatrix =>
                            exact Or.inr (Or.inl (hsame_trans rowMatrix matrixRouteSame))
                        | inr rowEntry =>
                            exact Or.inr (Or.inl (hsame_trans rowEntry entryReadRoute))
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨provenancePkg, localNamePkg, entryPkg⟩
    }
  exact ⟨cert, supportRoute, entryRoute, entryPkg⟩

theorem TransferOperator_golden_mean_matrix_boundary [AskSetup] [PackageSetup]
    {adjacency golden subshift fibonacci matrix classifier route provenance localName supportRead
      entryRead rejectedOneOne : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TransferOperatorCarrier adjacency golden subshift fibonacci matrix classifier route provenance
        localName bundle pkg ->
      Cont adjacency golden supportRead ->
        Cont supportRead fibonacci entryRead ->
          hsame rejectedOneOne (BHist.e1 (BHist.e1 BHist.Empty)) ->
            PkgSig bundle entryRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row adjacency ∨ hsame row golden ∨ hsame row subshift ∨
                      hsame row fibonacci ∨ hsame row matrix ∨ hsame row entryRead)
                  (fun row : BHist =>
                    hsame row classifier ∨ hsame row route ∨ hsame row provenance ∨
                      hsame row localName)
                  (fun _row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                      PkgSig bundle entryRead pkg)
                  hsame ∧
                hsame golden BHist.Empty ∧ hsame matrix BHist.Empty ∧
                  Cont adjacency golden supportRead ∧ Cont supportRead fibonacci entryRead ∧
                    (hsame rejectedOneOne BHist.Empty -> False) ∧
                      PkgSig bundle entryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier supportRoute entryRoute rejectedBoundary entryPkg
  obtain ⟨cert, _supportRoute, _entryRoute, _entryPkg⟩ :=
    TransferOperatorCarrier_namecert_obligations carrier supportRoute entryRoute entryPkg
  obtain ⟨_classifierSelf, matrixEmpty, goldenEmpty, _fibonacciEmpty, _routeEmpty,
    _matrixRoute, _adjacencyGolden, _subshiftFibonacci, _provenancePkg, _localNamePkg⟩ :=
    carrier
  have rejectedOneOneNotEmpty : hsame rejectedOneOne BHist.Empty -> False := by
    intro rejectedEmpty
    have oneOneEmpty : hsame (BHist.e1 (BHist.e1 BHist.Empty)) BHist.Empty :=
      hsame_trans (hsame_symm rejectedBoundary) rejectedEmpty
    cases oneOneEmpty
  exact
    ⟨cert, goldenEmpty, matrixEmpty, supportRoute, entryRoute, rejectedOneOneNotEmpty, entryPkg⟩

end BEDC.Derived.TransferOperatorUp
