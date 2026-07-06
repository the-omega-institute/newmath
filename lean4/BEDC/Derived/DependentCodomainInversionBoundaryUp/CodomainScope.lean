import BEDC.Derived.DependentCodomainInversionBoundaryUp

namespace BEDC.Derived.DependentCodomainInversionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DependentCodomainInversionBoundaryCarrier_codomain_scope [AskSetup] [PackageSetup]
    {Pi A a aPrime C0 C1 S R O H K P N pairRead substRead handoffRead ledgerRead
      requestRead replayRead provenanceRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.DependentCodomainInversionBoundaryCarrier Pi A a aPrime C0 C1 S R O H K P N
        bundle pkg →
      Cont C0 C1 pairRead →
        Cont pairRead S substRead →
          Cont substRead R handoffRead →
            Cont handoffRead O ledgerRead →
              Cont ledgerRead H requestRead →
                Cont requestRead K replayRead →
                  Cont replayRead P provenanceRead →
                    Cont provenanceRead N scopedRead →
                      PkgSig bundle scopedRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row Pi ∨ hsame row A ∨ hsame row a ∨
                                hsame row aPrime ∨ hsame row C0 ∨ hsame row C1 ∨
                                  hsame row S ∨ hsame row R ∨ hsame row O ∨
                                    hsame row H ∨ hsame row K ∨ hsame row P ∨
                                      hsame row N ∨ hsame row pairRead ∨
                                        hsame row scopedRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont C0 C1 pairRead ∧
                                Cont pairRead S substRead ∧
                                  Cont provenanceRead N scopedRead ∧
                                    PkgSig bundle scopedRead pkg)
                            hsame ∧ UnaryHistory pairRead ∧ UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: DependentCodomainInversionBoundaryCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier pairRoute substRoute handoffRoute ledgerRoute requestRoute replayRoute
    provenanceRoute scopedRoute scopedPkg
  obtain ⟨_piUnary, _domainUnary, _argUnary, _argPrimeUnary, c0Unary, c1Unary,
    sUnary, rUnary, oUnary, hUnary, kUnary, pUnary, nUnary, _namePkg⟩ := carrier
  have pairUnary : UnaryHistory pairRead :=
    unary_cont_closed c0Unary c1Unary pairRoute
  have substUnary : UnaryHistory substRead :=
    unary_cont_closed pairUnary sUnary substRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed substUnary rUnary handoffRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed handoffUnary oUnary ledgerRoute
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed ledgerUnary hUnary requestRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed requestUnary kUnary replayRoute
  have provenanceUnary : UnaryHistory provenanceRead :=
    unary_cont_closed replayUnary pUnary provenanceRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed provenanceUnary nUnary scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Pi ∨ hsame row A ∨ hsame row a ∨ hsame row aPrime ∨
              hsame row C0 ∨ hsame row C1 ∨ hsame row S ∨ hsame row R ∨
                hsame row O ∨ hsame row H ∨ hsame row K ∨ hsame row P ∨
                  hsame row N ∨ hsame row pairRead ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C0 C1 pairRead ∧ Cont pairRead S substRead ∧
              Cont provenanceRead N scopedRead ∧ PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      repeat (first | exact sourceRow.left | apply Or.inr)
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, pairRoute, substRoute, scopedRoute, scopedPkg⟩
  }
  exact ⟨cert, pairUnary, scopedUnary⟩

end BEDC.Derived.DependentCodomainInversionBoundaryUp
