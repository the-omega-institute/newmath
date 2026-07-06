import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DependentCodomainInversionBoundaryCarrier [AskSetup] [PackageSetup]
    (Pi A a aPrime C0 C1 S R O H K P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory Pi ∧ UnaryHistory A ∧ UnaryHistory a ∧ UnaryHistory aPrime ∧
    UnaryHistory C0 ∧ UnaryHistory C1 ∧ UnaryHistory S ∧ UnaryHistory R ∧
      UnaryHistory O ∧ UnaryHistory H ∧ UnaryHistory K ∧ UnaryHistory P ∧
        UnaryHistory N ∧ PkgSig bundle N pkg

theorem DependentCodomainInversionBoundaryCarrier_subject_reduction_handoff
    [AskSetup] [PackageSetup]
    {Pi A a aPrime C0 C1 S R O H K P N substRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DependentCodomainInversionBoundaryCarrier Pi A a aPrime C0 C1 S R O H K P N
        bundle pkg →
      Cont C0 S substRead →
        Cont substRead R handoffRead →
          PkgSig bundle handoffRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Pi ∨ hsame row A ∨ hsame row a ∨ hsame row aPrime ∨
                    hsame row C0 ∨ hsame row C1 ∨ hsame row S ∨ hsame row R ∨
                      hsame row O ∨ hsame row handoffRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont C0 S substRead ∧
                    Cont substRead R handoffRead ∧ PkgSig bundle handoffRead pkg)
                hsame ∧ UnaryHistory substRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: DependentCodomainInversionBoundaryCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier substRoute handoffRoute handoffPkg
  obtain ⟨_piUnary, _domainUnary, _argUnary, _argPrimeUnary, c0Unary, _c1Unary,
    sUnary, rUnary, _oUnary, _hUnary, _kUnary, _pUnary, _nUnary, _namePkg⟩ := carrier
  have substUnary : UnaryHistory substRead :=
    unary_cont_closed c0Unary sUnary substRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed substUnary rUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Pi ∨ hsame row A ∨ hsame row a ∨ hsame row aPrime ∨
              hsame row C0 ∨ hsame row C1 ∨ hsame row S ∨ hsame row R ∨
                hsame row O ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C0 S substRead ∧ Cont substRead R handoffRead ∧
              PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr sourceRow.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, substRoute, handoffRoute, handoffPkg⟩
  }
  exact ⟨cert, substUnary, handoffUnary⟩

end BEDC.Derived

namespace BEDC.Derived.DependentCodomainInversionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive DependentCodomainInversionBoundaryUp : Type where
  | mk
      (Pi A a a' C0 C1 S R O H P N : BHist) :
      DependentCodomainInversionBoundaryUp

def dependentCodomainInversionBoundaryFields :
    DependentCodomainInversionBoundaryUp -> List BHist
  | DependentCodomainInversionBoundaryUp.mk Pi A a a' C0 C1 S R O H P N =>
      [Pi, A, a, a', C0, C1, S, R, O, H, append S R, P, N]

theorem DependentCodomainInversionBoundaryCarrier_namecert_obligations
    (x : DependentCodomainInversionBoundaryUp) :
    exists Pi A a a' C0 C1 S R O H K P N : BHist,
      dependentCodomainInversionBoundaryFields x =
          [Pi, A, a, a', C0, C1, S, R, O, H, K, P, N] ∧
        hsame H H ∧ Cont S R K ∧
          Nonempty (NameCert (fun h : BHist => hsame h N) hsame) := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  cases x with
  | mk Pi A a a' C0 C1 S R O H P N =>
      refine
        ⟨Pi, A, a, a', C0, C1, S, R, O, H, append S R, P, N, ?_⟩
      constructor
      · rfl
      constructor
      · exact hsame_refl H
      constructor
      · rfl
      · exact
          Nonempty.intro {
            carrier_inhabited := Exists.intro N (hsame_refl N)
            equiv_refl := by
              intro row _source
              exact hsame_refl row
            equiv_symm := by
              intro row other same
              exact hsame_symm same
            equiv_trans := by
              intro row other third sameRO sameOT
              exact hsame_trans sameRO sameOT
            carrier_respects_equiv := by
              intro row other same source
              exact hsame_trans (hsame_symm same) source
          }

theorem DependentCodomainInversionBoundaryCarrier_ledger_nonescape [AskSetup] [PackageSetup]
    {Pi A a aPrime C0 C1 S R O H K P N substRead handoffRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.DependentCodomainInversionBoundaryCarrier Pi A a aPrime C0 C1 S R O H K P N
        bundle pkg ->
      Cont C0 S substRead ->
        Cont substRead R handoffRead ->
          Cont handoffRead O ledgerRead ->
            PkgSig bundle ledgerRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row R ∨ hsame row O ∨ hsame row H ∨
                      hsame row K ∨ hsame row P ∨ hsame row N ∨ hsame row ledgerRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont C0 S substRead ∧
                      Cont substRead R handoffRead ∧ Cont handoffRead O ledgerRead ∧
                        PkgSig bundle ledgerRead pkg)
                  hsame ∧ UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: DependentCodomainInversionBoundaryCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier substRoute handoffRoute ledgerRoute ledgerPkg
  obtain ⟨_piUnary, _domainUnary, _argUnary, _argPrimeUnary, c0Unary, _c1Unary,
    sUnary, rUnary, oUnary, _hUnary, _kUnary, _pUnary, _nUnary, _namePkg⟩ := carrier
  have substUnary : UnaryHistory substRead :=
    unary_cont_closed c0Unary sUnary substRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed substUnary rUnary handoffRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed handoffUnary oUnary ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row O ∨ hsame row H ∨
              hsame row K ∨ hsame row P ∨ hsame row N ∨ hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C0 S substRead ∧
              Cont substRead R handoffRead ∧ Cont handoffRead O ledgerRead ∧
                PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, substRoute, handoffRoute, ledgerRoute, ledgerPkg⟩
  }
  exact ⟨cert, ledgerUnary⟩

theorem DependentCodomainInversionBoundaryCarrier_codomain_readback_nonescape
    [AskSetup] [PackageSetup]
    {Pi A a aPrime C0 C1 S R O H K P N substRead obstructionRead frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.DependentCodomainInversionBoundaryCarrier Pi A a aPrime C0 C1 S R O H K P N
        bundle pkg →
      Cont C0 S substRead →
        Cont substRead R obstructionRead →
          Cont obstructionRead O frontierRead →
            PkgSig bundle frontierRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row C0 ∨ hsame row C1 ∨ hsame row S ∨ hsame row R ∨
                      hsame row O ∨ hsame row frontierRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont C0 S substRead ∧
                      Cont substRead R obstructionRead ∧ Cont obstructionRead O frontierRead ∧
                        PkgSig bundle frontierRead pkg)
                  hsame ∧ UnaryHistory substRead ∧ UnaryHistory obstructionRead ∧
                    UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: DependentCodomainInversionBoundaryCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier substRoute obstructionRoute frontierRoute frontierPkg
  obtain ⟨_piUnary, _domainUnary, _argUnary, _argPrimeUnary, c0Unary, _c1Unary,
    sUnary, rUnary, oUnary, _hUnary, _kUnary, _pUnary, _nUnary, _namePkg⟩ := carrier
  have substUnary : UnaryHistory substRead :=
    unary_cont_closed c0Unary sUnary substRoute
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed substUnary rUnary obstructionRoute
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed obstructionUnary oUnary frontierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C0 ∨ hsame row C1 ∨ hsame row S ∨ hsame row R ∨
              hsame row O ∨ hsame row frontierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C0 S substRead ∧ Cont substRead R obstructionRead ∧
              Cont obstructionRead O frontierRead ∧ PkgSig bundle frontierRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro frontierRead ⟨hsame_refl frontierRead, frontierUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, substRoute, obstructionRoute, frontierRoute, frontierPkg⟩
  }
  exact ⟨cert, substUnary, obstructionUnary, frontierUnary⟩

theorem DependentCodomainInversionBoundaryCarrier_readback_stability_request
    [AskSetup] [PackageSetup]
    {Pi A a aPrime C0 C1 S R O H K P N substRead handoffRead ledgerRead requestRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.DependentCodomainInversionBoundaryCarrier Pi A a aPrime C0 C1 S R O H K P N
        bundle pkg →
      Cont C0 S substRead →
        Cont substRead R handoffRead →
          Cont handoffRead O ledgerRead →
            Cont ledgerRead H requestRead →
              PkgSig bundle requestRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row requestRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row C0 ∨ hsame row C1 ∨ hsame row S ∨ hsame row R ∨
                        hsame row O ∨ hsame row H ∨ hsame row K ∨ hsame row P ∨
                          hsame row N ∨ hsame row requestRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont C0 S substRead ∧
                        Cont substRead R handoffRead ∧ Cont handoffRead O ledgerRead ∧
                          Cont ledgerRead H requestRead ∧ PkgSig bundle requestRead pkg)
                    hsame ∧ UnaryHistory substRead ∧ UnaryHistory handoffRead ∧
                      UnaryHistory ledgerRead ∧ UnaryHistory requestRead := by
  -- BEDC touchpoint anchor: DependentCodomainInversionBoundaryCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier substRoute handoffRoute ledgerRoute requestRoute requestPkg
  obtain ⟨_piUnary, _domainUnary, _argUnary, _argPrimeUnary, c0Unary, _c1Unary,
    sUnary, rUnary, oUnary, hUnary, _kUnary, _pUnary, _nUnary, _namePkg⟩ := carrier
  have substUnary : UnaryHistory substRead :=
    unary_cont_closed c0Unary sUnary substRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed substUnary rUnary handoffRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed handoffUnary oUnary ledgerRoute
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed ledgerUnary hUnary requestRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row requestRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C0 ∨ hsame row C1 ∨ hsame row S ∨ hsame row R ∨
              hsame row O ∨ hsame row H ∨ hsame row K ∨ hsame row P ∨
                hsame row N ∨ hsame row requestRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C0 S substRead ∧
              Cont substRead R handoffRead ∧ Cont handoffRead O ledgerRead ∧
                Cont ledgerRead H requestRead ∧ PkgSig bundle requestRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro requestRead ⟨hsame_refl requestRead, requestUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr sourceRow.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, substRoute, handoffRoute, ledgerRoute, requestRoute,
          requestPkg⟩
  }
  exact ⟨cert, substUnary, handoffUnary, ledgerUnary, requestUnary⟩

theorem DependentCodomainInversionBoundaryCarrier_frontier_coverage [AskSetup] [PackageSetup]
    {Pi A a aPrime C0 C1 S R O H K P N substRead handoffRead ledgerRead requestRead
      replayRead provenanceRead frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.DependentCodomainInversionBoundaryCarrier Pi A a aPrime C0 C1 S R O H K P N
        bundle pkg ->
      Cont C0 S substRead ->
        Cont substRead R handoffRead ->
          Cont handoffRead O ledgerRead ->
            Cont ledgerRead H requestRead ->
              Cont requestRead K replayRead ->
                Cont replayRead P provenanceRead ->
                  Cont provenanceRead N frontierRead ->
                    PkgSig bundle frontierRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row A ∨ hsame row a ∨ hsame row aPrime ∨
                              hsame row C0 ∨ hsame row C1 ∨ hsame row S ∨
                                hsame row R ∨ hsame row O ∨ hsame row H ∨
                                  hsame row K ∨ hsame row P ∨ hsame row N ∨
                                    hsame row frontierRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont C0 S substRead ∧
                              Cont substRead R handoffRead ∧
                                Cont handoffRead O ledgerRead ∧
                                  Cont ledgerRead H requestRead ∧
                                    Cont requestRead K replayRead ∧
                                      Cont replayRead P provenanceRead ∧
                                        Cont provenanceRead N frontierRead ∧
                                          PkgSig bundle frontierRead pkg)
                          hsame ∧ UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: DependentCodomainInversionBoundaryCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier substRoute handoffRoute ledgerRoute requestRoute replayRoute provenanceRoute
    frontierRoute frontierPkg
  obtain ⟨_piUnary, _domainUnary, _argUnary, _argPrimeUnary, c0Unary, _c1Unary,
    sUnary, rUnary, oUnary, hUnary, kUnary, pUnary, nUnary, _namePkg⟩ := carrier
  have substUnary : UnaryHistory substRead :=
    unary_cont_closed c0Unary sUnary substRoute
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
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed provenanceUnary nUnary frontierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row a ∨ hsame row aPrime ∨ hsame row C0 ∨
              hsame row C1 ∨ hsame row S ∨ hsame row R ∨ hsame row O ∨
                hsame row H ∨ hsame row K ∨ hsame row P ∨ hsame row N ∨
                  hsame row frontierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C0 S substRead ∧
              Cont substRead R handoffRead ∧ Cont handoffRead O ledgerRead ∧
                Cont ledgerRead H requestRead ∧ Cont requestRead K replayRead ∧
                  Cont replayRead P provenanceRead ∧ Cont provenanceRead N frontierRead ∧
                    PkgSig bundle frontierRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro frontierRead ⟨hsame_refl frontierRead, frontierUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, substRoute, handoffRoute, ledgerRoute, requestRoute,
          replayRoute, provenanceRoute, frontierRoute, frontierPkg⟩
  }
  exact ⟨cert, frontierUnary⟩

theorem DependentCodomainInversionBoundaryCarrier_public_obligation
    [AskSetup] [PackageSetup]
    {Pi A a aPrime C0 C1 S R O H K P N substRead handoffRead ledgerRead requestRead
      replayRead provenanceRead frontierRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.DependentCodomainInversionBoundaryCarrier Pi A a aPrime C0 C1 S R O H K P N
        bundle pkg →
      Cont C0 S substRead →
        Cont substRead R handoffRead →
          Cont handoffRead O ledgerRead →
            Cont ledgerRead H requestRead →
              Cont requestRead K replayRead →
                Cont replayRead P provenanceRead →
                  Cont provenanceRead N frontierRead →
                    Cont frontierRead Pi publicRead →
                      PkgSig bundle publicRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row Pi ∨ hsame row A ∨ hsame row C0 ∨
                                hsame row C1 ∨ hsame row S ∨ hsame row R ∨
                                  hsame row O ∨ hsame row publicRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont C0 S substRead ∧
                                Cont substRead R handoffRead ∧
                                  Cont handoffRead O ledgerRead ∧
                                    Cont ledgerRead H requestRead ∧
                                      Cont requestRead K replayRead ∧
                                        Cont replayRead P provenanceRead ∧
                                          Cont provenanceRead N frontierRead ∧
                                            Cont frontierRead Pi publicRead ∧
                                              PkgSig bundle publicRead pkg)
                            hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: DependentCodomainInversionBoundaryCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier substRoute handoffRoute ledgerRoute requestRoute replayRoute provenanceRoute
    frontierRoute publicRoute publicPkg
  obtain ⟨piUnary, _domainUnary, _argUnary, _argPrimeUnary, c0Unary, _c1Unary,
    sUnary, rUnary, oUnary, hUnary, kUnary, pUnary, nUnary, _namePkg⟩ := carrier
  have substUnary : UnaryHistory substRead :=
    unary_cont_closed c0Unary sUnary substRoute
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
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed provenanceUnary nUnary frontierRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed frontierUnary piUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Pi ∨ hsame row A ∨ hsame row C0 ∨ hsame row C1 ∨
              hsame row S ∨ hsame row R ∨ hsame row O ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C0 S substRead ∧ Cont substRead R handoffRead ∧
              Cont handoffRead O ledgerRead ∧ Cont ledgerRead H requestRead ∧
                Cont requestRead K replayRead ∧ Cont replayRead P provenanceRead ∧
                  Cont provenanceRead N frontierRead ∧ Cont frontierRead Pi publicRead ∧
                    PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact
        ⟨sourceRow.right, substRoute, handoffRoute, ledgerRoute, requestRoute,
          replayRoute, provenanceRoute, frontierRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

theorem DependentCodomainInversionBoundaryCarrier_obligation_closure_package
    [AskSetup] [PackageSetup]
    {Pi A a aPrime C0 C1 S R O H K P N substRead handoffRead ledgerRead requestRead
      replayRead provenanceRead frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.DependentCodomainInversionBoundaryCarrier Pi A a aPrime C0 C1 S R O H K P N
        bundle pkg ->
      Cont C0 S substRead ->
        Cont substRead R handoffRead ->
          Cont handoffRead O ledgerRead ->
            Cont ledgerRead H requestRead ->
              Cont requestRead K replayRead ->
                Cont replayRead P provenanceRead ->
                  Cont provenanceRead N frontierRead ->
                    PkgSig bundle requestRead pkg ->
                      PkgSig bundle frontierRead pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row Pi ∨ hsame row A ∨ hsame row a ∨
                                hsame row aPrime ∨ hsame row C0 ∨ hsame row C1 ∨
                                  hsame row S ∨ hsame row R ∨ hsame row O ∨
                                    hsame row H ∨ hsame row K ∨ hsame row P ∨
                                      hsame row N ∨ hsame row frontierRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont C0 S substRead ∧
                                Cont substRead R handoffRead ∧
                                  Cont handoffRead O ledgerRead ∧
                                    Cont ledgerRead H requestRead ∧
                                      Cont requestRead K replayRead ∧
                                        Cont replayRead P provenanceRead ∧
                                          Cont provenanceRead N frontierRead ∧
                                            PkgSig bundle frontierRead pkg)
                            hsame ∧ UnaryHistory substRead ∧ UnaryHistory handoffRead ∧
                          UnaryHistory ledgerRead ∧ UnaryHistory requestRead ∧
                            UnaryHistory replayRead ∧ UnaryHistory provenanceRead ∧
                              UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: DependentCodomainInversionBoundaryCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier substRoute handoffRoute ledgerRoute requestRoute replayRoute provenanceRoute
    frontierRoute _requestPkg frontierPkg
  obtain ⟨_piUnary, _domainUnary, _argUnary, _argPrimeUnary, c0Unary, _c1Unary,
    sUnary, rUnary, oUnary, hUnary, kUnary, pUnary, nUnary, _namePkg⟩ := carrier
  have substUnary : UnaryHistory substRead :=
    unary_cont_closed c0Unary sUnary substRoute
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
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed provenanceUnary nUnary frontierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Pi ∨ hsame row A ∨ hsame row a ∨ hsame row aPrime ∨
              hsame row C0 ∨ hsame row C1 ∨ hsame row S ∨ hsame row R ∨
                hsame row O ∨ hsame row H ∨ hsame row K ∨ hsame row P ∨
                  hsame row N ∨ hsame row frontierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C0 S substRead ∧ Cont substRead R handoffRead ∧
              Cont handoffRead O ledgerRead ∧ Cont ledgerRead H requestRead ∧
                Cont requestRead K replayRead ∧ Cont replayRead P provenanceRead ∧
                  Cont provenanceRead N frontierRead ∧ PkgSig bundle frontierRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro frontierRead ⟨hsame_refl frontierRead, frontierUnary⟩
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
      exact
        ⟨sourceRow.right, substRoute, handoffRoute, ledgerRoute, requestRoute,
          replayRoute, provenanceRoute, frontierRoute, frontierPkg⟩
  }
  exact
    ⟨cert, substUnary, handoffUnary, ledgerUnary, requestUnary, replayUnary,
      provenanceUnary, frontierUnary⟩

end BEDC.Derived.DependentCodomainInversionBoundaryUp
