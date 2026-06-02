import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_route_budget_exhaustion [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      source mesh locked budgetPrefix sealBudget terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal dyadic source →
        Cont source windows mesh →
          Cont mesh triangle locked →
            Cont dyadic windows budgetPrefix →
              Cont budgetPrefix sealRow sealBudget →
                Cont sealBudget realSeal terminal →
                  PkgSig bundle locked pkg →
                    PkgSig bundle sealBudget pkg →
                      PkgSig bundle terminal pkg →
                        UnaryHistory source ∧ UnaryHistory mesh ∧ UnaryHistory locked ∧
                          UnaryHistory budgetPrefix ∧ UnaryHistory sealBudget ∧
                            UnaryHistory terminal ∧ Cont diagonal dyadic source ∧
                              Cont source windows mesh ∧ Cont mesh triangle locked ∧
                                Cont dyadic windows budgetPrefix ∧
                                  Cont budgetPrefix sealRow sealBudget ∧
                                    Cont sealBudget realSeal terminal ∧
                                      PkgSig bundle provenance pkg ∧ PkgSig bundle locked pkg ∧
                                        PkgSig bundle sealBudget pkg ∧
                                          PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory
  intro carrier diagonalDyadicSource sourceWindowsMesh meshTriangleLocked
    dyadicWindowsBudgetPrefix budgetPrefixSealRowSealBudget sealBudgetRealSealTerminal
    lockedPkg sealBudgetPkg terminalPkg
  obtain ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory source :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicSource
  have meshUnary : UnaryHistory mesh :=
    unary_cont_closed sourceUnary windowsUnary sourceWindowsMesh
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed meshUnary triangleUnary meshTriangleLocked
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsBudgetPrefix
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed budgetPrefixUnary sealRowUnary budgetPrefixSealRowSealBudget
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealBudgetUnary realSealUnary sealBudgetRealSealTerminal
  exact
    ⟨sourceUnary, meshUnary, lockedUnary, budgetPrefixUnary, sealBudgetUnary, terminalUnary,
      diagonalDyadicSource, sourceWindowsMesh, meshTriangleLocked, dyadicWindowsBudgetPrefix,
      budgetPrefixSealRowSealBudget, sealBudgetRealSealTerminal, provenancePkg, lockedPkg,
      sealBudgetPkg, terminalPkg⟩

theorem DiagonalLimitCompatibilityRouteBudgetExhaustion [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetRead sealRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont dyadic windows budgetRead →
        Cont budgetRead sealRow sealRead →
          Cont sealRead realSeal terminalRead →
            PkgSig bundle terminalRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row budgetRead ∨ hsame row sealRead ∨ hsame row terminalRead)
                  (fun _row : BHist =>
                    Cont dyadic windows budgetRead ∧ Cont budgetRead sealRow sealRead ∧
                      Cont sealRead realSeal terminalRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle terminalRead pkg)
                  hsame ∧
                UnaryHistory budgetRead ∧ UnaryHistory sealRead ∧
                  UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier dyadicWindowsBudget budgetSeal sealTerminal terminalPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsBudget
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed budgetUnary sealRowUnary budgetSeal
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed sealReadUnary realSealUnary sealTerminal
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row budgetRead ∨ hsame row sealRead ∨ hsame row terminalRead)
          (fun _row : BHist =>
            Cont dyadic windows budgetRead ∧ Cont budgetRead sealRow sealRead ∧
              Cont sealRead realSeal terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle terminalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetRead (Or.inl (hsame_refl budgetRead))
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
        intro row other sameRows source
        cases source with
        | inl sameBudget =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameBudget)
        | inr rest =>
            cases rest with
            | inl sameSeal =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameSeal))
            | inr sameTerminal =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameTerminal))
    }
    pattern_sound := by
      intro _row _source
      exact ⟨dyadicWindowsBudget, budgetSeal, sealTerminal⟩
    ledger_sound := by
      intro row source
      cases source with
      | inl sameBudget =>
          exact
            ⟨unary_transport budgetUnary (hsame_symm sameBudget), provenancePkg, terminalPkg⟩
      | inr rest =>
          cases rest with
          | inl sameSeal =>
              exact
                ⟨unary_transport sealReadUnary (hsame_symm sameSeal), provenancePkg,
                  terminalPkg⟩
          | inr sameTerminal =>
              exact
                ⟨unary_transport terminalUnary (hsame_symm sameTerminal), provenancePkg,
                  terminalPkg⟩
  }
  exact ⟨cert, budgetUnary, sealReadUnary, terminalUnary⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
