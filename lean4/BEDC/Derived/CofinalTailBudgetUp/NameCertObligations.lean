import BEDC.Derived.CofinalTailBudgetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CofinalTailBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CofinalTailBudgetCarrier [AskSetup] [PackageSetup]
    (budget windows readback sealRow transports routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory budget ∧
    UnaryHistory windows ∧
      UnaryHistory readback ∧
        UnaryHistory sealRow ∧
          UnaryHistory transports ∧
            UnaryHistory routes ∧
              UnaryHistory provenance ∧
                UnaryHistory name ∧
                  Cont budget windows readback ∧
                    Cont readback sealRow routes ∧
                      PkgSig bundle provenance pkg ∧
                        PkgSig bundle name pkg

theorem CofinalTailBudgetCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {budget windows readback sealRow transports routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalTailBudgetCarrier budget windows readback sealRow transports routes provenance name
        bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CofinalTailBudgetCarrier budget windows readback sealRow transports routes
              provenance name bundle pkg ∧
            (hsame row budget ∨ hsame row windows ∨ hsame row readback ∨
              hsame row sealRow ∨ hsame row transports ∨ hsame row routes ∨
              hsame row provenance ∨ hsame row name))
        (fun _row : BHist =>
          Cont budget windows readback ∧ Cont readback sealRow routes ∧
            PkgSig bundle provenance pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle name pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory SemanticNameCert
  intro carrier
  have carrierPacket := carrier
  obtain ⟨budgetUnary, windowsUnary, readbackUnary, sealRowUnary, transportsUnary,
    routesUnary, provenanceUnary, nameUnary, budgetWindowsReadback, readbackSealRoutes,
    provenancePkg, namePkg⟩ := carrier
  let SourceSpec :=
    fun row : BHist =>
      CofinalTailBudgetCarrier budget windows readback sealRow transports routes provenance
          name bundle pkg ∧
        (hsame row budget ∨ hsame row windows ∨ hsame row readback ∨
          hsame row sealRow ∨ hsame row transports ∨ hsame row routes ∨
          hsame row provenance ∨ hsame row name)
  have sourceWitness : SourceSpec budget := by
    exact ⟨carrierPacket, Or.inl (hsame_refl budget)⟩
  have rowUnary :
      ∀ {row : BHist},
        (hsame row budget ∨ hsame row windows ∨ hsame row readback ∨
          hsame row sealRow ∨ hsame row transports ∨ hsame row routes ∨
          hsame row provenance ∨ hsame row name) →
          UnaryHistory row := by
    intro row rowMember
    cases rowMember with
    | inl sameBudget =>
        exact unary_transport budgetUnary (hsame_symm sameBudget)
    | inr rest =>
        cases rest with
        | inl sameWindows =>
            exact unary_transport windowsUnary (hsame_symm sameWindows)
        | inr rest =>
            cases rest with
            | inl sameReadback =>
                exact unary_transport readbackUnary (hsame_symm sameReadback)
            | inr rest =>
                cases rest with
                | inl sameSeal =>
                    exact unary_transport sealRowUnary (hsame_symm sameSeal)
                | inr rest =>
                    cases rest with
                    | inl sameTransports =>
                        exact unary_transport transportsUnary (hsame_symm sameTransports)
                    | inr rest =>
                        cases rest with
                        | inl sameRoutes =>
                            exact unary_transport routesUnary (hsame_symm sameRoutes)
                        | inr rest =>
                            cases rest with
                            | inl sameProvenance =>
                                exact unary_transport provenanceUnary (hsame_symm sameProvenance)
                            | inr sameName =>
                                exact unary_transport nameUnary (hsame_symm sameName)
  exact {
    core := {
      carrier_inhabited := Exists.intro budget sourceWitness
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
        cases sourceRow with
        | intro carrierRow rowMember =>
            cases rowMember with
            | inl sameBudget =>
                exact ⟨carrierRow, Or.inl (hsame_trans (hsame_symm sameRows) sameBudget)⟩
            | inr rest =>
                cases rest with
                | inl sameWindows =>
                    exact
                      ⟨carrierRow, Or.inr (Or.inl
                        (hsame_trans (hsame_symm sameRows) sameWindows))⟩
                | inr rest =>
                    cases rest with
                    | inl sameReadback =>
                        exact
                          ⟨carrierRow, Or.inr (Or.inr (Or.inl
                            (hsame_trans (hsame_symm sameRows) sameReadback)))⟩
                    | inr rest =>
                        cases rest with
                        | inl sameSeal =>
                            exact
                              ⟨carrierRow, Or.inr (Or.inr (Or.inr (Or.inl
                                (hsame_trans (hsame_symm sameRows) sameSeal))))⟩
                        | inr rest =>
                            cases rest with
                            | inl sameTransports =>
                                exact
                                  ⟨carrierRow, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                                    (hsame_trans (hsame_symm sameRows) sameTransports)))))⟩
                            | inr rest =>
                                cases rest with
                                | inl sameRoutes =>
                                    exact
                                      ⟨carrierRow, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                        (Or.inl
                                          (hsame_trans (hsame_symm sameRows)
                                            sameRoutes))))))⟩
                                | inr rest =>
                                    cases rest with
                                    | inl sameProvenance =>
                                        exact
                                          ⟨carrierRow, Or.inr (Or.inr (Or.inr (Or.inr
                                            (Or.inr (Or.inr (Or.inl
                                              (hsame_trans (hsame_symm sameRows)
                                                sameProvenance)))))))⟩
                                    | inr sameName =>
                                        exact
                                          ⟨carrierRow, Or.inr (Or.inr (Or.inr (Or.inr
                                            (Or.inr (Or.inr (Or.inr
                                              (hsame_trans (hsame_symm sameRows)
                                                sameName)))))))⟩
    }
    pattern_sound := by
      intro _row _source
      exact ⟨budgetWindowsReadback, readbackSealRoutes, provenancePkg⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨rowUnary sourceRow.right, namePkg⟩
  }

theorem CofinalTailBudgetCarrier_window_read_transport [AskSetup] [PackageSetup]
    {budget windows readback sealRow transports routes provenance name row : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalTailBudgetCarrier budget windows readback sealRow transports routes provenance name
        bundle pkg →
      hsame row windows →
        UnaryHistory row ∧ UnaryHistory budget ∧ Cont budget windows readback ∧
          Cont readback sealRow routes ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame
  intro carrier sameRowWindows
  obtain ⟨budgetUnary, windowsUnary, _readbackUnary, _sealRowUnary, _transportsUnary,
    _routesUnary, _provenanceUnary, _nameUnary, budgetWindowsReadback,
    readbackSealRoutes, provenancePkg, _namePkg⟩ := carrier
  have rowUnary : UnaryHistory row :=
    unary_transport windowsUnary (hsame_symm sameRowWindows)
  exact ⟨rowUnary, budgetUnary, budgetWindowsReadback, readbackSealRoutes, provenancePkg⟩

end BEDC.Derived.CofinalTailBudgetUp
