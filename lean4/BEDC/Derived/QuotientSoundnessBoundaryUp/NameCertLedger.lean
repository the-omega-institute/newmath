import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_namecert_ledger [AskSetup] [PackageSetup]
    {e a t v h c p n refusal replacement ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg →
      Cont e a v →
        Cont v h refusal →
          Cont h c replacement →
            Cont p n ledger →
              PkgSig bundle refusal pkg →
                PkgSig bundle replacement pkg →
                  PkgSig bundle ledger pkg →
                    SemanticNameCert
                        (fun row : BHist =>
                          QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                            hsame row ledger)
                        (fun row : BHist =>
                          Cont e a v ∧ Cont v h refusal ∧ Cont h c replacement ∧
                            Cont p n row)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle p pkg ∧ PkgSig bundle n pkg ∧
                            PkgSig bundle ledger pkg)
                        hsame ∧
                      UnaryHistory refusal ∧ UnaryHistory replacement ∧
                        UnaryHistory ledger := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert
  intro carrier eAV vHRefusal hCReplacement pNLedger _refusalPkg _replacementPkg ledgerPkg
  have carrierWitness := carrier
  obtain ⟨_eUnary, _aUnary, _tUnary, vUnary, hUnary, cUnary, pUnary, nUnary,
    _carrierEAV, _eTH, _hCN, pPkg, nPkg, _hN⟩ := carrier
  have refusalUnary : UnaryHistory refusal :=
    unary_cont_closed vUnary hUnary vHRefusal
  have replacementUnary : UnaryHistory replacement :=
    unary_cont_closed hUnary cUnary hCReplacement
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed pUnary nUnary pNLedger
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
              hsame row ledger)
          (fun row : BHist =>
            Cont e a v ∧ Cont v h refusal ∧ Cont h c replacement ∧ Cont p n row)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle p pkg ∧ PkgSig bundle n pkg ∧
              PkgSig bundle ledger pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro ledger ⟨carrierWitness, hsame_refl ledger⟩
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
          exact ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
      }
      pattern_sound := by
        intro row sourceRow
        exact
          ⟨eAV, vHRefusal, hCReplacement,
            cont_result_hsame_transport pNLedger (hsame_symm sourceRow.right)⟩
      ledger_sound := by
        intro row sourceRow
        exact
          ⟨unary_transport_symm ledgerUnary sourceRow.right, pPkg, nPkg, ledgerPkg⟩
    }
  exact ⟨cert, refusalUnary, replacementUnary, ledgerUnary⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
