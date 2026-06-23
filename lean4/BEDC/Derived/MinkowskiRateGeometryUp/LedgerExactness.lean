import BEDC.Derived.MinkowskiRateGeometryUp.Carrier

namespace BEDC.Derived.MinkowskiRateGeometryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MinkowskiRateGeometryCarrier_ledger_exactness [AskSetup] [PackageSetup]
    {config causal rate frame distance transport replay provenance localName ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MinkowskiRateGeometryCarrier config causal rate frame distance transport replay provenance
        localName bundle pkg →
      Cont rate frame ledgerRead →
        PkgSig bundle ledgerRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row config ∨ hsame row causal ∨ hsame row rate ∨ hsame row frame ∨
                  hsame row distance ∨ hsame row ledgerRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont config causal rate ∧ Cont rate frame distance ∧
                  Cont rate frame ledgerRead ∧ PkgSig bundle distance pkg ∧
                    PkgSig bundle ledgerRead pkg)
              hsame ∧
            UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier rateFrameLedger ledgerPkg
  obtain ⟨_configUnary, _causalUnary, rateUnary, frameUnary, _distanceUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, configCausalRate,
    rateFrameDistance, _distanceTransportReplay, distancePkg, _provenancePkg,
    _localNamePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed rateUnary frameUnary rateFrameLedger
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row config ∨ hsame row causal ∨ hsame row rate ∨ hsame row frame ∨
              hsame row distance ∨ hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont config causal rate ∧ Cont rate frame distance ∧
              Cont rate frame ledgerRead ∧ PkgSig bundle distance pkg ∧
                PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
      exact
        ⟨sourceRow.right, configCausalRate, rateFrameDistance, rateFrameLedger,
          distancePkg, ledgerPkg⟩
  }
  exact ⟨cert, ledgerUnary⟩

end BEDC.Derived.MinkowskiRateGeometryUp
