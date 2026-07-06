import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationBridgeRoute [AskSetup] [PackageSetup]
    {W M Q T S H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg ->
      Cont W M Q -> Cont Q T S -> Cont S H C -> Cont C P N -> PkgSig bundle N pkg ->
        SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨ hsame row S ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W M Q ∧ Cont Q T S ∧ Cont S H C ∧ Cont C P N ∧
              PkgSig bundle N pkg)
          hsame := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier auditRoute sealRoute transportRoute nameRoute bridgePkg
  obtain ⟨_wUnary, _mUnary, _qUnary, _tUnary, _sUnary, _hUnary, _cUnary, _pUnary,
    nUnary, _carrierAudit, _carrierLedger, _carrierSeal, _carrierName, _carrierPkg⟩ :=
    carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, nUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, auditRoute, sealRoute, transportRoute, nameRoute, bridgePkg⟩
  }

end BEDC.Derived.CauchyOscillationUp
