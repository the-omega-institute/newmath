import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_ledger_consumer_exactness
    [AskSetup] [PackageSetup] {a b c d e f g h p n refusal audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      (hsame refusal a ∨ hsame refusal b ∨ hsame refusal c ∨ hsame refusal d ∨
          hsame refusal e ∨ hsame refusal f ∨ hsame refusal g) ->
        Cont h p audit ->
          PkgSig bundle audit pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row audit ∧ UnaryHistory row)
              (fun row : BHist => UnaryHistory refusal ∧ hsame row audit)
              (fun _row : BHist => hsame p n ∧ PkgSig bundle p pkg ∧ PkgSig bundle audit pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro packet refusalRow auditRoute auditPkg
  have refusalLedger :=
    AxisZeckendorfCannotClaimRegistryPacket_refusal_ledger_row packet refusalRow
  have publicBoundary :=
    AxisZeckendorfCannotClaimRegistryPacket_public_boundary packet auditRoute auditPkg
  obtain ⟨refusalUnary, _routeAB, _routeCD, _routeEF, sameProvenanceName, provenancePkg⟩ :=
    refusalLedger
  obtain
    ⟨_aUnary, _bUnary, _cUnary, _dUnary, _eUnary, _fUnary, _gUnary, _hUnary,
      _pUnary, auditUnary, _auditRoute, _sameProvenanceName, _provenancePkg,
      auditPkgWitness⟩ := publicBoundary
  exact {
    core := {
      carrier_inhabited := Exists.intro audit
        (And.intro (hsame_refl audit) auditUnary)
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
          And.intro (hsame_trans (hsame_symm sameRows) sourceRow.left)
            (unary_transport sourceRow.right sameRows)
    }
    pattern_sound := by
      intro _row sourceRow
      exact And.intro refusalUnary sourceRow.left
    ledger_sound := by
      intro _row _sourceRow
      exact And.intro sameProvenanceName (And.intro provenancePkg auditPkgWitness)
  }

end BEDC.Derived.AxisZeckendorfCannotClaimUp
