import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_root_unblock_package [AskSetup]
    [PackageSetup] {a b c d e f g h p n rootRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      Cont h p rootRead ->
        Cont rootRead n auditRead ->
          PkgSig bundle rootRead pkg ->
            PkgSig bundle auditRead pkg ->
              SemanticNameCert
                    (fun row : BHist =>
                      hsame row rootRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                    (fun row : BHist => Cont h p row ∧ hsame row rootRead)
                    (fun row : BHist =>
                      Cont row n auditRead ∧ PkgSig bundle auditRead pkg ∧ hsame p n)
                    hsame ∧
                UnaryHistory rootRead ∧ UnaryHistory auditRead ∧ PkgSig bundle p pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro packet rootRoute auditRoute rootPkg auditPkg
  obtain
    ⟨aUnary, bUnary, _cUnary, _dUnary, _eUnary, _fUnary, _gUnary, routeAB, _routeCD,
      _routeEF, pUnary, sameProvenanceName, provenancePkg⟩ := packet
  have hUnary : UnaryHistory h :=
    unary_cont_closed aUnary bUnary routeAB
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed hUnary pUnary rootRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed rootUnary (unary_transport pUnary sameProvenanceName) auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist => Cont h p row ∧ hsame row rootRead)
          (fun row : BHist =>
            Cont row n auditRead ∧ PkgSig bundle auditRead pkg ∧ hsame p n)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro rootRead ⟨hsame_refl rootRead, rootUnary, rootPkg⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          cases same
          exact source
      }
      pattern_sound := by
        intro row source
        exact
          ⟨cont_result_hsame_transport rootRoute (hsame_symm source.left),
            source.left⟩
      ledger_sound := by
        intro row source
        have rowRoot : hsame row rootRead := source.left
        have rowAudit : Cont row n auditRead := by
          cases rowRoot
          exact auditRoute
        exact
          ⟨rowAudit, auditPkg, sameProvenanceName⟩
    }
  exact ⟨cert, rootUnary, auditUnary, provenancePkg⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
