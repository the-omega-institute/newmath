import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_audit_gate_consumption [AskSetup]
    [PackageSetup] {a b c d e f g h p n selected audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg →
      (hsame selected a ∨ hsame selected b ∨ hsame selected c ∨ hsame selected d ∨
        hsame selected e ∨ hsame selected f ∨ hsame selected g) →
        Cont h p audit →
          PkgSig bundle audit pkg →
            SemanticNameCert
                  (fun row : BHist =>
                    hsame row audit ∧ UnaryHistory row ∧ PkgSig bundle audit pkg)
                  (fun row : BHist =>
                    UnaryHistory selected ∧ hsame row audit ∧ Cont h p audit)
                  (fun _row : BHist =>
                    hsame p n ∧ PkgSig bundle p pkg ∧ PkgSig bundle audit pkg)
                  hsame ∧
                UnaryHistory selected ∧ UnaryHistory audit ∧ Cont a b h ∧
                  Cont c d h ∧ Cont e f h ∧ Cont h p audit ∧ hsame p n ∧
                    PkgSig bundle p pkg ∧ PkgSig bundle audit pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro packet selectedRow auditRoute auditPkg
  obtain
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, routeCD, routeEF,
      pUnary, sameProvenanceName, provenancePkg⟩ := packet
  have selectedUnary : UnaryHistory selected := by
    cases selectedRow with
    | inl sameA =>
        exact unary_transport_symm aUnary sameA
    | inr rest =>
        cases rest with
        | inl sameB =>
            exact unary_transport_symm bUnary sameB
        | inr rest =>
            cases rest with
            | inl sameC =>
                exact unary_transport_symm cUnary sameC
            | inr rest =>
                cases rest with
                | inl sameD =>
                    exact unary_transport_symm dUnary sameD
                | inr rest =>
                    cases rest with
                    | inl sameE =>
                        exact unary_transport_symm eUnary sameE
                    | inr rest =>
                        cases rest with
                        | inl sameF =>
                            exact unary_transport_symm fUnary sameF
                        | inr sameG =>
                            exact unary_transport_symm gUnary sameG
  have hUnary : UnaryHistory h :=
    unary_cont_closed aUnary bUnary routeAB
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed hUnary pUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row audit ∧ UnaryHistory row ∧ PkgSig bundle audit pkg)
          (fun row : BHist =>
            UnaryHistory selected ∧ hsame row audit ∧ Cont h p audit)
          (fun _row : BHist =>
            hsame p n ∧ PkgSig bundle p pkg ∧ PkgSig bundle audit pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro audit
          ⟨hsame_refl audit, auditUnary, auditPkg⟩
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
              unary_transport sourceRow.right.left sameRows, sourceRow.right.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact ⟨selectedUnary, sourceRow.left, auditRoute⟩
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨sameProvenanceName, provenancePkg, auditPkg⟩
    }
  exact
    ⟨cert, selectedUnary, auditUnary, routeAB, routeCD, routeEF, auditRoute,
      sameProvenanceName, provenancePkg, auditPkg⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
