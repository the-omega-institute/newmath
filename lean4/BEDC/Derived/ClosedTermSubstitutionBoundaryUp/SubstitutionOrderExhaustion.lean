import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundarySubstitutionOrderExhaustion [AskSetup] [PackageSetup]
    {source value depth sourceClosed valueClosed shift substitute ledger audit transport route
      provenance localName substitutionRead auditRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory sourceClosed → UnaryHistory valueClosed → UnaryHistory ledger →
      UnaryHistory audit → UnaryHistory transport → UnaryHistory localName →
        Cont sourceClosed valueClosed substitutionRead →
          Cont substitutionRead ledger auditRead →
            Cont auditRead audit finalRead →
              PkgSig bundle provenance pkg →
                PkgSig bundle localName pkg →
                  SemanticNameCert
                    (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row sourceClosed ∨ hsame row valueClosed ∨ hsame row ledger ∨
                        hsame row audit ∨ hsame row finalRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont substitutionRead ledger auditRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                    hsame ∧ UnaryHistory substitutionRead ∧ UnaryHistory auditRead ∧
                      UnaryHistory finalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro sourceClosedUnary valueClosedUnary ledgerUnary auditUnary _transportUnary _localNameUnary
    substitutionRoute auditRoute finalRoute provenancePkg localNamePkg
  have substitutionUnary : UnaryHistory substitutionRead :=
    unary_cont_closed sourceClosedUnary valueClosedUnary substitutionRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed substitutionUnary ledgerUnary auditRoute
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed auditReadUnary auditUnary finalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceClosed ∨ hsame row valueClosed ∨ hsame row ledger ∨
              hsame row audit ∨ hsame row finalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont substitutionRead ledger auditRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro finalRead ⟨hsame_refl finalRead, finalUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, auditRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, substitutionUnary, auditReadUnary, finalUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
