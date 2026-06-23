import BEDC.Derived.UpgradeRegistryUp.StatusPreservation

namespace BEDC.Derived.UpgradeRegistryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UpgradeRegistryPublicExport [AskSetup] [PackageSetup]
    {T S Nx F B A R H C P L statusRead blockerRead namedRead exportRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T → UnaryHistory S → UnaryHistory Nx → UnaryHistory F → UnaryHistory B →
      UnaryHistory A → UnaryHistory R → UnaryHistory C → UnaryHistory L →
        Cont S Nx statusRead → Cont F B blockerRead → Cont C L namedRead →
          Cont statusRead blockerRead exportRead → Cont namedRead exportRead publicRead →
            PkgSig bundle namedRead pkg → PkgSig bundle exportRead pkg →
              PkgSig bundle publicRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row T ∨ hsame row S ∨ hsame row Nx ∨ hsame row B ∨
                        hsame row exportRead ∨ hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle publicRead pkg ∧
                        PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro _targetUnary statusUnary nextUnary fieldUnary blockerUnary _auditUnary
    _formalUnary continuationUnary localUnary statusCont blockerCont namedCont exportCont
    publicCont namedPkg _exportPkg publicPkg
  have statusReadUnary : UnaryHistory statusRead :=
    unary_cont_closed statusUnary nextUnary statusCont
  have blockerReadUnary : UnaryHistory blockerRead :=
    unary_cont_closed fieldUnary blockerUnary blockerCont
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed continuationUnary localUnary namedCont
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed statusReadUnary blockerReadUnary exportCont
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed namedReadUnary exportReadUnary publicCont
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead :=
    ⟨hsame_refl publicRead, publicReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row S ∨ hsame row Nx ∨ hsame row B ∨
              hsame row exportRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle publicRead pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicPkg, namedPkg⟩
  }
  exact ⟨cert, publicReadUnary⟩

end BEDC.Derived.UpgradeRegistryUp
