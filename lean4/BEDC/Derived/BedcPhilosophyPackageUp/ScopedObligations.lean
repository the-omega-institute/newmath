import BEDC.Derived.BedcPhilosophyPackageUp.NameCertObligations

namespace BEDC.Derived.BedcPhilosophyPackageUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BedcPhilosophyPackage_scoped_obligations [AskSetup] [PackageSetup]
    {T R M G D S C A H K N registryRead auditRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BedcPhilosophyPackageCarrier T R M G D S C A H K N bundle pkg →
      Cont R A registryRead →
        Cont S A auditRead →
          Cont registryRead auditRead scopedRead →
            PkgSig bundle scopedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row T ∨ hsame row R ∨ hsame row M ∨ hsame row G ∨
                      hsame row D ∨ hsame row S ∨ hsame row C ∨ hsame row A ∨
                        hsame row H ∨ hsame row K ∨ hsame row N ∨
                          hsame row registryRead ∨ hsame row auditRead ∨
                            hsame row scopedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont R A registryRead ∧ Cont S A auditRead ∧
                      Cont registryRead auditRead scopedRead ∧ PkgSig bundle scopedRead pkg)
                  hsame ∧
                UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro carrier routeRegistry routeAudit routeScoped scopedPkg
  have unaryR : UnaryHistory R := carrier.right.left
  have unaryS : UnaryHistory S := carrier.right.right.right.right.right.left
  have unaryA : UnaryHistory A := carrier.right.right.right.right.right.right.right.left
  have registryUnary : UnaryHistory registryRead :=
    unary_cont_closed unaryR unaryA routeRegistry
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed unaryS unaryA routeAudit
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed registryUnary auditUnary routeScoped
  have sourceScoped :
      (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row) scopedRead := by
    exact ⟨hsame_refl scopedRead, scopedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row R ∨ hsame row M ∨ hsame row G ∨
              hsame row D ∨ hsame row S ∨ hsame row C ∨ hsame row A ∨
                hsame row H ∨ hsame row K ∨ hsame row N ∨ hsame row registryRead ∨
                  hsame row auditRead ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R A registryRead ∧ Cont S A auditRead ∧
              Cont registryRead auditRead scopedRead ∧ PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead sourceScoped
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
        exact ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeRegistry, routeAudit, routeScoped, scopedPkg⟩
  }
  exact ⟨cert, scopedUnary⟩

end BEDC.Derived.BedcPhilosophyPackageUp
