import BEDC.Derived.MachineExportBoundaryUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MachineExportBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MachineExportBoundary_namecert_obligations [AskSetup] [PackageSetup]
    {R T A F H C P N registryRead auditRead refusalRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R → UnaryHistory T → UnaryHistory A → UnaryHistory F → UnaryHistory N →
      Cont R T registryRead → Cont registryRead A auditRead →
        Cont auditRead F refusalRead → Cont refusalRead N namedRead →
          PkgSig bundle P pkg → PkgSig bundle N pkg →
            SemanticNameCert
                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row R ∨ hsame row T ∨ hsame row A ∨ hsame row F ∨
                    hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                      hsame row registryRead ∨ hsame row auditRead ∨
                        hsame row refusalRead ∨ hsame row namedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont R T registryRead ∧
                    Cont registryRead A auditRead ∧ Cont auditRead F refusalRead ∧
                      Cont refusalRead N namedRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle N pkg)
                hsame ∧ UnaryHistory registryRead ∧ UnaryHistory auditRead ∧
              UnaryHistory refusalRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro unaryR unaryT unaryA unaryF unaryN registryRoute auditRoute refusalRoute namedRoute
    provenancePkg namePkg
  have registryUnary : UnaryHistory registryRead :=
    unary_cont_closed unaryR unaryT registryRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed registryUnary unaryA auditRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed auditUnary unaryF refusalRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed refusalUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row T ∨ hsame row A ∨ hsame row F ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row registryRead ∨ hsame row auditRead ∨
                  hsame row refusalRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R T registryRead ∧ Cont registryRead A auditRead ∧
              Cont auditRead F refusalRead ∧ Cont refusalRead N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, registryRoute, auditRoute, refusalRoute, namedRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, registryUnary, auditUnary, refusalUnary, namedUnary⟩

end BEDC.Derived.MachineExportBoundaryUp
