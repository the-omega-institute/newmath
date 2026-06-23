import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationGluingExactness [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N localFamily gluedRead sheafRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont P L localFamily →
        Cont localFamily G gluedRead →
          Cont gluedRead S sheafRead →
            PkgSig bundle sheafRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sheafRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row P ∨ hsame row L ∨ hsame row G ∨ hsame row S ∨
                      hsame row localFamily ∨ hsame row gluedRead ∨ hsame row sheafRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont P L localFamily ∧
                      Cont localFamily G gluedRead ∧ Cont gluedRead S sheafRead ∧
                        PkgSig bundle sheafRead pkg)
                  hsame ∧
                UnaryHistory localFamily ∧ UnaryHistory gluedRead ∧
                  UnaryHistory sheafRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier localRoute glueRoute sheafRoute sheafPkg
  obtain ⟨_cUnary, _tUnary, _jUnary, pUnary, lUnary, gUnary, sUnary, _hUnary, _rUnary,
    _qUnary, _nUnary, _namePkg⟩ := carrier
  have localFamilyUnary : UnaryHistory localFamily :=
    unary_cont_closed pUnary lUnary localRoute
  have gluedReadUnary : UnaryHistory gluedRead :=
    unary_cont_closed localFamilyUnary gUnary glueRoute
  have sheafReadUnary : UnaryHistory sheafRead :=
    unary_cont_closed gluedReadUnary sUnary sheafRoute
  have sourceSheaf :
      (fun row : BHist => hsame row sheafRead ∧ UnaryHistory row) sheafRead :=
    ⟨hsame_refl sheafRead, sheafReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sheafRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row L ∨ hsame row G ∨ hsame row S ∨
              hsame row localFamily ∨ hsame row gluedRead ∨ hsame row sheafRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont P L localFamily ∧ Cont localFamily G gluedRead ∧
              Cont gluedRead S sheafRead ∧ PkgSig bundle sheafRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sheafRead sourceSheaf
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localRoute, glueRoute, sheafRoute, sheafPkg⟩
  }
  exact ⟨cert, localFamilyUnary, gluedReadUnary, sheafReadUnary⟩

end BEDC.Derived.SheafificationUp
