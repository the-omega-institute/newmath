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

theorem SheafificationKernelScopePackage [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N localRead gluedRead sheafRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont P L localRead →
        Cont localRead G gluedRead →
          Cont gluedRead S sheafRead →
            PkgSig bundle Q pkg →
              PkgSig bundle N pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sheafRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
                        hsame row L ∨ hsame row G ∨ hsame row S ∨ hsame row H ∨
                          hsame row R ∨ hsame row Q ∨ hsame row N ∨ hsame row sheafRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont P L localRead ∧
                        Cont localRead G gluedRead ∧ Cont gluedRead S sheafRead ∧
                          PkgSig bundle Q pkg ∧ PkgSig bundle N pkg)
                    hsame := by
  -- BEDC touchpoint anchor: SheafificationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier localRoute gluedRoute sheafRoute provenancePkg namePkg
  obtain ⟨_cUnary, _tUnary, _jUnary, pUnary, lUnary, gUnary, sUnary, _hUnary,
    _rUnary, _qUnary, _nUnary, _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed pUnary lUnary localRoute
  have gluedUnary : UnaryHistory gluedRead :=
    unary_cont_closed localUnary gUnary gluedRoute
  have sheafUnary : UnaryHistory sheafRead :=
    unary_cont_closed gluedUnary sUnary sheafRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro sheafRead
        ⟨hsame_refl sheafRead, sheafUnary⟩
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
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, localRoute, gluedRoute, sheafRoute, provenancePkg, namePkg⟩
  }

end BEDC.Derived.SheafificationUp
