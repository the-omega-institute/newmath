import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationPlusSeparationObligation [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N separatedRead gluingRead sheafRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont P L separatedRead →
        Cont separatedRead G gluingRead →
          Cont gluingRead S sheafRead →
            PkgSig bundle sheafRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sheafRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row P ∨ hsame row L ∨ hsame row G ∨ hsame row S ∨
                      hsame row separatedRead ∨ hsame row gluingRead ∨
                        hsame row sheafRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont P L separatedRead ∧
                      Cont separatedRead G gluingRead ∧
                        Cont gluingRead S sheafRead ∧ PkgSig bundle sheafRead pkg)
                  hsame ∧
                UnaryHistory separatedRead ∧ UnaryHistory gluingRead ∧
                  UnaryHistory sheafRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier separatedRoute gluingRoute sheafRoute sheafPkg
  obtain ⟨_cUnary, _tUnary, _jUnary, pUnary, lUnary, gUnary, sUnary, _hUnary,
    _rUnary, _qUnary, _nUnary, _qPkg, _nPkg⟩ := carrier
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed pUnary lUnary separatedRoute
  have gluingUnary : UnaryHistory gluingRead :=
    unary_cont_closed separatedUnary gUnary gluingRoute
  have sheafUnary : UnaryHistory sheafRead :=
    unary_cont_closed gluingUnary sUnary sheafRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sheafRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row L ∨ hsame row G ∨ hsame row S ∨
              hsame row separatedRead ∨ hsame row gluingRead ∨ hsame row sheafRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont P L separatedRead ∧
              Cont separatedRead G gluingRead ∧
                Cont gluingRead S sheafRead ∧ PkgSig bundle sheafRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sheafRead ⟨hsame_refl sheafRead, sheafUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, separatedRoute, gluingRoute, sheafRoute, sheafPkg⟩
  }
  exact ⟨cert, separatedUnary, gluingUnary, sheafUnary⟩

end BEDC.Derived.SheafificationUp
