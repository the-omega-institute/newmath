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

theorem SheafificationCoverLocalGluingObligation [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N coverWindow localRead gluingRead sheafRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C T coverWindow →
        Cont P L localRead →
          Cont localRead G gluingRead →
            Cont gluingRead S sheafRead →
              PkgSig bundle Q pkg →
                PkgSig bundle N pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sheafRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
                          hsame row L ∨ hsame row G ∨ hsame row S ∨ hsame row H ∨
                            hsame row R ∨ hsame row Q ∨ hsame row N ∨
                              hsame row coverWindow ∨ hsame row localRead ∨
                                hsame row gluingRead ∨ hsame row sheafRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont C T coverWindow ∧
                          Cont P L localRead ∧ Cont localRead G gluingRead ∧
                            Cont gluingRead S sheafRead ∧ PkgSig bundle Q pkg ∧
                              PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory coverWindow ∧ UnaryHistory localRead ∧
                      UnaryHistory gluingRead ∧ UnaryHistory sheafRead := by
  -- BEDC touchpoint anchor: SheafificationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coverRoute localRoute gluingRoute sheafRoute qPkg nPkg
  obtain ⟨cUnary, tUnary, _jUnary, pUnary, lUnary, gUnary, sUnary, _hUnary,
    _rUnary, _qUnary, _nUnary, _qPkgCarrier, _nPkgCarrier⟩ := carrier
  have coverUnary : UnaryHistory coverWindow :=
    unary_cont_closed cUnary tUnary coverRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed pUnary lUnary localRoute
  have gluingUnary : UnaryHistory gluingRead :=
    unary_cont_closed localUnary gUnary gluingRoute
  have sheafUnary : UnaryHistory sheafRead :=
    unary_cont_closed gluingUnary sUnary sheafRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sheafRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨ hsame row L ∨
              hsame row G ∨ hsame row S ∨ hsame row H ∨ hsame row R ∨ hsame row Q ∨
                hsame row N ∨ hsame row coverWindow ∨ hsame row localRead ∨
                  hsame row gluingRead ∨ hsame row sheafRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C T coverWindow ∧ Cont P L localRead ∧
              Cont localRead G gluingRead ∧ Cont gluingRead S sheafRead ∧
                PkgSig bundle Q pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sheafRead ⟨hsame_refl sheafRead, sheafUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, coverRoute, localRoute, gluingRoute, sheafRoute, qPkg, nPkg⟩
  }
  exact ⟨cert, coverUnary, localUnary, gluingUnary, sheafUnary⟩

end BEDC.Derived.SheafificationUp
