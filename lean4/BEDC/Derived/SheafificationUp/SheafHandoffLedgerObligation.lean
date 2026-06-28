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

theorem SheafificationSheafHandoffLedgerObligation [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N sourceRead localityRead gluingRead sheafRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C T sourceRead →
        Cont P L localityRead →
          Cont localityRead G gluingRead →
            Cont gluingRead S sheafRead →
              Cont sheafRead H handoffRead →
                PkgSig bundle handoffRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
                          hsame row L ∨ hsame row G ∨ hsame row S ∨ hsame row H ∨
                            hsame row R ∨ hsame row Q ∨ hsame row N ∨
                              hsame row sourceRead ∨ hsame row localityRead ∨
                                hsame row gluingRead ∨ hsame row sheafRead ∨
                                  hsame row handoffRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont C T sourceRead ∧ Cont P L localityRead ∧
                          Cont localityRead G gluingRead ∧ Cont gluingRead S sheafRead ∧
                            Cont sheafRead H handoffRead ∧
                              PkgSig bundle handoffRead pkg)
                      hsame ∧
                    UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: SheafificationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute localityRoute gluingRoute sheafRoute handoffRoute handoffPkg
  obtain ⟨cUnary, tUnary, _jUnary, pUnary, lUnary, gUnary, sUnary, hUnary, _rUnary,
    _qUnary, _nUnary, _qPkg, _nPkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed cUnary tUnary sourceRoute
  have localityReadUnary : UnaryHistory localityRead :=
    unary_cont_closed pUnary lUnary localityRoute
  have gluingReadUnary : UnaryHistory gluingRead :=
    unary_cont_closed localityReadUnary gUnary gluingRoute
  have sheafReadUnary : UnaryHistory sheafRead :=
    unary_cont_closed gluingReadUnary sUnary sheafRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed sheafReadUnary hUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨ hsame row L ∨
              hsame row G ∨ hsame row S ∨ hsame row H ∨ hsame row R ∨ hsame row Q ∨
                hsame row N ∨ hsame row sourceRead ∨ hsame row localityRead ∨
                  hsame row gluingRead ∨ hsame row sheafRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C T sourceRead ∧ Cont P L localityRead ∧
              Cont localityRead G gluingRead ∧ Cont gluingRead S sheafRead ∧
                Cont sheafRead H handoffRead ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead
        ⟨hsame_refl handoffRead, handoffReadUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, localityRoute, gluingRoute, sheafRoute, handoffRoute,
          handoffPkg⟩
  }
  exact ⟨cert, handoffReadUnary⟩

end BEDC.Derived.SheafificationUp
