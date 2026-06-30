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

theorem SheafificationPlusLocalityGluingLedger [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N sourceRead localRead gluingRead sheafRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C T sourceRead →
        Cont P L localRead →
          Cont localRead G gluingRead →
            Cont gluingRead S sheafRead →
              Cont sheafRead R replayRead →
                PkgSig bundle replayRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
                          hsame row L ∨ hsame row G ∨ hsame row S ∨ hsame row R ∨
                            hsame row sourceRead ∨ hsame row localRead ∨
                              hsame row gluingRead ∨ hsame row sheafRead ∨
                                hsame row replayRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont C T sourceRead ∧ Cont P L localRead ∧
                          Cont localRead G gluingRead ∧ Cont gluingRead S sheafRead ∧
                            Cont sheafRead R replayRead ∧ PkgSig bundle replayRead pkg)
                      hsame ∧
                    UnaryHistory L ∧ UnaryHistory G ∧ UnaryHistory S ∧
                      UnaryHistory sourceRead ∧ UnaryHistory localRead ∧
                        UnaryHistory gluingRead ∧ UnaryHistory sheafRead ∧
                          UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: SheafificationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute localRoute gluingRoute sheafRoute replayRoute replayPkg
  obtain ⟨cUnary, tUnary, _jUnary, pUnary, lUnary, gUnary, sUnary, _hUnary, rUnary,
    _qUnary, _nUnary, _qPkg, _nPkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed cUnary tUnary sourceRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed pUnary lUnary localRoute
  have gluingUnary : UnaryHistory gluingRead :=
    unary_cont_closed localUnary gUnary gluingRoute
  have sheafUnary : UnaryHistory sheafRead :=
    unary_cont_closed gluingUnary sUnary sheafRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed sheafUnary rUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
              hsame row L ∨ hsame row G ∨ hsame row S ∨ hsame row R ∨
                hsame row sourceRead ∨ hsame row localRead ∨ hsame row gluingRead ∨
                  hsame row sheafRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C T sourceRead ∧ Cont P L localRead ∧
              Cont localRead G gluingRead ∧ Cont gluingRead S sheafRead ∧
                Cont sheafRead R replayRead ∧ PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead
        ⟨hsame_refl replayRead, replayUnary⟩
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
                          (Or.inr
                            (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, localRoute, gluingRoute, sheafRoute, replayRoute,
          replayPkg⟩
  }
  exact
    ⟨cert, lUnary, gUnary, sUnary, sourceUnary, localUnary, gluingUnary, sheafUnary,
      replayUnary⟩

end BEDC.Derived.SheafificationUp
