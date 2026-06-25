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

theorem SheafificationCoverGluingNonescape [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N coverRead localityRead gluingRead sheafRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont J P coverRead →
        Cont coverRead L localityRead →
          Cont localityRead G gluingRead →
            Cont gluingRead S sheafRead →
              PkgSig bundle sheafRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sheafRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
                        hsame row L ∨ hsame row G ∨ hsame row S ∨
                          hsame row coverRead ∨ hsame row localityRead ∨
                            hsame row gluingRead ∨ hsame row sheafRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont J P coverRead ∧
                        Cont coverRead L localityRead ∧
                          Cont localityRead G gluingRead ∧
                            Cont gluingRead S sheafRead ∧
                              PkgSig bundle sheafRead pkg)
                    hsame ∧
                  UnaryHistory coverRead ∧ UnaryHistory localityRead ∧
                    UnaryHistory gluingRead ∧ UnaryHistory sheafRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier coverRoute localityRoute gluingRoute sheafRoute sheafPkg
  obtain ⟨_cUnary, _tUnary, jUnary, pUnary, lUnary, gUnary, sUnary, _hUnary,
    _rUnary, _qUnary, _nUnary, _provenancePkg, _namePkg⟩ := carrier
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed jUnary pUnary coverRoute
  have localityUnary : UnaryHistory localityRead :=
    unary_cont_closed coverUnary lUnary localityRoute
  have gluingUnary : UnaryHistory gluingRead :=
    unary_cont_closed localityUnary gUnary gluingRoute
  have sheafUnary : UnaryHistory sheafRead :=
    unary_cont_closed gluingUnary sUnary sheafRoute
  have sourceSheaf :
      (fun row : BHist => hsame row sheafRead ∧ UnaryHistory row) sheafRead :=
    ⟨hsame_refl sheafRead, sheafUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sheafRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
              hsame row L ∨ hsame row G ∨ hsame row S ∨ hsame row coverRead ∨
                hsame row localityRead ∨ hsame row gluingRead ∨ hsame row sheafRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J P coverRead ∧ Cont coverRead L localityRead ∧
              Cont localityRead G gluingRead ∧ Cont gluingRead S sheafRead ∧
                PkgSig bundle sheafRead pkg)
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
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverRoute, localityRoute, gluingRoute, sheafRoute,
          sheafPkg⟩
  }
  exact ⟨cert, coverUnary, localityUnary, gluingUnary, sheafUnary⟩

end BEDC.Derived.SheafificationUp
