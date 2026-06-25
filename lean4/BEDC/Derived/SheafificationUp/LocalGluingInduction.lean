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

theorem SheafificationLocalGluingInduction [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N localFamily gluedRead sheafRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg ->
      Cont P L localFamily ->
        Cont localFamily G gluedRead ->
          Cont gluedRead S sheafRead ->
            Cont sheafRead R replayRead ->
              PkgSig bundle replayRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
                        hsame row L ∨ hsame row G ∨ hsame row S ∨ hsame row H ∨
                          hsame row R ∨ hsame row Q ∨ hsame row N ∨
                            hsame row localFamily ∨ hsame row gluedRead ∨
                              hsame row sheafRead ∨ hsame row replayRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont P L localFamily ∧
                        Cont localFamily G gluedRead ∧ Cont gluedRead S sheafRead ∧
                          Cont sheafRead R replayRead ∧ PkgSig bundle replayRead pkg)
                    hsame ∧
                  UnaryHistory localFamily ∧ UnaryHistory gluedRead ∧
                    UnaryHistory sheafRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier localRoute glueRoute sheafRoute replayRoute replayPkg
  obtain ⟨_cUnary, _tUnary, _jUnary, pUnary, lUnary, gUnary, sUnary, _hUnary, rUnary,
    _qUnary, _nUnary, _provenancePkg, _namePkg⟩ := carrier
  have localFamilyUnary : UnaryHistory localFamily :=
    unary_cont_closed pUnary lUnary localRoute
  have gluedReadUnary : UnaryHistory gluedRead :=
    unary_cont_closed localFamilyUnary gUnary glueRoute
  have sheafReadUnary : UnaryHistory sheafRead :=
    unary_cont_closed gluedReadUnary sUnary sheafRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed sheafReadUnary rUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
              hsame row L ∨ hsame row G ∨ hsame row S ∨ hsame row H ∨
                hsame row R ∨ hsame row Q ∨ hsame row N ∨ hsame row localFamily ∨
                  hsame row gluedRead ∨ hsame row sheafRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont P L localFamily ∧ Cont localFamily G gluedRead ∧
              Cont gluedRead S sheafRead ∧ Cont sheafRead R replayRead ∧
                PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead
        ⟨hsame_refl replayRead, replayReadUnary⟩
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
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localRoute, glueRoute, sheafRoute, replayRoute, replayPkg⟩
  }
  exact ⟨cert, localFamilyUnary, gluedReadUnary, sheafReadUnary, replayReadUnary⟩

end BEDC.Derived.SheafificationUp
