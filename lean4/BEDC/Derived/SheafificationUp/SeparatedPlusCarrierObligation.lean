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

theorem SheafificationSeparatedPlusCarrierObligation [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N separatedRead localityRead plusRead sheafRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg ->
      Cont C J separatedRead ->
        Cont P L localityRead ->
          Cont localityRead G plusRead ->
            Cont plusRead S sheafRead ->
              PkgSig bundle sheafRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sheafRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row C ∨ hsame row J ∨ hsame row P ∨ hsame row L ∨
                        hsame row G ∨ hsame row S ∨ hsame row separatedRead ∨
                          hsame row localityRead ∨ hsame row plusRead ∨
                            hsame row sheafRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont C J separatedRead ∧
                        Cont P L localityRead ∧ Cont localityRead G plusRead ∧
                          Cont plusRead S sheafRead ∧ PkgSig bundle sheafRead pkg)
                    hsame ∧
                  UnaryHistory separatedRead ∧ UnaryHistory localityRead ∧
                    UnaryHistory plusRead ∧ UnaryHistory sheafRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier separatedRoute localityRoute plusRoute sheafRoute sheafPkg
  obtain ⟨cUnary, _tUnary, jUnary, pUnary, lUnary, gUnary, sUnary, _hUnary, _rUnary,
    _qUnary, _nUnary, _qPkg, _namePkg⟩ := carrier
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed cUnary jUnary separatedRoute
  have localityUnary : UnaryHistory localityRead :=
    unary_cont_closed pUnary lUnary localityRoute
  have plusUnary : UnaryHistory plusRead :=
    unary_cont_closed localityUnary gUnary plusRoute
  have sheafUnary : UnaryHistory sheafRead :=
    unary_cont_closed plusUnary sUnary sheafRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sheafRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row J ∨ hsame row P ∨ hsame row L ∨
              hsame row G ∨ hsame row S ∨ hsame row separatedRead ∨
                hsame row localityRead ∨ hsame row plusRead ∨ hsame row sheafRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C J separatedRead ∧ Cont P L localityRead ∧
              Cont localityRead G plusRead ∧ Cont plusRead S sheafRead ∧
                PkgSig bundle sheafRead pkg)
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
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, separatedRoute, localityRoute, plusRoute, sheafRoute, sheafPkg⟩
  }
  exact ⟨cert, separatedUnary, localityUnary, plusUnary, sheafUnary⟩

end BEDC.Derived.SheafificationUp
