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

theorem SheafificationRootObligationCarrier [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N sourceRead localityRead gluingRead targetRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C T sourceRead →
        Cont sourceRead P localityRead →
          Cont localityRead G gluingRead →
            Cont gluingRead S targetRead →
              Cont targetRead Q namedRead →
                PkgSig bundle N pkg →
                  SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
                        hsame row L ∨ hsame row G ∨ hsame row S ∨ hsame row H ∨
                          hsame row R ∨ hsame row Q ∨ hsame row N ∨
                            hsame row sourceRead ∨ hsame row localityRead ∨
                              hsame row gluingRead ∨ hsame row targetRead ∨
                                hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont C T sourceRead ∧
                        Cont sourceRead P localityRead ∧ Cont localityRead G gluingRead ∧
                          Cont gluingRead S targetRead ∧ Cont targetRead Q namedRead ∧
                            PkgSig bundle N pkg)
                    hsame ∧ UnaryHistory sourceRead ∧ UnaryHistory localityRead ∧
                      UnaryHistory gluingRead ∧ UnaryHistory targetRead ∧
                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier sourceRoute localityRoute gluingRoute targetRoute namedRoute namePkg
  obtain ⟨cUnary, tUnary, _jUnary, pUnary, _lUnary, gUnary, sUnary, _hUnary, _rUnary,
    qUnary, _nUnary, _qPkg, _carrierNamePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed cUnary tUnary sourceRoute
  have localityReadUnary : UnaryHistory localityRead :=
    unary_cont_closed sourceReadUnary pUnary localityRoute
  have gluingReadUnary : UnaryHistory gluingRead :=
    unary_cont_closed localityReadUnary gUnary gluingRoute
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed gluingReadUnary sUnary targetRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed targetReadUnary qUnary namedRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨ hsame row L ∨
            hsame row G ∨ hsame row S ∨ hsame row H ∨ hsame row R ∨ hsame row Q ∨
              hsame row N ∨ hsame row sourceRead ∨ hsame row localityRead ∨
                hsame row gluingRead ∨ hsame row targetRead ∨ hsame row namedRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont C T sourceRead ∧ Cont sourceRead P localityRead ∧
            Cont localityRead G gluingRead ∧ Cont gluingRead S targetRead ∧
              Cont targetRead Q namedRead ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inr sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, sourceRoute, localityRoute, gluingRoute, targetRoute, namedRoute,
          namePkg⟩
  }
  exact
    ⟨cert, sourceReadUnary, localityReadUnary, gluingReadUnary, targetReadUnary,
      namedReadUnary⟩

end BEDC.Derived.SheafificationUp
