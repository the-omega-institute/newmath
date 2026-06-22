import BEDC.Derived.SetlikeUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SetlikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SetlikeClassifierExtensionalNonescape [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N classifierRead subsetRead extensionalRead transportRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory I ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory H ->
                  UnaryHistory N ->
                    Cont M Q classifierRead ->
                      Cont classifierRead I subsetRead ->
                        Cont subsetRead R extensionalRead ->
                          Cont extensionalRead E transportRead ->
                            Cont transportRead N namedRead ->
                              PkgSig bundle P pkg ->
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row namedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row M ∨ hsame row Q ∨ hsame row I ∨
                                        hsame row R ∨ hsame row E ∨
                                          hsame row classifierRead ∨
                                            hsame row subsetRead ∨
                                              hsame row extensionalRead ∨
                                                hsame row transportRead ∨
                                                  hsame row namedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont M Q classifierRead ∧
                                        Cont classifierRead I subsetRead ∧
                                          Cont subsetRead R extensionalRead ∧
                                            Cont extensionalRead E transportRead ∧
                                              Cont transportRead N namedRead ∧
                                                PkgSig bundle P pkg)
                                    hsame ∧
                                  UnaryHistory classifierRead ∧
                                    UnaryHistory extensionalRead ∧
                                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields mUnary qUnary iUnary rUnary eUnary _hUnary nUnary classifierRoute subsetRoute
    extensionalRoute transportRoute namedRoute provenancePkg
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed mUnary qUnary classifierRoute
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed classifierUnary iUnary subsetRoute
  have extensionalUnary : UnaryHistory extensionalRead :=
    unary_cont_closed subsetUnary rUnary extensionalRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed extensionalUnary eUnary transportRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed transportUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row classifierRead ∨ hsame row subsetRead ∨
                hsame row extensionalRead ∨ hsame row transportRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q classifierRead ∧
              Cont classifierRead I subsetRead ∧ Cont subsetRead R extensionalRead ∧
                Cont extensionalRead E transportRead ∧ Cont transportRead N namedRead ∧
                  PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, classifierRoute, subsetRoute, extensionalRoute, transportRoute,
          namedRoute, provenancePkg⟩
  }
  exact ⟨cert, classifierUnary, extensionalUnary, namedUnary⟩

end BEDC.Derived.SetlikeUp
