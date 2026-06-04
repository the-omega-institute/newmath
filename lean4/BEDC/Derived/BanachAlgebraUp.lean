import BEDC.Derived.BanachAlgebraUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BanachAlgebraUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BanachAlgebraNameCertObligations [AskSetup] [PackageSetup]
    {R N B Q M H C P L productRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R ->
      UnaryHistory N ->
        UnaryHistory B ->
          UnaryHistory Q ->
            UnaryHistory M ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory L ->
                      Cont R N B ->
                        Cont B Q productRead ->
                          Cont productRead M completionRead ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle completionRead pkg ->
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row completionRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row R ∨ hsame row N ∨ hsame row B ∨
                                        hsame row Q ∨ hsame row M ∨ hsame row H ∨
                                          hsame row C ∨ hsame row P ∨ hsame row L ∨
                                            hsame row completionRead)
                                    (fun row : BHist =>
                                      hsame row completionRead ∧ Cont R N B ∧
                                        PkgSig bundle completionRead pkg)
                                    hsame ∧ UnaryHistory productRead ∧
                                      UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BanachAlgebraUp BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro rUnary nUnary bUnary qUnary mUnary _hUnary _cUnary _pUnary _lUnary
    ringNormRoute productRoute completionRoute _provenancePkg completionPkg
  have productUnary : UnaryHistory productRead :=
    unary_cont_closed bUnary qUnary productRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed productUnary mUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row N ∨ hsame row B ∨ hsame row Q ∨
              hsame row M ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row L ∨ hsame row completionRead)
          (fun row : BHist =>
            hsame row completionRead ∧ Cont R N B ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead
        ⟨hsame_refl completionRead, completionUnary⟩
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
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr sourceRow.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, ringNormRoute, completionPkg⟩
  }
  exact ⟨cert, productUnary, completionUnary⟩

end BEDC.Derived.BanachAlgebraUp
