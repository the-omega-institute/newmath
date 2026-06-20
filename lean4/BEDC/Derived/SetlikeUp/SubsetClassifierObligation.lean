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

theorem SetlikeSubsetClassifierObligation [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N subsetReplay classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory I ->
            UnaryHistory H ->
              UnaryHistory C ->
                Cont M Q classifierRead ->
                  Cont Q I subsetReplay ->
                    PkgSig bundle N pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row subsetReplay ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row M ∨ hsame row Q ∨ hsame row I ∨
                              hsame row classifierRead ∨ hsame row subsetReplay)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont M Q classifierRead ∧
                              Cont Q I subsetReplay ∧ PkgSig bundle N pkg)
                          hsame ∧ UnaryHistory classifierRead ∧
                        UnaryHistory subsetReplay := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro fields rowsM rowsQ rowsI _rowsH _rowsC classifierRoute subsetRoute namePkg
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed rowsM rowsQ classifierRoute
  have subsetUnary : UnaryHistory subsetReplay :=
    unary_cont_closed rowsQ rowsI subsetRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row subsetReplay ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row classifierRead ∨
              hsame row subsetReplay)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q classifierRead ∧ Cont Q I subsetReplay ∧
              PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro subsetReplay ⟨hsame_refl subsetReplay, subsetUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, classifierRoute, subsetRoute, namePkg⟩
  }
  exact ⟨cert, classifierUnary, subsetUnary⟩

end BEDC.Derived.SetlikeUp
