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

theorem SetlikeSubsetClassifierExactness [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N implicationRead comprehensionRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory Q ->
        UnaryHistory I ->
          UnaryHistory R ->
            UnaryHistory E ->
              Cont Q I implicationRead ->
                Cont implicationRead R comprehensionRead ->
                  Cont comprehensionRead E boundaryRead ->
                    PkgSig bundle P pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
                              hsame row implicationRead ∨ hsame row comprehensionRead ∨
                                hsame row boundaryRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont Q I implicationRead ∧
                              Cont implicationRead R comprehensionRead ∧
                                Cont comprehensionRead E boundaryRead ∧ PkgSig bundle P pkg)
                          hsame ∧
                        UnaryHistory implicationRead ∧ UnaryHistory comprehensionRead ∧
                          UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields qUnary iUnary rUnary eUnary implicationRoute comprehensionRoute boundaryRoute
    packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have implicationUnary : UnaryHistory implicationRead :=
    unary_cont_closed qUnary iUnary implicationRoute
  have comprehensionUnary : UnaryHistory comprehensionRead :=
    unary_cont_closed implicationUnary rUnary comprehensionRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed comprehensionUnary eUnary boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row implicationRead ∨ hsame row comprehensionRead ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q I implicationRead ∧
              Cont implicationRead R comprehensionRead ∧
                Cont comprehensionRead E boundaryRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, implicationRoute, comprehensionRoute, boundaryRoute, packageRead⟩
  }
  exact ⟨cert, implicationUnary, comprehensionUnary, boundaryUnary⟩

end BEDC.Derived.SetlikeUp
