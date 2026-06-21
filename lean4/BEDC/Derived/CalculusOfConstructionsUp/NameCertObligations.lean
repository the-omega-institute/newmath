import BEDC.Derived.CalculusOfConstructionsUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CalculusOfConstructionsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusOfConstructionsCarrier_namecert_obligations [AskSetup] [PackageSetup]
    (C : CalculusOfConstructionsUp)
    {S Pi L A Gamma Sigma B R H K P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    calculusOfConstructionsFields C = [S, Pi, L, A, Gamma, Sigma, B, R, H, K, P, N] ->
      UnaryHistory S ->
        UnaryHistory Pi ->
          UnaryHistory L ->
            UnaryHistory A ->
              UnaryHistory Gamma ->
                UnaryHistory Sigma ->
                  UnaryHistory R ->
                    UnaryHistory H ->
                      UnaryHistory P ->
                        UnaryHistory N ->
                          Cont Gamma Sigma B ->
                            Cont B R K ->
                              PkgSig bundle P pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row S ∨ hsame row Pi ∨ hsame row L ∨
                                        hsame row A ∨ hsame row Gamma ∨ hsame row Sigma ∨
                                          hsame row B ∨ hsame row R ∨ hsame row H ∨
                                            hsame row K ∨ hsame row P ∨ hsame row N)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont Gamma Sigma B ∧
                                        Cont B R K ∧ PkgSig bundle P pkg)
                                    hsame ∧
                                  UnaryHistory B ∧ UnaryHistory K := by
  -- BEDC touchpoint anchor: CalculusOfConstructionsUp calculusOfConstructionsFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsS rowsPi rowsL rowsA rowsGamma rowsSigma rowsR rowsH rowsP rowsN
    betaRoute replayRoute packageRead
  have _acceptedFields :
      calculusOfConstructionsFields C = [S, Pi, L, A, Gamma, Sigma, B, R, H, K, P, N] :=
    fields
  have betaUnary : UnaryHistory B :=
    unary_cont_closed rowsGamma rowsSigma betaRoute
  have replayUnary : UnaryHistory K :=
    unary_cont_closed betaUnary rowsR replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row Pi ∨ hsame row L ∨ hsame row A ∨
              hsame row Gamma ∨ hsame row Sigma ∨ hsame row B ∨ hsame row R ∨
                hsame row H ∨ hsame row K ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Gamma Sigma B ∧ Cont B R K ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, rowsN⟩
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
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, betaRoute, replayRoute, packageRead⟩
  }
  exact ⟨cert, betaUnary, replayUnary⟩

end BEDC.Derived.CalculusOfConstructionsUp
