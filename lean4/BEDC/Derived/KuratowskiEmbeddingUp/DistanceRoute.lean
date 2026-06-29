import BEDC.Derived.KuratowskiEmbeddingUp.NameCertObligations

namespace BEDC.Derived.KuratowskiEmbeddingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KuratowskiEmbeddingCarrier_distance_route [AskSetup] [PackageSetup]
    {M B D T I H C _P _N distanceRead targetRead targetRoute isometryRead replayRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory B ->
        UnaryHistory D ->
          UnaryHistory T ->
            UnaryHistory I ->
              UnaryHistory H ->
                UnaryHistory C ->
                  Cont M B distanceRead ->
                    Cont distanceRead D targetRead ->
                      Cont targetRead T targetRoute ->
                        Cont targetRoute I isometryRead ->
                          Cont isometryRead H replayRead ->
                            Cont replayRead C publicRead ->
                              PkgSig bundle publicRead pkg ->
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row publicRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row M ∨ hsame row B ∨ hsame row D ∨
                                        hsame row T ∨ hsame row I ∨ hsame row H ∨
                                          hsame row C ∨ hsame row publicRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ PkgSig bundle publicRead pkg)
                                    hsame ∧
                                  UnaryHistory distanceRead ∧ UnaryHistory targetRead ∧
                                    UnaryHistory targetRoute ∧ UnaryHistory isometryRead ∧
                                      UnaryHistory replayRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro mUnary bUnary dUnary tUnary iUnary hUnary cUnary distanceRoute targetRouteRow
    targetRouteRow' isometryRoute replayRoute publicRoute publicPkg
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed mUnary bUnary distanceRoute
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed distanceUnary dUnary targetRouteRow
  have targetRouteUnary : UnaryHistory targetRoute :=
    unary_cont_closed targetUnary tUnary targetRouteRow'
  have isometryUnary : UnaryHistory isometryRead :=
    unary_cont_closed targetRouteUnary iUnary isometryRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed isometryUnary hUnary replayRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed replayUnary cUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row B ∨ hsame row D ∨ hsame row T ∨ hsame row I ∨
              hsame row H ∨ hsame row C ∨ hsame row publicRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨publicRead, hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicPkg⟩
  }
  exact
    ⟨cert, distanceUnary, targetUnary, targetRouteUnary, isometryUnary, replayUnary,
      publicUnary⟩

end BEDC.Derived.KuratowskiEmbeddingUp
