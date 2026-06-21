import BEDC.Derived.SchurLemmaUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SchurLemmaUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SchurLemmaCarrier_namecert_obligations [AskSetup] [PackageSetup] (K : SchurLemmaUp)
    {U V H S T R P N homRead boundaryRead transportedRead replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    schurLemmaFields K = [U, V, H, S, T, R, P, N] ->
      UnaryHistory U ->
        UnaryHistory V ->
          UnaryHistory S ->
            UnaryHistory T ->
              UnaryHistory R ->
                UnaryHistory N ->
                  Cont U V homRead ->
                    Cont homRead S boundaryRead ->
                      Cont boundaryRead T transportedRead ->
                        Cont transportedRead R replayRead ->
                          Cont replayRead N namedRead ->
                            PkgSig bundle P pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row U ∨ hsame row V ∨ hsame row H ∨
                                      hsame row S ∨ hsame row T ∨ hsame row R ∨
                                        hsame row P ∨ hsame row N ∨ hsame row homRead ∨
                                          hsame row boundaryRead ∨
                                            hsame row transportedRead ∨
                                              hsame row replayRead ∨ hsame row namedRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont U V homRead ∧
                                      Cont homRead S boundaryRead ∧
                                        Cont boundaryRead T transportedRead ∧
                                          Cont transportedRead R replayRead ∧
                                            Cont replayRead N namedRead ∧
                                              PkgSig bundle P pkg)
                                  hsame ∧
                                UnaryHistory homRead ∧ UnaryHistory boundaryRead ∧
                                  UnaryHistory transportedRead ∧ UnaryHistory replayRead ∧
                                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SchurLemmaUp schurLemmaFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsU rowsV rowsS rowsT rowsR rowsN homRoute boundaryRoute transportedRoute
    replayRoute namedRoute packageRead
  have _acceptedFields : schurLemmaFields K = [U, V, H, S, T, R, P, N] := fields
  have homUnary : UnaryHistory homRead :=
    unary_cont_closed rowsU rowsV homRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed homUnary rowsS boundaryRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed boundaryUnary rowsT transportedRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportedUnary rowsR replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary rowsN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row V ∨ hsame row H ∨ hsame row S ∨ hsame row T ∨
              hsame row R ∨ hsame row P ∨ hsame row N ∨ hsame row homRead ∨
                hsame row boundaryRead ∨ hsame row transportedRead ∨ hsame row replayRead ∨
                  hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U V homRead ∧ Cont homRead S boundaryRead ∧
              Cont boundaryRead T transportedRead ∧ Cont transportedRead R replayRead ∧
                Cont replayRead N namedRead ∧ PkgSig bundle P pkg)
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
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, homRoute, boundaryRoute, transportedRoute, replayRoute, namedRoute,
          packageRead⟩
  }
  exact ⟨cert, homUnary, boundaryUnary, transportedUnary, replayUnary, namedUnary⟩

end BEDC.Derived.SchurLemmaUp
