import BEDC.Derived.SetlikeUp.RootNameCertObligations

namespace BEDC.Derived.SetlikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SetlikeExtensionalBoundaryClassifierLock [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N extensionalRead transportedRead replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory E ->
            UnaryHistory H ->
              UnaryHistory C ->
                UnaryHistory N ->
                  Cont E Q extensionalRead ->
                    Cont extensionalRead H transportedRead ->
                      Cont transportedRead C replayRead ->
                        Cont replayRead N namedRead ->
                          PkgSig bundle P pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row M ∨ hsame row Q ∨ hsame row E ∨
                                    hsame row extensionalRead ∨ hsame row transportedRead ∨
                                      hsame row replayRead ∨ hsame row namedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont E Q extensionalRead ∧
                                    Cont extensionalRead H transportedRead ∧
                                      Cont transportedRead C replayRead ∧
                                        Cont replayRead N namedRead ∧ PkgSig bundle P pkg)
                                hsame ∧
                              UnaryHistory extensionalRead ∧ UnaryHistory transportedRead ∧
                                UnaryHistory replayRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields rowsM rowsQ rowsE rowsH rowsC rowsN extensionalRoute transportRoute
    replayRoute namedRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have extensionalUnary : UnaryHistory extensionalRead :=
    unary_cont_closed rowsE rowsQ extensionalRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed extensionalUnary rowsH transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportedUnary rowsC replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary rowsN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row E ∨ hsame row extensionalRead ∨
              hsame row transportedRead ∨ hsame row replayRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont E Q extensionalRead ∧
              Cont extensionalRead H transportedRead ∧ Cont transportedRead C replayRead ∧
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, extensionalRoute, transportRoute, replayRoute, namedRoute,
          packageRead⟩
  }
  exact ⟨cert, extensionalUnary, transportedUnary, replayUnary, namedUnary⟩

end BEDC.Derived.SetlikeUp
