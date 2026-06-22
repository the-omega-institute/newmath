import BEDC.Derived.SetlikeUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
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

theorem SetlikeExtensionalBoundaryObligation [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipRead subsetRead boundaryRead transportRead replayRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory I ->
            UnaryHistory E ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory N ->
                    Cont M Q membershipRead ->
                      Cont Q I subsetRead ->
                        Cont subsetRead E boundaryRead ->
                          Cont boundaryRead H transportRead ->
                            Cont transportRead C replayRead ->
                              Cont replayRead N namedRead ->
                                PkgSig bundle P pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row namedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row M ∨ hsame row Q ∨ hsame row I ∨
                                          hsame row E ∨ hsame row H ∨ hsame row C ∨
                                            hsame row N ∨ hsame row membershipRead ∨
                                              hsame row subsetRead ∨ hsame row boundaryRead ∨
                                                hsame row transportRead ∨
                                                  hsame row replayRead ∨
                                                    hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont M Q membershipRead ∧
                                          Cont Q I subsetRead ∧ Cont subsetRead E boundaryRead ∧
                                            Cont boundaryRead H transportRead ∧
                                              Cont transportRead C replayRead ∧
                                                Cont replayRead N namedRead ∧
                                                  PkgSig bundle P pkg)
                                      hsame ∧ UnaryHistory boundaryRead ∧
                                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields unaryM unaryQ unaryI unaryE unaryH unaryC unaryN membershipRoute subsetRoute
    boundaryRoute transportRoute replayRoute namedRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed unaryM unaryQ membershipRoute
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed unaryQ unaryI subsetRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed subsetUnary unaryE boundaryRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed boundaryUnary unaryH transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary unaryC replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row E ∨ hsame row H ∨
              hsame row C ∨ hsame row N ∨ hsame row membershipRead ∨
                hsame row subsetRead ∨ hsame row boundaryRead ∨ hsame row transportRead ∨
                  hsame row replayRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipRead ∧ Cont Q I subsetRead ∧
              Cont subsetRead E boundaryRead ∧ Cont boundaryRead H transportRead ∧
                Cont transportRead C replayRead ∧ Cont replayRead N namedRead ∧
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, membershipRoute, subsetRoute, boundaryRoute, transportRoute,
          replayRoute, namedRoute, packageRead⟩
  }
  exact ⟨cert, boundaryUnary, namedUnary⟩

end BEDC.Derived.SetlikeUp
