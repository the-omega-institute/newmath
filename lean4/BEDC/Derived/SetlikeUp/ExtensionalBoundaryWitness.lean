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

theorem SetlikeExtensionalBoundaryWitness [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipRead subsetRead comprehensionRead boundaryRead
      transportRead replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory I ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory N ->
                      Cont M Q membershipRead ->
                        Cont Q I subsetRead ->
                          Cont I R comprehensionRead ->
                            Cont comprehensionRead E boundaryRead ->
                              Cont boundaryRead H transportRead ->
                                Cont transportRead C replayRead ->
                                  Cont replayRead N namedRead ->
                                    PkgSig bundle P pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row boundaryRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row M ∨ hsame row Q ∨ hsame row I ∨
                                              hsame row R ∨ hsame row E ∨
                                                hsame row boundaryRead ∨
                                                  hsame row namedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧
                                              Cont comprehensionRead E boundaryRead ∧
                                                Cont boundaryRead H transportRead ∧
                                                  Cont transportRead C replayRead ∧
                                                    PkgSig bundle P pkg)
                                          hsame ∧
                                        UnaryHistory boundaryRead ∧
                                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields unaryM unaryQ unaryI unaryR unaryE unaryH unaryC unaryN membershipRoute
    subsetRoute comprehensionRoute boundaryRoute transportRoute replayRoute namedRoute
    packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have _membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed unaryM unaryQ membershipRoute
  have _subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed unaryQ unaryI subsetRoute
  have comprehensionUnary : UnaryHistory comprehensionRead :=
    unary_cont_closed unaryI unaryR comprehensionRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed comprehensionUnary unaryE boundaryRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed boundaryUnary unaryH transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary unaryC replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row boundaryRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont comprehensionRead E boundaryRead ∧
              Cont boundaryRead H transportRead ∧ Cont transportRead C replayRead ∧
                PkgSig bundle P pkg)
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, boundaryRoute, transportRoute, replayRoute, packageRead⟩
  }
  exact ⟨cert, boundaryUnary, namedUnary⟩

end BEDC.Derived.SetlikeUp
