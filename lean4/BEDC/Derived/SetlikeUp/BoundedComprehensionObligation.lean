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

theorem SetlikeBoundedComprehensionObligation [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N membershipRead subsetRead boundedFamilyRead comprehensionRead
      transportRead replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ->
      UnaryHistory M ->
        UnaryHistory Q ->
          UnaryHistory I ->
            UnaryHistory R ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory N ->
                    Cont M Q membershipRead ->
                      Cont Q I subsetRead ->
                        Cont membershipRead subsetRead boundedFamilyRead ->
                          Cont boundedFamilyRead R comprehensionRead ->
                            Cont comprehensionRead H transportRead ->
                              Cont transportRead C replayRead ->
                                Cont replayRead N namedRead ->
                                  PkgSig bundle P pkg ->
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row namedRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row M ∨ hsame row Q ∨ hsame row I ∨
                                            hsame row R ∨ hsame row H ∨ hsame row C ∨
                                              hsame row N ∨ hsame row membershipRead ∨
                                                hsame row subsetRead ∨
                                                  hsame row boundedFamilyRead ∨
                                                    hsame row comprehensionRead ∨
                                                      hsame row namedRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont M Q membershipRead ∧
                                            Cont Q I subsetRead ∧
                                              Cont membershipRead subsetRead boundedFamilyRead ∧
                                                Cont boundedFamilyRead R comprehensionRead ∧
                                                  Cont comprehensionRead H transportRead ∧
                                                    Cont transportRead C replayRead ∧
                                                      Cont replayRead N namedRead ∧
                                                        PkgSig bundle P pkg)
                                        hsame ∧
                                      UnaryHistory boundedFamilyRead ∧
                                        UnaryHistory comprehensionRead ∧
                                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields unaryM unaryQ unaryI unaryR unaryH unaryC unaryN membershipRoute subsetRoute
    boundedFamilyRoute comprehensionRoute transportRoute replayRoute namedRoute packageRead
  have _acceptedFields : setlikeFields S = [M, Q, I, R, E, H, C, P, N] := fields
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed unaryM unaryQ membershipRoute
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed unaryQ unaryI subsetRoute
  have boundedFamilyUnary : UnaryHistory boundedFamilyRead :=
    unary_cont_closed membershipUnary subsetUnary boundedFamilyRoute
  have comprehensionUnary : UnaryHistory comprehensionRead :=
    unary_cont_closed boundedFamilyUnary unaryR comprehensionRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed comprehensionUnary unaryH transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary unaryC replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row H ∨
              hsame row C ∨ hsame row N ∨ hsame row membershipRead ∨
                hsame row subsetRead ∨ hsame row boundedFamilyRead ∨
                  hsame row comprehensionRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q membershipRead ∧ Cont Q I subsetRead ∧
              Cont membershipRead subsetRead boundedFamilyRead ∧
                Cont boundedFamilyRead R comprehensionRead ∧
                  Cont comprehensionRead H transportRead ∧
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
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, membershipRoute, subsetRoute, boundedFamilyRoute,
          comprehensionRoute, transportRoute, replayRoute, namedRoute, packageRead⟩
  }
  exact ⟨cert, boundedFamilyUnary, comprehensionUnary, namedUnary⟩

end BEDC.Derived.SetlikeUp
