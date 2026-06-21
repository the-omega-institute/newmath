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

theorem SetlikeExtensionalBoundaryRoute [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N boundaryPrefix extensionalRead transportRead replayRead
      provenanceRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] →
      UnaryHistory M →
        UnaryHistory Q →
          UnaryHistory I →
            UnaryHistory R →
              UnaryHistory E →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory P →
                      UnaryHistory N →
                        Cont M Q boundaryPrefix →
                          Cont boundaryPrefix I extensionalRead →
                            Cont extensionalRead R transportRead →
                              Cont transportRead E replayRead →
                                Cont replayRead H provenanceRead →
                                  Cont provenanceRead N namedRead →
                                    PkgSig bundle P pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row namedRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row M ∨ hsame row Q ∨ hsame row I ∨
                                              hsame row R ∨ hsame row E ∨ hsame row H ∨
                                                hsame row N ∨ hsame row boundaryPrefix ∨
                                                  hsame row extensionalRead ∨
                                                    hsame row transportRead ∨
                                                      hsame row replayRead ∨
                                                        hsame row provenanceRead ∨
                                                          hsame row namedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont M Q boundaryPrefix ∧
                                              Cont boundaryPrefix I extensionalRead ∧
                                                Cont extensionalRead R transportRead ∧
                                                  Cont transportRead E replayRead ∧
                                                    Cont replayRead H provenanceRead ∧
                                                      Cont provenanceRead N namedRead ∧
                                                        PkgSig bundle P pkg)
                                          hsame ∧
                                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro _fields mUnary qUnary iUnary rUnary eUnary hUnary _cUnary _pUnary nUnary
    boundaryRoute extensionalRoute transportRoute replayRoute provenanceRoute namedRoute
    provenancePkg
  have boundaryUnary : UnaryHistory boundaryPrefix :=
    unary_cont_closed mUnary qUnary boundaryRoute
  have extensionalUnary : UnaryHistory extensionalRead :=
    unary_cont_closed boundaryUnary iUnary extensionalRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed extensionalUnary rUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary eUnary replayRoute
  have provenanceUnary : UnaryHistory provenanceRead :=
    unary_cont_closed replayUnary hUnary provenanceRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed provenanceUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row R ∨ hsame row E ∨
              hsame row H ∨ hsame row N ∨ hsame row boundaryPrefix ∨
                hsame row extensionalRead ∨ hsame row transportRead ∨
                  hsame row replayRead ∨ hsame row provenanceRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q boundaryPrefix ∧
              Cont boundaryPrefix I extensionalRead ∧ Cont extensionalRead R transportRead ∧
                Cont transportRead E replayRead ∧ Cont replayRead H provenanceRead ∧
                  Cont provenanceRead N namedRead ∧ PkgSig bundle P pkg)
          hsame := by
    exact {
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
                              (Or.inr (Or.inr source.left)))))))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, boundaryRoute, extensionalRoute, transportRoute, replayRoute,
            provenanceRoute, namedRoute, provenancePkg⟩
    }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.SetlikeUp
