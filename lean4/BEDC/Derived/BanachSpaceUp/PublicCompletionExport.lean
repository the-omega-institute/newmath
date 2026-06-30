import BEDC.Derived.BanachSpaceUp.CompleteMetricReduction
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BanachSpacePublicCompletionExport [AskSetup] [PackageSetup]
    {V N M Q S R E Z H C P L normMetric cauchyRead completionRead toleranceRead
      separatedRead transportRead replayRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory V →
      UnaryHistory N →
        UnaryHistory M →
          UnaryHistory Q →
            UnaryHistory S →
              UnaryHistory R →
                UnaryHistory E →
                  UnaryHistory Z →
                    UnaryHistory H →
                      UnaryHistory C →
                        UnaryHistory L →
                          Cont V N normMetric →
                            Cont Q S cauchyRead →
                              Cont cauchyRead R completionRead →
                                Cont completionRead E toleranceRead →
                                  Cont toleranceRead Z separatedRead →
                                    Cont separatedRead H transportRead →
                                      Cont transportRead C replayRead →
                                        Cont replayRead L publicRead →
                                          PkgSig bundle P pkg →
                                            PkgSig bundle publicRead pkg →
                                              BanachSpaceCompleteMetricReduction
                                                  V N M Q S R E Z ∧
                                                SemanticNameCert
                                                    (fun row : BHist =>
                                                      hsame row publicRead ∧
                                                        UnaryHistory row)
                                                    (fun row : BHist =>
                                                      hsame row V ∨ hsame row N ∨
                                                        hsame row M ∨ hsame row Q ∨
                                                          hsame row S ∨ hsame row R ∨
                                                            hsame row E ∨ hsame row Z ∨
                                                              hsame row H ∨ hsame row C ∨
                                                                hsame row L ∨
                                                                  hsame row publicRead)
                                                    (fun row : BHist =>
                                                      hsame row publicRead ∧
                                                        PkgSig bundle publicRead pkg ∧
                                                          BanachSpaceCompleteMetricReduction
                                                            V N M Q S R E Z)
                                                    hsame ∧
                                                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro vUnary nUnary mUnary qUnary sUnary rUnary eUnary zUnary hUnary cUnary lUnary
    normRoute cauchyRoute completionRoute toleranceRoute separatedRoute transportRoute
    replayRoute publicRoute _provenancePkg publicPkg
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed qUnary sUnary cauchyRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed cauchyUnary rUnary completionRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed completionUnary eUnary toleranceRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed toleranceUnary zUnary separatedRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed separatedUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed replayUnary lUnary publicRoute
  have reduction : BanachSpaceCompleteMetricReduction V N M Q S R E Z := by
    exact
      ⟨vUnary, nUnary, mUnary, qUnary, sUnary, rUnary, eUnary, zUnary, normMetric,
        cauchyRead, completionRead, toleranceRead, separatedRead, normRoute, cauchyRoute,
        completionRoute, toleranceRoute, separatedRoute⟩
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row N ∨ hsame row M ∨ hsame row Q ∨ hsame row S ∨
              hsame row R ∨ hsame row E ∨ hsame row Z ∨ hsame row H ∨ hsame row C ∨
                hsame row L ∨ hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ PkgSig bundle publicRead pkg ∧
              BanachSpaceCompleteMetricReduction V N M Q S R E Z)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro publicRead sourcePublic
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
        exact ⟨source.left, publicPkg, reduction⟩
    }
  exact ⟨reduction, cert, publicUnary⟩

end BEDC.Derived.BanachSpaceUp
