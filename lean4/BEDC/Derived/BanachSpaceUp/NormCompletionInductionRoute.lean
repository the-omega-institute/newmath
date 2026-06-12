import BEDC.Derived.BanachSpaceUp.TasteGate
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

theorem BanachSpaceNormCompletionInductionRoute [AskSetup] [PackageSetup]
    {V N M Q S R E Z H C P L normMetric cauchyRead completionRead toleranceRead
      sealRead separatedRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BanachSpaceUp.mk V N M Q S R E Z H C P L =
        BanachSpaceUp.mk V N M Q S R E Z H C P L →
      UnaryHistory V →
        UnaryHistory N →
          UnaryHistory Q →
            UnaryHistory S →
              UnaryHistory R →
                UnaryHistory E →
                  UnaryHistory Z →
                    UnaryHistory H →
                      UnaryHistory C →
                        Cont V N normMetric →
                          Cont Q S cauchyRead →
                            Cont cauchyRead R completionRead →
                              Cont completionRead E toleranceRead →
                                Cont toleranceRead Z separatedRead →
                                  Cont H C localRead →
                                    PkgSig bundle P pkg →
                                      PkgSig bundle L pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row localRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row V ∨ hsame row N ∨ hsame row M ∨
                                                hsame row Q ∨ hsame row S ∨ hsame row R ∨
                                                  hsame row E ∨ hsame row Z ∨ hsame row H ∨
                                                    hsame row C ∨ hsame row P ∨ hsame row L ∨
                                                      hsame row localRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont V N normMetric ∧
                                                Cont Q S cauchyRead ∧
                                                  Cont cauchyRead R completionRead ∧
                                                    Cont completionRead E toleranceRead ∧
                                                      Cont toleranceRead Z separatedRead ∧
                                                        Cont H C localRead ∧
                                                          PkgSig bundle P pkg ∧
                                                            PkgSig bundle L pkg)
                                            hsame ∧
                                          UnaryHistory normMetric ∧ UnaryHistory cauchyRead ∧
                                            UnaryHistory completionRead ∧
                                              UnaryHistory toleranceRead ∧
                                                UnaryHistory separatedRead ∧
                                                  UnaryHistory localRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro _carrierRoute vUnary nUnary qUnary sUnary rUnary eUnary zUnary hUnary cUnary
    normRoute cauchyRoute completionRoute toleranceRoute separatedRoute localRoute
    provenancePkg localPkg
  have normUnary : UnaryHistory normMetric :=
    unary_cont_closed vUnary nUnary normRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed qUnary sUnary cauchyRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed cauchyUnary rUnary completionRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed completionUnary eUnary toleranceRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed toleranceUnary zUnary separatedRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed hUnary cUnary localRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row N ∨ hsame row M ∨ hsame row Q ∨ hsame row S ∨
              hsame row R ∨ hsame row E ∨ hsame row Z ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row L ∨ hsame row localRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont V N normMetric ∧ Cont Q S cauchyRead ∧
              Cont cauchyRead R completionRead ∧ Cont completionRead E toleranceRead ∧
                Cont toleranceRead Z separatedRead ∧ Cont H C localRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle L pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localRead ⟨hsame_refl localRead, localUnary⟩
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
        ⟨source.right, normRoute, cauchyRoute, completionRoute, toleranceRoute,
          separatedRoute, localRoute, provenancePkg, localPkg⟩
  }
  exact
    ⟨cert, normUnary, cauchyUnary, completionUnary, toleranceUnary, separatedUnary,
      localUnary⟩

end BEDC.Derived.BanachSpaceUp
