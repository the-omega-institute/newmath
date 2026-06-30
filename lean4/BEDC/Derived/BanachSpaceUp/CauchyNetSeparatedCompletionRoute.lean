import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BanachSpaceCauchyNetSeparatedCompletionRoute [AskSetup] [PackageSetup]
    {V N M Q S R E Z H C P L cauchyRead completionRead toleranceRead realSeal
      separatedRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory Q →
      UnaryHistory S →
        UnaryHistory R →
          UnaryHistory E →
            UnaryHistory Z →
              UnaryHistory H →
                UnaryHistory C →
                  Cont Q S cauchyRead →
                    Cont cauchyRead R completionRead →
                      Cont completionRead E toleranceRead →
                        Cont toleranceRead Z separatedRead →
                          Cont H C localRead →
                            PkgSig bundle P pkg →
                              PkgSig bundle L pkg →
                                SemanticNameCert
                                    (fun row : BHist => hsame row separatedRead ∧
                                      UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row Q ∨ hsame row S ∨ hsame row R ∨
                                        hsame row E ∨ hsame row Z ∨ hsame row H ∨
                                          hsame row C ∨ hsame row P ∨ hsame row L ∨
                                            hsame row separatedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont Q S cauchyRead ∧
                                        Cont cauchyRead R completionRead ∧
                                          Cont completionRead E toleranceRead ∧
                                            Cont toleranceRead Z separatedRead ∧
                                              PkgSig bundle P pkg ∧ PkgSig bundle L pkg)
                                    hsame ∧
                                  UnaryHistory cauchyRead ∧
                                    UnaryHistory completionRead ∧
                                      UnaryHistory toleranceRead ∧
                                        UnaryHistory separatedRead ∧
                                          UnaryHistory localRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro unaryQ unaryS unaryR unaryE unaryZ unaryH unaryC
  intro cauchyRoute completionRoute toleranceRoute separatedRoute localRoute
  intro provenancePkg localNamePkg
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed unaryQ unaryS cauchyRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed cauchyUnary unaryR completionRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed completionUnary unaryE toleranceRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed toleranceUnary unaryZ separatedRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed unaryH unaryC localRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row Z ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row L ∨
                hsame row separatedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q S cauchyRead ∧
              Cont cauchyRead R completionRead ∧ Cont completionRead E toleranceRead ∧
                Cont toleranceRead Z separatedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle L pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro separatedRead ⟨hsame_refl separatedRead,
        separatedUnary⟩
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, cauchyRoute, completionRoute, toleranceRoute, separatedRoute,
          provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, cauchyUnary, completionUnary, toleranceUnary, separatedUnary, localUnary⟩

end BEDC.Derived.BanachSpaceUp
