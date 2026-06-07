import BEDC.Derived.LawlessSequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LawlessSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LawlessSequenceBaireWindowStability [AskSetup] [PackageSetup]
    {S B R _H C P N prefixRead baireRead realRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory B →
        UnaryHistory R →
          UnaryHistory N →
            Cont S B prefixRead →
              Cont prefixRead B baireRead →
                Cont baireRead R realRead →
                  Cont realRead N namedRead →
                    PkgSig bundle P pkg →
                      PkgSig bundle N pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row S ∨ hsame row B ∨ hsame row R ∨
                                hsame row prefixRead ∨ hsame row baireRead ∨
                                  hsame row namedRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont S B prefixRead ∧
                                Cont prefixRead B baireRead ∧ Cont baireRead R realRead ∧
                                  Cont realRead N namedRead ∧ PkgSig bundle P pkg ∧
                                    PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory prefixRead ∧ UnaryHistory baireRead ∧
                            UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro sUnary bUnary rUnary nUnary prefixRoute baireRoute realRoute namedRoute
    provenancePkg namePkg
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sUnary bUnary prefixRoute
  have baireUnary : UnaryHistory baireRead :=
    unary_cont_closed prefixUnary bUnary baireRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed baireUnary rUnary realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row R ∨ hsame row prefixRead ∨
              hsame row baireRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S B prefixRead ∧ Cont prefixRead B baireRead ∧
              Cont baireRead R realRead ∧ Cont realRead N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, prefixRoute, baireRoute, realRoute, namedRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, prefixUnary, baireUnary, namedUnary⟩

end BEDC.Derived.LawlessSequenceUp
