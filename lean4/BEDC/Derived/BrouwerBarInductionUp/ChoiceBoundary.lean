import BEDC.Derived.BrouwerBarInductionUp.PrefixStability
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.BrouwerBarInductionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BrouwerBarInductionChoiceBoundary [AskSetup] [PackageSetup]
    {T B M I W R E H C P N prefixRead streamRead regseqRead realRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory B →
        UnaryHistory M →
          UnaryHistory I →
            UnaryHistory W →
              UnaryHistory R →
                UnaryHistory E →
                  UnaryHistory N →
                    Cont T B prefixRead →
                      Cont prefixRead I streamRead →
                        Cont streamRead W regseqRead →
                          Cont regseqRead R realRead →
                            Cont realRead E localRead →
                              PkgSig bundle localRead pkg →
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row localRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row T ∨ hsame row B ∨ hsame row M ∨
                                        hsame row I ∨ hsame row W ∨ hsame row R ∨
                                          hsame row E ∨ hsame row localRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ PkgSig bundle localRead pkg)
                                    hsame ∧
                                  UnaryHistory localRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro tUnary bUnary _mUnary iUnary wUnary rUnary eUnary _nUnary prefixRoute streamRoute
    regseqRoute realRoute localRoute localPkg
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed tUnary bUnary prefixRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed prefixUnary iUnary streamRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamUnary wUnary regseqRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary rUnary realRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed realUnary eUnary localRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row B ∨ hsame row M ∨ hsame row I ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row localRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle localRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro localRead ⟨hsame_refl localRead, localUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same source
        have otherSame : hsame other localRead :=
          hsame_trans (hsame_symm same) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right same
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localPkg⟩
  }
  exact ⟨cert, localUnary⟩

end BEDC.Derived.BrouwerBarInductionUp
