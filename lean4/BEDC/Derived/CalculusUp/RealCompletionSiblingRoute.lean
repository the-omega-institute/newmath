import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRealCompletionSiblingRoute [AskSetup] [PackageSetup]
    {derivative integral limit real regSeq stream dyadic name derivativeRead integralRead
      limitRead realRead regSeqRead streamRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory derivative →
      UnaryHistory integral →
        UnaryHistory limit →
          UnaryHistory real →
            UnaryHistory regSeq →
              UnaryHistory stream →
                UnaryHistory dyadic →
                  UnaryHistory name →
                    Cont derivative real derivativeRead →
                      Cont integral regSeq integralRead →
                        Cont limit stream limitRead →
                          Cont derivativeRead dyadic realRead →
                            Cont integralRead regSeq regSeqRead →
                              Cont limitRead stream streamRead →
                                Cont realRead name publicRead →
                                  PkgSig bundle publicRead pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row publicRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row derivativeRead ∨ hsame row realRead ∨
                                            hsame row regSeqRead ∨ hsame row streamRead ∨
                                              hsame row publicRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧
                                            Cont derivative real derivativeRead ∧
                                              Cont integral regSeq integralRead ∧
                                                Cont limit stream limitRead ∧
                                                  Cont realRead name publicRead ∧
                                                    PkgSig bundle publicRead pkg)
                                        hsame ∧
                                      UnaryHistory derivativeRead ∧
                                        UnaryHistory integralRead ∧ UnaryHistory limitRead ∧
                                          UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro derivativeUnary integralUnary limitUnary realUnary regSeqUnary streamUnary dyadicUnary
    nameUnary derivativeRoute integralRoute limitRoute realRoute regSeqRoute streamRoute
    publicRoute publicPkg
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed derivativeUnary realUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed integralUnary regSeqUnary integralRoute
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed limitUnary streamUnary limitRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed derivativeReadUnary dyadicUnary realRoute
  have _regSeqReadUnary : UnaryHistory regSeqRead :=
    unary_cont_closed integralReadUnary regSeqUnary regSeqRoute
  have _streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed limitReadUnary streamUnary streamRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed realReadUnary nameUnary publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row derivativeRead ∨ hsame row realRead ∨ hsame row regSeqRead ∨
              hsame row streamRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont derivative real derivativeRead ∧
              Cont integral regSeq integralRead ∧ Cont limit stream limitRead ∧
                Cont realRead name publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, derivativeRoute, integralRoute, limitRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, derivativeReadUnary, integralReadUnary, limitReadUnary, publicReadUnary⟩

end BEDC.Derived.CalculusUp
