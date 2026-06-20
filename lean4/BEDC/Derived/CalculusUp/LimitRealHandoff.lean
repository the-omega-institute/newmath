import BEDC.Derived.CalculusUp

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusLimitRealHandoff [AskSetup] [PackageSetup]
    {stream regSeq real limit derivative integral derivativeRead integralRead sharedRead
      realRead limitRead provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory stream →
      UnaryHistory regSeq →
        UnaryHistory real →
          UnaryHistory limit →
            UnaryHistory derivative →
              UnaryHistory integral →
                Cont derivative regSeq derivativeRead →
                  Cont integral regSeq integralRead →
                    Cont derivativeRead integralRead sharedRead →
                      Cont sharedRead real realRead →
                        Cont realRead limit limitRead →
                          PkgSig bundle provenance pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row limitRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row stream ∨ hsame row regSeq ∨ hsame row real ∨
                                    hsame row limit ∨ hsame row limitRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧
                                    Cont derivative regSeq derivativeRead ∧
                                      Cont integral regSeq integralRead ∧
                                        Cont derivativeRead integralRead sharedRead ∧
                                          Cont sharedRead real realRead ∧
                                            Cont realRead limit limitRead ∧
                                              PkgSig bundle provenance pkg)
                                hsame ∧
                              UnaryHistory sharedRead ∧ UnaryHistory realRead ∧
                                UnaryHistory limitRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro streamUnary regSeqUnary realUnary limitUnary derivativeUnary integralUnary
    derivativeRoute integralRoute sharedRoute realRoute limitRoute provenancePkg
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed derivativeUnary regSeqUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed integralUnary regSeqUnary integralRoute
  have sharedReadUnary : UnaryHistory sharedRead :=
    unary_cont_closed derivativeReadUnary integralReadUnary sharedRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed sharedReadUnary realUnary realRoute
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed realReadUnary limitUnary limitRoute
  have sourceAtLimit :
      (fun row : BHist => hsame row limitRead ∧ UnaryHistory row) limitRead := by
    exact ⟨hsame_refl limitRead, limitReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row limitRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row regSeq ∨ hsame row real ∨ hsame row limit ∨
              hsame row limitRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont derivative regSeq derivativeRead ∧
              Cont integral regSeq integralRead ∧ Cont derivativeRead integralRead sharedRead ∧
                Cont sharedRead real realRead ∧ Cont realRead limit limitRead ∧
                  PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro limitRead sourceAtLimit
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
      exact
        ⟨source.right, derivativeRoute, integralRoute, sharedRoute, realRoute,
          limitRoute, provenancePkg⟩
  }
  exact ⟨cert, sharedReadUnary, realReadUnary, limitReadUnary⟩

end BEDC.Derived.CalculusUp
