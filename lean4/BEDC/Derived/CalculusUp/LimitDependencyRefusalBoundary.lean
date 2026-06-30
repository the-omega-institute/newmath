import BEDC.Derived.CalculusUp

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusLimitDependencyRefusalBoundary [AskSetup] [PackageSetup]
    {stream dyadic real limit derivative integral derivativeRead integralRead toleranceRead
      realRead endpointRead refusalRead provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory stream →
      UnaryHistory dyadic →
        UnaryHistory real →
          UnaryHistory limit →
            UnaryHistory derivative →
              UnaryHistory integral →
                Cont derivative integral endpointRead →
                  Cont stream dyadic toleranceRead →
                    Cont toleranceRead real realRead →
                      Cont endpointRead realRead refusalRead →
                        PkgSig bundle provenance pkg →
                          PkgSig bundle localName pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row stream ∨ hsame row dyadic ∨ hsame row real ∨
                                    hsame row limit ∨ hsame row endpointRead ∨
                                      hsame row toleranceRead ∨ hsame row realRead ∨
                                        hsame row refusalRead)
                                (fun row : BHist =>
                                  hsame row refusalRead ∧ Cont derivative integral endpointRead ∧
                                    Cont stream dyadic toleranceRead ∧
                                      Cont toleranceRead real realRead ∧
                                        Cont endpointRead realRead refusalRead ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle localName pkg)
                                hsame ∧
                              UnaryHistory endpointRead ∧ UnaryHistory toleranceRead ∧
                                UnaryHistory realRead ∧ UnaryHistory refusalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro streamUnary dyadicUnary realUnary _limitUnary derivativeUnary integralUnary
    endpointRoute toleranceRoute realRoute refusalRoute provenancePkg localNamePkg
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed derivativeUnary integralUnary endpointRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed streamUnary dyadicUnary toleranceRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed toleranceUnary realUnary realRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed endpointUnary realReadUnary refusalRoute
  have sourceRefusal :
      (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row) refusalRead :=
    ⟨hsame_refl refusalRead, refusalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row dyadic ∨ hsame row real ∨ hsame row limit ∨
              hsame row endpointRead ∨ hsame row toleranceRead ∨ hsame row realRead ∨
                hsame row refusalRead)
          (fun row : BHist =>
            hsame row refusalRead ∧ Cont derivative integral endpointRead ∧
              Cont stream dyadic toleranceRead ∧ Cont toleranceRead real realRead ∧
                Cont endpointRead realRead refusalRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceRefusal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, endpointRoute, toleranceRoute, realRoute, refusalRoute,
          provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, endpointUnary, toleranceUnary, realReadUnary, refusalUnary⟩

end BEDC.Derived.CalculusUp
