import BEDC.Derived.CalculusUp.RiemannIntegralDependencyRoute

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusFiniteLimitSealRoute [AskSetup] [PackageSetup]
    {derivativeRow integralRow regSeqRow finiteLimitSeal realRow derivativeRead integralRead
      sharedRead sealRead endpointRead provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory derivativeRow →
      UnaryHistory integralRow →
        UnaryHistory regSeqRow →
          UnaryHistory finiteLimitSeal →
            UnaryHistory realRow →
              Cont derivativeRow regSeqRow derivativeRead →
                Cont integralRow regSeqRow integralRead →
                  Cont derivativeRead integralRead sharedRead →
                    Cont sharedRead finiteLimitSeal sealRead →
                      Cont sealRead realRow endpointRead →
                        PkgSig bundle provenance pkg →
                          PkgSig bundle localName pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row derivativeRow ∨ hsame row integralRow ∨
                                    hsame row regSeqRow ∨ hsame row finiteLimitSeal ∨
                                      hsame row realRow ∨ hsame row endpointRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧
                                    Cont derivativeRead integralRead sharedRead ∧
                                      Cont sharedRead finiteLimitSeal sealRead ∧
                                        Cont sealRead realRow endpointRead ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle localName pkg)
                                hsame ∧
                              UnaryHistory derivativeRead ∧ UnaryHistory integralRead ∧
                                UnaryHistory sharedRead ∧ UnaryHistory sealRead ∧
                                  UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro derivativeUnary integralUnary regSeqUnary finiteSealUnary realUnary derivativeRoute
    integralRoute sharedRoute sealRoute endpointRoute provenancePkg localNamePkg
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed derivativeUnary regSeqUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed integralUnary regSeqUnary integralRoute
  have sharedReadUnary : UnaryHistory sharedRead :=
    unary_cont_closed derivativeReadUnary integralReadUnary sharedRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sharedReadUnary finiteSealUnary sealRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed sealReadUnary realUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row derivativeRow ∨ hsame row integralRow ∨ hsame row regSeqRow ∨
              hsame row finiteLimitSeal ∨ hsame row realRow ∨ hsame row endpointRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont derivativeRead integralRead sharedRead ∧
              Cont sharedRead finiteLimitSeal sealRead ∧ Cont sealRead realRow endpointRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpointRead ⟨hsame_refl endpointRead, endpointReadUnary⟩
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
      exact ⟨source.right, sharedRoute, sealRoute, endpointRoute, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, derivativeReadUnary, integralReadUnary, sharedReadUnary, sealReadUnary,
      endpointReadUnary⟩

end BEDC.Derived.CalculusUp
