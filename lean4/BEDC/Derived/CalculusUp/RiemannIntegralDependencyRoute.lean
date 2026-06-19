import BEDC.Derived.CalculusUp

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRiemannIntegralDependencyRoute [AskSetup] [PackageSetup]
    {derivativeRow integralRow regSeqRow realRow derivativeRead integralRead sharedRead
      routeRead provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory derivativeRow →
      UnaryHistory integralRow →
        UnaryHistory regSeqRow →
          UnaryHistory realRow →
            Cont derivativeRow regSeqRow derivativeRead →
              Cont integralRow regSeqRow integralRead →
                Cont derivativeRead integralRead sharedRead →
                  Cont sharedRead realRow routeRead →
                    PkgSig bundle provenance pkg →
                      PkgSig bundle localName pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row derivativeRow ∨ hsame row integralRow ∨
                                hsame row regSeqRow ∨ hsame row realRow ∨
                                  hsame row routeRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont derivativeRead integralRead sharedRead ∧
                                Cont sharedRead realRow routeRead ∧
                                  PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                            hsame ∧
                          UnaryHistory derivativeRead ∧ UnaryHistory integralRead ∧
                            UnaryHistory sharedRead ∧ UnaryHistory routeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro derivativeUnary integralUnary regSeqUnary realUnary derivativeRoute integralRoute
    sharedRoute routeRoute provenancePkg localNamePkg
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed derivativeUnary regSeqUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed integralUnary regSeqUnary integralRoute
  have sharedReadUnary : UnaryHistory sharedRead :=
    unary_cont_closed derivativeReadUnary integralReadUnary sharedRoute
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed sharedReadUnary realUnary routeRoute
  have sourceAtRoute : hsame routeRead routeRead ∧ UnaryHistory routeRead :=
    ⟨hsame_refl routeRead, routeReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row derivativeRow ∨ hsame row integralRow ∨ hsame row regSeqRow ∨
              hsame row realRow ∨ hsame row routeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont derivativeRead integralRead sharedRead ∧
              Cont sharedRead realRow routeRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead sourceAtRoute
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
      exact ⟨source.right, sharedRoute, routeRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, derivativeReadUnary, integralReadUnary, sharedReadUnary, routeReadUnary⟩

theorem CalculusRiemannIntegralRootCarrierDependencyRoute [AskSetup] [PackageSetup]
    {real limit continuous derivative integral readback transport replay provenance localName
      derivativeRead integralRead sharedRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CalculusRootDerivativeIntegralCarrier real limit continuous derivative integral readback
        transport replay provenance localName bundle pkg →
      Cont continuous derivative derivativeRead →
        Cont integral readback integralRead →
          Cont derivativeRead integralRead sharedRead →
            Cont sharedRead real routeRead →
              PkgSig bundle routeRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row derivativeRead ∨ hsame row integralRead ∨
                        hsame row sharedRead ∨ hsame row real ∨ hsame row routeRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont derivativeRead integralRead sharedRead ∧
                        Cont sharedRead real routeRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle routeRead pkg)
                    hsame ∧
                  UnaryHistory sharedRead ∧ UnaryHistory routeRead := by
  -- BEDC touchpoint anchor: CalculusRootDerivativeIntegralCarrier SemanticNameCert
  intro carrier derivativeRoute integralRoute sharedRoute routeRoute routePkg
  have admitted :=
    CalculusRootDerivativeIntegralCarrier_admission carrier derivativeRoute integralRoute
  obtain ⟨_rootCert, derivativeReadUnary, integralReadUnary⟩ := admitted
  obtain ⟨realUnary, _limitUnary, _continuousUnary, _derivativeUnary, _integralUnary,
    _readbackUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _realLimitRoute, _continuousDerivativeRoute, _derivativeTransportRoute,
    _transportReplayRoute, provenancePkg⟩ := carrier
  have sharedReadUnary : UnaryHistory sharedRead :=
    unary_cont_closed derivativeReadUnary integralReadUnary sharedRoute
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed sharedReadUnary realUnary routeRoute
  have sourceAtRoute : hsame routeRead routeRead ∧ UnaryHistory routeRead :=
    ⟨hsame_refl routeRead, routeReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row derivativeRead ∨ hsame row integralRead ∨ hsame row sharedRead ∨
              hsame row real ∨ hsame row routeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont derivativeRead integralRead sharedRead ∧
              Cont sharedRead real routeRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle routeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead sourceAtRoute
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
      exact ⟨source.right, sharedRoute, routeRoute, provenancePkg, routePkg⟩
  }
  exact ⟨cert, sharedReadUnary, routeReadUnary⟩

end BEDC.Derived.CalculusUp
