import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorFunctorialRootObligation [AskSetup] [PackageSetup]
    {U1 F1 E1 R1 W1 D1 S1 H1 C1 P1 N1 U2 F2 E2 R2 W2 D2 S2 H2 C2 P2 N2
      source1 extension1 seal1 source2 extension2 seal2 compositeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U1 F1 E1 R1 W1 D1 S1 H1 C1 P1 N1 bundle pkg ->
      UniformCompletionFunctorCarrier U2 F2 E2 R2 W2 D2 S2 H2 C2 P2 N2 bundle pkg ->
        Cont U1 F1 source1 ->
          Cont source1 E1 extension1 ->
            Cont extension1 S1 seal1 ->
              Cont U2 F2 source2 ->
                Cont source2 E2 extension2 ->
                  Cont extension2 S2 seal2 ->
                    Cont seal1 seal2 compositeRead ->
                      PkgSig bundle compositeRead pkg ->
                        SemanticNameCert
                            (fun row : BHist =>
                              hsame row compositeRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row U1 ∨ hsame row F1 ∨ hsame row E1 ∨
                                hsame row U2 ∨ hsame row F2 ∨ hsame row E2 ∨
                                  hsame row compositeRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont U1 F1 source1 ∧
                                Cont source1 E1 extension1 ∧
                                  Cont U2 F2 source2 ∧
                                    Cont source2 E2 extension2 ∧
                                      Cont seal1 seal2 compositeRead ∧
                                        PkgSig bundle compositeRead pkg)
                            hsame ∧
                          UnaryHistory source1 ∧ UnaryHistory extension1 ∧
                            UnaryHistory seal1 ∧ UnaryHistory source2 ∧
                              UnaryHistory extension2 ∧ UnaryHistory seal2 ∧
                                UnaryHistory compositeRead := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier1 carrier2 sourceRoute1 extensionRoute1 sealRoute1 sourceRoute2
    extensionRoute2 sealRoute2 compositeRoute compositePkg
  obtain ⟨unaryU1, unaryF1, unaryE1, _unaryR1, _unaryW1, _unaryD1, unaryS1,
    _unaryH1, _unaryC1, _unaryP1, _unaryN1, _carrierSourceRoute1,
      _carrierReadbackRoute1, _carrierSealRoute1, _provenancePkg1,
        _localNamePkg1⟩ := carrier1
  obtain ⟨unaryU2, unaryF2, unaryE2, _unaryR2, _unaryW2, _unaryD2, unaryS2,
    _unaryH2, _unaryC2, _unaryP2, _unaryN2, _carrierSourceRoute2,
      _carrierReadbackRoute2, _carrierSealRoute2, _provenancePkg2,
        _localNamePkg2⟩ := carrier2
  have sourceUnary1 : UnaryHistory source1 :=
    unary_cont_closed unaryU1 unaryF1 sourceRoute1
  have extensionUnary1 : UnaryHistory extension1 :=
    unary_cont_closed sourceUnary1 unaryE1 extensionRoute1
  have sealUnary1 : UnaryHistory seal1 :=
    unary_cont_closed extensionUnary1 unaryS1 sealRoute1
  have sourceUnary2 : UnaryHistory source2 :=
    unary_cont_closed unaryU2 unaryF2 sourceRoute2
  have extensionUnary2 : UnaryHistory extension2 :=
    unary_cont_closed sourceUnary2 unaryE2 extensionRoute2
  have sealUnary2 : UnaryHistory seal2 :=
    unary_cont_closed extensionUnary2 unaryS2 sealRoute2
  have compositeUnary : UnaryHistory compositeRead :=
    unary_cont_closed sealUnary1 sealUnary2 compositeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compositeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U1 ∨ hsame row F1 ∨ hsame row E1 ∨ hsame row U2 ∨
              hsame row F2 ∨ hsame row E2 ∨ hsame row compositeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U1 F1 source1 ∧ Cont source1 E1 extension1 ∧
              Cont U2 F2 source2 ∧ Cont source2 E2 extension2 ∧
                Cont seal1 seal2 compositeRead ∧ PkgSig bundle compositeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro compositeRead ⟨hsame_refl compositeRead, compositeUnary⟩
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute1, extensionRoute1, sourceRoute2, extensionRoute2,
          compositeRoute, compositePkg⟩
  }
  exact
    ⟨cert, sourceUnary1, extensionUnary1, sealUnary1, sourceUnary2, extensionUnary2,
      sealUnary2, compositeUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
