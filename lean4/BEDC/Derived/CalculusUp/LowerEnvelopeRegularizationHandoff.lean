import BEDC.Derived.CalculusUp

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusLowerEnvelopeRegularizationHandoff [AskSetup] [PackageSetup]
    {lowerSemi epigraph regSeq dyadic real lowerRead rationalRead dyadicRead realRead
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory lowerSemi ->
      UnaryHistory epigraph ->
        UnaryHistory regSeq ->
          UnaryHistory dyadic ->
            UnaryHistory real ->
              Cont lowerSemi epigraph lowerRead ->
                Cont lowerRead regSeq rationalRead ->
                  Cont rationalRead dyadic dyadicRead ->
                    Cont dyadicRead real realRead ->
                      PkgSig bundle provenance pkg ->
                        PkgSig bundle localName pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row lowerSemi ∨ hsame row epigraph ∨
                                  hsame row regSeq ∨ hsame row dyadic ∨ hsame row real ∨
                                    hsame row lowerRead ∨ hsame row rationalRead ∨
                                      hsame row dyadicRead ∨ hsame row realRead ∨
                                        hsame row provenance ∨ hsame row localName)
                              (fun row : BHist =>
                                UnaryHistory row ∧
                                  Cont lowerSemi epigraph lowerRead ∧
                                    Cont lowerRead regSeq rationalRead ∧
                                      Cont rationalRead dyadic dyadicRead ∧
                                        Cont dyadicRead real realRead ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle localName pkg)
                              hsame ∧ UnaryHistory lowerRead ∧ UnaryHistory rationalRead ∧
                            UnaryHistory dyadicRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro lowerSemiUnary epigraphUnary regSeqUnary dyadicUnary realUnary lowerRoute
    rationalRoute dyadicRoute realRoute provenancePkg localNamePkg
  have lowerReadUnary : UnaryHistory lowerRead :=
    unary_cont_closed lowerSemiUnary epigraphUnary lowerRoute
  have rationalReadUnary : UnaryHistory rationalRead :=
    unary_cont_closed lowerReadUnary regSeqUnary rationalRoute
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed rationalReadUnary dyadicUnary dyadicRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed dyadicReadUnary realUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lowerSemi ∨ hsame row epigraph ∨ hsame row regSeq ∨
              hsame row dyadic ∨ hsame row real ∨ hsame row lowerRead ∨
                hsame row rationalRead ∨ hsame row dyadicRead ∨ hsame row realRead ∨
                  hsame row provenance ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont lowerSemi epigraph lowerRead ∧
              Cont lowerRead regSeq rationalRead ∧ Cont rationalRead dyadic dyadicRead ∧
                Cont dyadicRead real realRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
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
                          (Or.inl source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, lowerRoute, rationalRoute, dyadicRoute, realRoute,
          provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, lowerReadUnary, rationalReadUnary, dyadicReadUnary, realReadUnary⟩

end BEDC.Derived.CalculusUp
