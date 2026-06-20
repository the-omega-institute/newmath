import BEDC.Derived.CalculusUp

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusLimitRealDerivativeReadback [AskSetup] [PackageSetup]
    {derivativeRow regSeqRow realRow streamRow dyadicRow derivativeRead scheduleRead
      rationalRead dyadicRead realRead provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory derivativeRow →
      UnaryHistory regSeqRow →
        UnaryHistory realRow →
          UnaryHistory streamRow →
            UnaryHistory dyadicRow →
              Cont derivativeRow streamRow derivativeRead →
                Cont streamRow regSeqRow scheduleRead →
                  Cont scheduleRead dyadicRow rationalRead →
                    Cont rationalRead dyadicRow dyadicRead →
                      Cont dyadicRead realRow realRead →
                        PkgSig bundle provenance pkg →
                          PkgSig bundle localName pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row derivativeRead ∨ hsame row scheduleRead ∨
                                    hsame row rationalRead ∨ hsame row dyadicRead ∨
                                      hsame row realRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont dyadicRead realRow realRead ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle localName pkg)
                                hsame ∧
                              UnaryHistory derivativeRead ∧ UnaryHistory scheduleRead ∧
                                UnaryHistory rationalRead ∧ UnaryHistory dyadicRead ∧
                                  UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro derivativeUnary regSeqUnary realUnary streamUnary dyadicUnary derivativeRoute
    scheduleRoute rationalRoute dyadicRoute realRoute provenancePkg localNamePkg
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed derivativeUnary streamUnary derivativeRoute
  have scheduleReadUnary : UnaryHistory scheduleRead :=
    unary_cont_closed streamUnary regSeqUnary scheduleRoute
  have rationalReadUnary : UnaryHistory rationalRead :=
    unary_cont_closed scheduleReadUnary dyadicUnary rationalRoute
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed rationalReadUnary dyadicUnary dyadicRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed dyadicReadUnary realUnary realRoute
  have sourceReal :
      (fun row : BHist => hsame row realRead ∧ UnaryHistory row) realRead := by
    exact ⟨hsame_refl realRead, realReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row derivativeRead ∨ hsame row scheduleRead ∨
              hsame row rationalRead ∨ hsame row dyadicRead ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont dyadicRead realRow realRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead sourceReal
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
      exact ⟨source.right, realRoute, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, derivativeReadUnary, scheduleReadUnary, rationalReadUnary, dyadicReadUnary,
      realReadUnary⟩

end BEDC.Derived.CalculusUp
