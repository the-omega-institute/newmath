import BEDC.Derived.RealUp.FiniteWindow
import BEDC.FKernel.Ask
import BEDC.FKernel.Package

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp
open BEDC.Derived.StreamNameUp

theorem RegseqratFiniteWindowSealExactness [AskSetup] [PackageSetup]
    {s t : BHist → BHist} {window : ProbeBundle BHist}
    {bundle : ProbeBundle ProbeName} {n dyadicRead streamRead realSeal : BHist} {pkg : Pkg} :
    RatStreamNameFiniteWindowClassifier s t window →
      InBundle n window →
        UnaryHistory n →
          Cont (s n) (t n) dyadicRead →
            Cont dyadicRead n streamRead →
              Cont streamRead n realSeal →
                PkgSig bundle realSeal pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row dyadicRead ∨ hsame row streamRead ∨ hsame row realSeal)
                      (fun row : BHist => PkgSig bundle realSeal pkg ∧ hsame row realSeal)
                      hsame ∧
                    UnaryHistory dyadicRead ∧ UnaryHistory streamRead ∧
                      UnaryHistory realSeal ∧ Cont (s n) (t n) dyadicRead ∧
                        Cont dyadicRead n streamRead ∧ Cont streamRead n realSeal ∧
                          PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro classified selected nUnary dyadicCont streamCont realSealCont realSealPkg
  have selectedClassifier : RatHistoryClassifier (s n) (t n) :=
    classified n selected nUnary
  have positives :
      PositiveUnaryDenominator (s n) ∧ PositiveUnaryDenominator (t n) :=
    RatHistoryClassifier_positive_denominators selectedClassifier
  have sourceUnary : UnaryHistory (s n) :=
    (PositiveUnaryDenominator_unary_and_nonempty positives.left).left
  have targetUnary : UnaryHistory (t n) :=
    (PositiveUnaryDenominator_unary_and_nonempty positives.right).left
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed sourceUnary targetUnary dyadicCont
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicUnary nUnary streamCont
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed streamUnary nUnary realSealCont
  have sourceAtSeal : hsame realSeal realSeal ∧ UnaryHistory realSeal :=
    ⟨hsame_refl realSeal, realSealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadicRead ∨ hsame row streamRead ∨ hsame row realSeal)
          (fun row : BHist => PkgSig bundle realSeal pkg ∧ hsame row realSeal)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal sourceAtSeal
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨realSealPkg, source.left⟩
  }
  exact
    ⟨cert, dyadicUnary, streamUnary, realSealUnary, dyadicCont, streamCont, realSealCont,
      realSealPkg⟩

end BEDC.Derived.RealUp
