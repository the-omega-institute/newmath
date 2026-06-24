import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive FiniteCauchyTailHandoffUp : Type where
  | mk
      (regSeqRat streamName dyadicRatCore cauchyModulus tailSelector realSeal transport
        continuation provenance localNameCert : BHist) :
      FiniteCauchyTailHandoffUp
  deriving DecidableEq

namespace FiniteCauchyTailHandoffUp

theorem FiniteCauchyTailHandoffRealSealRoute [AskSetup] [PackageSetup]
    {R W D M S Z H K P N windowRead budgetRead modulusRead selectorRead realSealRead
      transportRead replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R ->
      UnaryHistory W ->
        UnaryHistory D ->
          UnaryHistory M ->
            UnaryHistory S ->
              UnaryHistory Z ->
                UnaryHistory H ->
                  UnaryHistory K ->
                    UnaryHistory N ->
                      Cont R W windowRead ->
                        Cont windowRead D budgetRead ->
                          Cont budgetRead M modulusRead ->
                            Cont modulusRead S selectorRead ->
                              Cont selectorRead Z realSealRead ->
                                Cont realSealRead H transportRead ->
                                  Cont transportRead K replayRead ->
                                    Cont replayRead N namedRead ->
                                      PkgSig bundle P pkg ->
                                        PkgSig bundle namedRead pkg ->
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row namedRead ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row R ∨ hsame row W ∨
                                                  hsame row D ∨ hsame row M ∨
                                                    hsame row S ∨ hsame row Z ∨
                                                      hsame row H ∨ hsame row K ∨
                                                        hsame row P ∨ hsame row N ∨
                                                          hsame row namedRead)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧
                                                  Cont R W windowRead ∧
                                                    Cont windowRead D budgetRead ∧
                                                      Cont budgetRead M modulusRead ∧
                                                        Cont modulusRead S selectorRead ∧
                                                          Cont selectorRead Z
                                                              realSealRead ∧
                                                            Cont realSealRead H
                                                                transportRead ∧
                                                              Cont transportRead K
                                                                  replayRead ∧
                                                                Cont replayRead N
                                                                    namedRead ∧
                                                                  PkgSig bundle namedRead
                                                                    pkg)
                                              hsame ∧
                                            UnaryHistory windowRead ∧
                                              UnaryHistory budgetRead ∧
                                                UnaryHistory modulusRead ∧
                                                  UnaryHistory selectorRead ∧
                                                    UnaryHistory realSealRead ∧
                                                      UnaryHistory transportRead ∧
                                                        UnaryHistory replayRead ∧
                                                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro unaryR unaryW unaryD unaryM unaryS unaryZ unaryH unaryK unaryN windowRoute
    budgetRoute modulusRoute selectorRoute realSealRoute transportRoute replayRoute namedRoute
    _provenancePkg namedPkg
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryR unaryW windowRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed windowUnary unaryD budgetRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed budgetUnary unaryM modulusRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusUnary unaryS selectorRoute
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed selectorUnary unaryZ realSealRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed realSealUnary unaryH transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary unaryK replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary unaryN namedRoute
  have sourceNamed :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead := by
    exact ⟨hsame_refl namedRead, namedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row D ∨ hsame row M ∨ hsame row S ∨
              hsame row Z ∨ hsame row H ∨ hsame row K ∨ hsame row P ∨ hsame row N ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R W windowRead ∧ Cont windowRead D budgetRead ∧
              Cont budgetRead M modulusRead ∧ Cont modulusRead S selectorRead ∧
                Cont selectorRead Z realSealRead ∧ Cont realSealRead H transportRead ∧
                  Cont transportRead K replayRead ∧ Cont replayRead N namedRead ∧
                    PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead sourceNamed
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
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, budgetRoute, modulusRoute, selectorRoute, realSealRoute,
          transportRoute, replayRoute, namedRoute, namedPkg⟩
  }
  exact
    ⟨cert, windowUnary, budgetUnary, modulusUnary, selectorUnary, realSealUnary,
      transportUnary, replayUnary, namedUnary⟩

end FiniteCauchyTailHandoffUp

end BEDC.Derived
