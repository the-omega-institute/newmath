import BEDC.Derived.UniformCauchyFilterUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformCauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyFilterCarrier_completion_handoff [AskSetup] [PackageSetup]
    {U F C T S R E H K P N baseRead rationalRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory U -> UnaryHistory F -> UnaryHistory C -> UnaryHistory T ->
      UnaryHistory S -> UnaryHistory R -> UnaryHistory E -> UnaryHistory H ->
        UnaryHistory K -> UnaryHistory P -> UnaryHistory N -> Cont F C baseRead ->
          Cont S R rationalRead -> Cont rationalRead E completionRead ->
            PkgSig bundle P pkg -> PkgSig bundle N pkg ->
              PkgSig bundle completionRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row F ∨ hsame row C ∨ hsame row S ∨ hsame row R ∨
                        hsame row E ∨ hsame row baseRead ∨ hsame row rationalRead ∨
                          hsame row completionRead)
                    (fun row : BHist =>
                      hsame row completionRead ∧ Cont F C baseRead ∧
                        Cont S R rationalRead ∧ Cont rationalRead E completionRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                            PkgSig bundle completionRead pkg)
                    hsame ∧ UnaryHistory baseRead ∧ UnaryHistory rationalRead ∧
                  UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _unaryU unaryF unaryC _unaryT unaryS unaryR unaryE _unaryH _unaryK _unaryP
    _unaryN baseRoute rationalRoute completionRoute provenancePkg namePkg completionPkg
  have baseUnary : UnaryHistory baseRead :=
    unary_cont_closed unaryF unaryC baseRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed unaryS unaryR rationalRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed rationalUnary unaryE completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row C ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨
              hsame row baseRead ∨ hsame row rationalRead ∨ hsame row completionRead)
          (fun row : BHist =>
            hsame row completionRead ∧ Cont F C baseRead ∧ Cont S R rationalRead ∧
              Cont rationalRead E completionRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, baseRoute, rationalRoute, completionRoute, provenancePkg,
          namePkg, completionPkg⟩
  }
  exact ⟨cert, baseUnary, rationalUnary, completionUnary⟩

end BEDC.Derived.UniformCauchyFilterUp
