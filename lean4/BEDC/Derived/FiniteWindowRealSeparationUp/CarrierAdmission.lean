import BEDC.Derived.FiniteWindowRealSeparationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteWindowRealSeparationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteWindowRealSeparationCarrier_admission [AskSetup] [PackageSetup]
    {W D S R H C P N replay named : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    UnaryHistory W -> UnaryHistory D -> UnaryHistory S -> UnaryHistory R ->
      UnaryHistory H -> UnaryHistory C -> UnaryHistory P -> UnaryHistory N ->
        Cont W D S -> Cont S R replay -> Cont replay N named -> PkgSig bundle P pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row named ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨
                  hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                    hsame row replay ∨ hsame row named)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont W D S ∧ Cont S R replay ∧
                  Cont replay N named ∧ PkgSig bundle P pkg)
              hsame := by
  -- BEDC touchpoint anchor: FiniteWindowRealSeparationUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryW unaryD _unaryS unaryR _unaryH _unaryC _unaryP unaryN windowRoute
    replayRoute namedRoute packageP
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed (unary_cont_closed unaryW unaryD windowRoute) unaryR replayRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed replayUnary unaryN namedRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRoute, replayRoute, namedRoute, packageP⟩
  }

end BEDC.Derived.FiniteWindowRealSeparationUp
