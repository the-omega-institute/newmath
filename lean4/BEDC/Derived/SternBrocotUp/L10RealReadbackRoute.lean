import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.SternBrocotUp.TasteGate

namespace BEDC.Derived.SternBrocotUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SternBrocotL10RealReadbackRoute [AskSetup] [PackageSetup]
    {A L U M F B Q R H C P N treeRead streamRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont A M treeRead -> Cont treeRead Q streamRead -> Cont streamRead R realRead ->
      UnaryHistory A -> UnaryHistory M -> UnaryHistory Q -> UnaryHistory R ->
        PkgSig bundle P pkg ->
          SemanticNameCert (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row A ∨ hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row F ∨
                hsame row B ∨ hsame row Q ∨ hsame row R ∨ hsame row H ∨ hsame row C ∨
                  hsame row P ∨ hsame row N ∨ hsame row realRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont A M treeRead ∧ Cont treeRead Q streamRead ∧
                Cont streamRead R realRead ∧ PkgSig bundle P pkg)
            hsame ∧ UnaryHistory treeRead ∧ UnaryHistory streamRead ∧
              UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro treeRoute streamRoute realRoute aUnary mUnary qUnary rUnary provenancePkg
  have treeUnary : UnaryHistory treeRead :=
    unary_cont_closed aUnary mUnary treeRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed treeUnary qUnary streamRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed streamUnary rUnary realRoute
  have cert :
      SemanticNameCert (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row A ∨ hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row F ∨
            hsame row B ∨ hsame row Q ∨ hsame row R ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N ∨ hsame row realRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont A M treeRead ∧ Cont treeRead Q streamRead ∧
            Cont streamRead R realRead ∧ PkgSig bundle P pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, treeRoute, streamRoute, realRoute, provenancePkg⟩
  }
  exact ⟨cert, treeUnary, streamUnary, realUnary⟩

end BEDC.Derived.SternBrocotUp
