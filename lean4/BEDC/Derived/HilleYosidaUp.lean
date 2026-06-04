import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HilleYosidaUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HilleYosidaCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {B A R S N H C P L graphRead resolventRead semigroupRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B -> UnaryHistory A -> UnaryHistory R -> UnaryHistory S ->
      UnaryHistory N -> UnaryHistory C -> Cont B A graphRead ->
        Cont graphRead R resolventRead -> Cont resolventRead S semigroupRead ->
          Cont semigroupRead C replayRead -> PkgSig bundle P pkg ->
            PkgSig bundle L pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row B ∨ hsame row A ∨ hsame row R ∨ hsame row S ∨
                      hsame row N ∨ hsame row C ∨ hsame row replayRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont B A graphRead ∧
                      Cont graphRead R resolventRead ∧
                        Cont resolventRead S semigroupRead ∧
                          Cont semigroupRead C replayRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle L pkg)
                  hsame ∧
                UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro bUnary aUnary rUnary sUnary _nUnary cUnary graphRoute resolventRoute
    semigroupRoute replayRoute provenancePkg localNamePkg
  have graphUnary : UnaryHistory graphRead :=
    unary_cont_closed bUnary aUnary graphRoute
  have resolventUnary : UnaryHistory resolventRead :=
    unary_cont_closed graphUnary rUnary resolventRoute
  have semigroupUnary : UnaryHistory semigroupRead :=
    unary_cont_closed resolventUnary sUnary semigroupRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed semigroupUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row R ∨ hsame row S ∨ hsame row N ∨
              hsame row C ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B A graphRead ∧ Cont graphRead R resolventRead ∧
              Cont resolventRead S semigroupRead ∧ Cont semigroupRead C replayRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle L pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, graphRoute, resolventRoute, semigroupRoute, replayRoute,
          provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, replayUnary⟩

end BEDC.Derived.HilleYosidaUp
