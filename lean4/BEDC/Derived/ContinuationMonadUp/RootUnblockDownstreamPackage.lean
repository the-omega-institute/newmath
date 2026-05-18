import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_unblock_downstream_package [AskSetup] [PackageSetup]
    {A B C f g u H K L N read category generator : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N read ->
        Cont read category generator ->
          UnaryHistory category ->
            PkgSig bundle L pkg ->
              PkgSig bundle generator pkg ->
                (SemanticNameCert
                  (fun row : BHist => hsame row L ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row L ∧ Cont L N read ∧ Cont read category generator)
                  (fun row : BHist =>
                    hsame row L ∧ PkgSig bundle L pkg ∧ PkgSig bundle generator pkg)
                  hsame ∧
                    UnaryHistory read ∧ UnaryHistory generator ∧ hsame N L) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier readRoute generatorRoute categoryUnary pkgL pkgGenerator
  have closure :
      UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory K ∧ UnaryHistory L ∧ hsame N L :=
    ContinuationMonadCarrier_route_closure carrier
  have unaryL : UnaryHistory L :=
    closure.right.right.right.left
  have sameEndpoint : hsame N L :=
    closure.right.right.right.right
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have readUnary : UnaryHistory read :=
    unary_cont_closed unaryL unaryN readRoute
  have generatorUnary : UnaryHistory generator :=
    unary_cont_closed readUnary categoryUnary generatorRoute
  have sourceL : (fun row : BHist => hsame row L ∧ UnaryHistory row) L := by
    exact ⟨hsame_refl L, unaryL⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row L ∧ UnaryHistory row)
        (fun row : BHist => hsame row L ∧ Cont L N read ∧ Cont read category generator)
        (fun row : BHist =>
          hsame row L ∧ PkgSig bundle L pkg ∧ PkgSig bundle generator pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro L sourceL
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, readRoute, generatorRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, pkgL, pkgGenerator⟩
    }
  exact ⟨cert, readUnary, generatorUnary, sameEndpoint⟩

end BEDC.Derived.ContinuationMonadUp
