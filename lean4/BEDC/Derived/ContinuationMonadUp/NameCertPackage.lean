import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_namecert_package [AskSetup] [PackageSetup]
    {A B C f g u H K L N packageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont K L packageRead ->
        PkgSig bundle L pkg ->
          PkgSig bundle packageRead pkg ->
            UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
              UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                UnaryHistory packageRead ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
                    (fun row : BHist => hsame row L ∨ hsame row packageRead)
                    (fun row : BHist =>
                      PkgSig bundle packageRead pkg ∧ hsame row packageRead)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier packageRoute _lPkg packagePkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    _sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have packageUnary : UnaryHistory packageRead :=
    unary_cont_closed unaryK unaryL packageRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row L ∨ hsame row packageRead)
        (fun row : BHist => PkgSig bundle packageRead pkg ∧ hsame row packageRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro packageRead ⟨hsame_refl packageRead, packageUnary⟩
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
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr source.left
      ledger_sound := by
        intro _row source
        exact ⟨packagePkg, source.left⟩
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, packageUnary,
      cert⟩

end BEDC.Derived.ContinuationMonadUp
