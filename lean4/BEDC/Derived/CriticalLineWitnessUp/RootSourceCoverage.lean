import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.Package

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_source_coverage [AskSetup] [PackageSetup]
    {Z S M R Q H C P N sourceRead comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont sourceRead Q comparisonRead ->
          PkgSig bundle comparisonRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row sourceRead ∨ hsame row comparisonRead) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                    hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N ∨ hsame row sourceRead ∨ hsame row comparisonRead)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle comparisonRead pkg)
                hsame ∧
              UnaryHistory sourceRead ∧ UnaryHistory comparisonRead := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier sourceRoute comparisonRoute comparisonPkg
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    carrier
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have appendUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport appendUnary (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have _unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed sourceUnary unaryQ comparisonRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row sourceRead ∨ hsame row comparisonRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
              hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row sourceRead ∨ hsame row comparisonRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle comparisonRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro comparisonRead
          ⟨Or.inr (hsame_refl comparisonRead), comparisonUnary⟩
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
        cases source.left with
        | inl sameSource =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameSource),
                unary_transport source.right sameRows⟩
        | inr sameComparison =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameComparison),
                unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSource =>
          right; right; right; right; right; right; right; right; right
          exact Or.inl sameSource
      | inr sameComparison =>
          right; right; right; right; right; right; right; right; right; right
          exact sameComparison
    ledger_sound := by
      intro _row source
      exact ⟨source.right, comparisonPkg⟩
  }
  exact ⟨cert, sourceUnary, comparisonUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
