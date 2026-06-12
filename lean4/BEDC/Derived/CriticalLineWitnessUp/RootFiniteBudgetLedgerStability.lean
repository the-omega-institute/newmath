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

theorem CriticalLineWitnessCarrier_root_finite_budget_ledger_stability
    [AskSetup] [PackageSetup]
    {Z S M R Q H C P N modulusRead transportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R modulusRead ->
        Cont H C transportRead ->
          PkgSig bundle modulusRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row Q ∨ hsame row modulusRead ∨ hsame row transportRead) ∧
                    UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                    hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N ∨ hsame row modulusRead ∨ hsame row transportRead)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle modulusRead pkg)
                hsame ∧
              UnaryHistory modulusRead ∧ UnaryHistory transportRead := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier modulusRoute transportRoute modulusPkg
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
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed unaryH unaryC transportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row Q ∨ hsame row modulusRead ∨ hsame row transportRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
              hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row modulusRead ∨ hsame row transportRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle modulusRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro modulusRead
          ⟨Or.inr (Or.inl (hsame_refl modulusRead)), modulusUnary⟩
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
        | inl sameQ =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameQ),
                unary_transport source.right sameRows⟩
        | inr rest =>
            cases rest with
            | inl sameModulus =>
                exact
                  ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameModulus)),
                    unary_transport source.right sameRows⟩
            | inr sameTransport =>
                exact
                  ⟨Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameTransport)),
                    unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameQ =>
          right; right; right; right
          exact Or.inl sameQ
      | inr rest =>
          cases rest with
          | inl sameModulus =>
              right; right; right; right; right; right; right; right; right
              exact Or.inl sameModulus
          | inr sameTransport =>
              right; right; right; right; right; right; right; right; right; right
              exact sameTransport
    ledger_sound := by
      intro _row source
      exact ⟨source.right, modulusPkg⟩
  }
  exact ⟨cert, modulusUnary, transportUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
