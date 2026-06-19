import BEDC.Derived.RegularCauchyRegularityWitnessUp.NameCertObligations

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyRegularityWitnessUp

theorem RegularCauchyRegularityWitness_tail_window_regularity [AskSetup] [PackageSetup]
    {source _diagonal consumer limitSeal tailWindow regularityRead _transport _replay provenance name :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory tailWindow →
        UnaryHistory limitSeal →
          Cont source tailWindow regularityRead →
            Cont regularityRead limitSeal consumer →
              PkgSig bundle provenance pkg →
                PkgSig bundle name pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row tailWindow ∨ hsame row regularityRead ∨ hsame row limitSeal ∨
                          hsame row consumer)
                      (fun row : BHist =>
                        hsame row consumer ∧ Cont source tailWindow regularityRead ∧
                          Cont regularityRead limitSeal consumer)
                      hsame ∧
                    Cont source tailWindow regularityRead ∧
                      Cont regularityRead limitSeal consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro sourceUnary tailUnary limitUnary sourceToRegularity regularityToConsumer
    _provenancePkg _namePkg
  have regularityUnary : UnaryHistory regularityRead :=
    unary_cont_closed sourceUnary tailUnary sourceToRegularity
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed regularityUnary limitUnary regularityToConsumer
  have sourceConsumer :
      (fun row : BHist => hsame row consumer ∧ UnaryHistory row) consumer := by
    exact ⟨hsame_refl consumer, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row tailWindow ∨ hsame row regularityRead ∨ hsame row limitSeal ∨
              hsame row consumer)
          (fun row : BHist =>
            hsame row consumer ∧ Cont source tailWindow regularityRead ∧
              Cont regularityRead limitSeal consumer)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer sourceConsumer
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
      exact Or.inr (Or.inr (Or.inr sourceRow.left))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, sourceToRegularity, regularityToConsumer⟩
  }
  exact ⟨cert, sourceToRegularity, regularityToConsumer⟩

end BEDC.Derived.RegularCauchyRegularityWitnessUp
