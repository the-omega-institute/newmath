import BEDC.Derived.RegularCauchyRegularityWitnessUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyRegularityWitnessUp

theorem RegularCauchyRegularityWitnessTailWindowRegularity [AskSetup] [PackageSetup]
    {S mu j Omega R Q E H C P N tailRead sealRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRegularityWitnessCarrier S mu j Omega R Q E H C P N bundle pkg →
      Cont Omega R tailRead →
        Cont tailRead Q sealRead →
          Cont sealRead E completionRead →
            PkgSig bundle completionRead pkg →
              UnaryHistory Omega ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory E ∧
                UnaryHistory tailRead ∧ UnaryHistory sealRead ∧ UnaryHistory completionRead ∧
                  Cont j Omega R ∧ Cont R Q E ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier omegaTail tailSeal sealCompletion completionPkg
  obtain ⟨_unaryS, _unaryMu, _unaryJ, unaryOmega, unaryR, unaryQ, unaryE,
    _unaryH, _unaryC, _unaryP, _unaryN, _routeSMuJ, routeJOmegaR, routeRQE,
    _routeEHC, _pkgP, _pkgN⟩ := carrier
  have unaryTailRead : UnaryHistory tailRead :=
    unary_cont_closed unaryOmega unaryR omegaTail
  have unarySealRead : UnaryHistory sealRead :=
    unary_cont_closed unaryTailRead unaryQ tailSeal
  have unaryCompletionRead : UnaryHistory completionRead :=
    unary_cont_closed unarySealRead unaryE sealCompletion
  exact
    ⟨unaryOmega, unaryR, unaryQ, unaryE, unaryTailRead, unarySealRead,
      unaryCompletionRead, routeJOmegaR, routeRQE, completionPkg⟩

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
