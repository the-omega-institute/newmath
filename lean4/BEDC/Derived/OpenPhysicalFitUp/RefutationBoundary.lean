import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.OpenPhysicalFitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem OpenPhysicalFit_refutation_boundary [AskSetup] [PackageSetup]
    {H Pi O M C F E L R N refutationRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory F ->
      UnaryHistory C ->
        UnaryHistory L ->
          Cont F C refutationRead ->
            Cont refutationRead L ledgerRead ->
              PkgSig bundle ledgerRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row refutationRead ∨ hsame row ledgerRead)
                    (fun _row : BHist =>
                      Cont F C refutationRead ∧ Cont refutationRead L ledgerRead)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle ledgerRead pkg)
                    hsame ∧
                  UnaryHistory refutationRead ∧ UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fUnary cUnary lUnary refutationRoute ledgerRoute ledgerPkg
  have refutationUnary : UnaryHistory refutationRead :=
    unary_cont_closed fUnary cUnary refutationRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed refutationUnary lUnary ledgerRoute
  have carrierInhabited :
      Exists (fun row : BHist => hsame row refutationRead ∨ hsame row ledgerRead) :=
    Exists.intro refutationRead (Or.inl (hsame_refl refutationRead))
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refutationRead ∨ hsame row ledgerRead)
          (fun _row : BHist => Cont F C refutationRead ∧ Cont refutationRead L ledgerRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := carrierInhabited
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
        intro row other sameRows source
        cases source with
        | inl sameRefutation =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameRefutation)
        | inr sameLedger =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameLedger)
    }
    pattern_sound := by
      intro _row _source
      exact ⟨refutationRoute, ledgerRoute⟩
    ledger_sound := by
      intro row source
      cases source with
      | inl sameRefutation =>
          exact ⟨unary_transport refutationUnary (hsame_symm sameRefutation), ledgerPkg⟩
      | inr sameLedger =>
          exact ⟨unary_transport ledgerUnary (hsame_symm sameLedger), ledgerPkg⟩
  }
  exact ⟨cert, refutationUnary, ledgerUnary⟩

end BEDC.Derived.OpenPhysicalFitUp
