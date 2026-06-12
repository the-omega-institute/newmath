import BEDC.Derived.TheoremGapRegistryUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TheoremGapRegistryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TheoremGapRegistry_strength_gate [AskSetup] [PackageSetup]
    {T D S G C F A L H P N licensed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory D →
        Cont T D S →
          Cont D S licensed →
            PkgSig bundle P pkg →
              PkgSig bundle N pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row licensed ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row T ∨ hsame row D ∨ hsame row S ∨ hsame row licensed)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont T D S ∧ Cont D S licensed ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory licensed := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro tUnary dUnary strengthRoute licenseRoute provenancePkg namePkg
  have strengthUnary : UnaryHistory S :=
    unary_cont_closed tUnary dUnary strengthRoute
  have licensedUnary : UnaryHistory licensed :=
    unary_cont_closed dUnary strengthUnary licenseRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro licensed ⟨hsame_refl licensed, licensedUnary⟩
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
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, strengthRoute, licenseRoute, provenancePkg, namePkg⟩
    }
  · exact licensedUnary

theorem TheoremGapRegistry_ledger_nonescape [AskSetup] [PackageSetup]
    {T D S G C F A L _H P N licensed ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory D →
        UnaryHistory G →
          UnaryHistory C →
            UnaryHistory A →
              UnaryHistory L →
                Cont T D S →
                  Cont D S licensed →
                    Cont G C F →
                      Cont A L ledger →
                        PkgSig bundle P pkg →
                          PkgSig bundle N pkg →
                            SemanticNameCert
                                (fun row : BHist =>
                                  (hsame row licensed ∨ hsame row F ∨ hsame row ledger) ∧
                                    UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row T ∨ hsame row D ∨ hsame row S ∨
                                    hsame row G ∨ hsame row C ∨ hsame row F ∨
                                      hsame row A ∨ hsame row L ∨ hsame row licensed ∨
                                        hsame row ledger)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont T D S ∧ Cont D S licensed ∧
                                    Cont G C F ∧ Cont A L ledger ∧
                                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory licensed := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro tUnary dUnary gUnary cUnary aUnary lUnary strengthRoute licenseRoute gapRoute
    ledgerRoute provenancePkg namePkg
  have strengthUnary : UnaryHistory S :=
    unary_cont_closed tUnary dUnary strengthRoute
  have licensedUnary : UnaryHistory licensed :=
    unary_cont_closed dUnary strengthUnary licenseRoute
  have failureUnary : UnaryHistory F :=
    unary_cont_closed gUnary cUnary gapRoute
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed aUnary lUnary ledgerRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro licensed ⟨Or.inl (hsame_refl licensed), licensedUnary⟩
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
          constructor
          · cases source.left with
            | inl sameLicensed =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameLicensed)
            | inr tail =>
                cases tail with
                | inl sameFailure =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameFailure))
                | inr sameLedger =>
                    exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameLedger))
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl sameLicensed =>
            right
            right
            right
            right
            right
            right
            right
            right
            left
            exact sameLicensed
        | inr tail =>
            cases tail with
            | inl sameFailure =>
                right
                right
                right
                right
                right
                left
                exact sameFailure
            | inr sameLedger =>
                right
                right
                right
                right
                right
                right
                right
                right
                right
                exact sameLedger
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, strengthRoute, licenseRoute, gapRoute, ledgerRoute,
            provenancePkg, namePkg⟩
    }
  · exact licensedUnary

end BEDC.Derived.TheoremGapRegistryUp
