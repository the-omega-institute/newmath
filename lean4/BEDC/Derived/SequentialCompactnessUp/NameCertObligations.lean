import BEDC.Derived.SequentialCompactnessUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentialCompactnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactnessCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {compactSource sequenceWindow selectorWindow readback realSeal transport provenance
      localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory compactSource →
      UnaryHistory sequenceWindow →
        UnaryHistory readback →
          UnaryHistory transport →
            Cont compactSource sequenceWindow selectorWindow →
              Cont selectorWindow readback realSeal →
                Cont realSeal transport consumer →
                  PkgSig bundle provenance pkg →
                    PkgSig bundle localCert pkg →
                      PkgSig bundle consumer pkg →
                        SemanticNameCert
                          (fun row : BHist =>
                            hsame row selectorWindow ∨ hsame row realSeal ∨
                              hsame row consumer)
                          (fun row : BHist => UnaryHistory row)
                          (fun _row : BHist =>
                            PkgSig bundle provenance pkg ∧ PkgSig bundle localCert pkg ∧
                              PkgSig bundle consumer pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro compactUnary sequenceUnary readbackUnary transportUnary selectorCont realSealCont
    consumerCont provenancePkg localCertPkg consumerPkg
  have selectorUnary : UnaryHistory selectorWindow :=
    unary_cont_closed compactUnary sequenceUnary selectorCont
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed selectorUnary readbackUnary realSealCont
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed realSealUnary transportUnary consumerCont
  have selectorSource :
      (fun row : BHist =>
        hsame row selectorWindow ∨ hsame row realSeal ∨ hsame row consumer) selectorWindow := by
    exact Or.inl (hsame_refl selectorWindow)
  exact {
    core := {
      carrier_inhabited := Exists.intro selectorWindow selectorSource
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
        intro row other same source
        cases source with
        | inl sameSelector =>
            exact Or.inl (hsame_trans (hsame_symm same) sameSelector)
        | inr rest =>
            cases rest with
            | inl sameSeal =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) sameSeal))
            | inr sameConsumer =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm same) sameConsumer))
    }
    pattern_sound := by
      intro row source
      cases source with
      | inl sameSelector =>
          exact unary_transport selectorUnary (hsame_symm sameSelector)
      | inr rest =>
          cases rest with
          | inl sameSeal =>
              exact unary_transport realSealUnary (hsame_symm sameSeal)
          | inr sameConsumer =>
              exact unary_transport consumerUnary (hsame_symm sameConsumer)
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, localCertPkg, consumerPkg⟩
  }

end BEDC.Derived.SequentialCompactnessUp
