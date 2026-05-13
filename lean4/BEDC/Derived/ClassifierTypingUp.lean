import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClassifierTypingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Ext
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def ClassifierTypingCarrier [AskSetup] [PackageSetup]
    (term membership reduction signature transport routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory term ∧
    UnaryHistory membership ∧
      UnaryHistory reduction ∧
        UnaryHistory signature ∧
          UnaryHistory transport ∧
            UnaryHistory routes ∧
              UnaryHistory provenance ∧
                UnaryHistory name ∧
                  Ext term BMark.b0 membership ∧
                    Cont term reduction signature ∧
                      Cont membership routes name ∧
                        SigRel bundle term signature ∧
                          PkgSig bundle provenance pkg

theorem ClassifierTypingCarrier_membership_stability [AskSetup] [PackageSetup]
    {term membership reduction signature transport routes provenance name membership' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClassifierTypingCarrier term membership reduction signature transport routes provenance name
        bundle pkg ->
      hsame membership membership' ->
        UnaryHistory membership' ∧ Ext term BMark.b0 membership ∧
          hsame membership membership' ∧ Cont membership routes name ∧
            PkgSig bundle provenance pkg := by
  intro carrier sameMembership
  obtain
    ⟨_termUnary, membershipUnary, _reductionUnary, _signatureUnary, _transportUnary,
      _routesUnary, _provenanceUnary, _nameUnary, termMembership, _termReductionSignature,
      membershipRoutesName, _termSignature, provenancePkg⟩ := carrier
  have membershipPrimeUnary : UnaryHistory membership' :=
    unary_transport membershipUnary sameMembership
  exact
    ⟨membershipPrimeUnary, termMembership, sameMembership, membershipRoutesName, provenancePkg⟩

theorem ClassifierTypingCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {term membership reduction signature transport routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClassifierTypingCarrier term membership reduction signature transport routes provenance name
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          ClassifierTypingCarrier term membership reduction signature transport routes provenance
              name bundle pkg ∧
            hsame row name)
        (fun row : BHist =>
          ClassifierTypingCarrier term membership reduction signature transport routes provenance
              name bundle pkg ∧
            hsame row name)
        (fun row : BHist =>
          ClassifierTypingCarrier term membership reduction signature transport routes provenance
              name bundle pkg ∧
            hsame row name)
        hsame := by
  intro carrier
  have carrierData :
      ClassifierTypingCarrier term membership reduction signature transport routes provenance name
        bundle pkg :=
    carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro name ⟨carrierData, hsame_refl name⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

end BEDC.Derived.ClassifierTypingUp
