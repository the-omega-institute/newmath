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

theorem ClassifierTypingCarrier_signature_gap_readback [AskSetup] [PackageSetup]
    {term membership reduction signature transport routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClassifierTypingCarrier term membership reduction signature transport routes provenance name
        bundle pkg ->
      UnaryHistory signature ∧ Ext term BMark.b0 membership ∧
        Cont term reduction signature ∧ SigRel bundle term signature ∧
          PkgSig bundle provenance pkg ∧ hsame name name := by
  intro carrier
  obtain
    ⟨_termUnary, _membershipUnary, _reductionUnary, signatureUnary, _transportUnary,
      _routesUnary, _provenanceUnary, _nameUnary, termMembership, termReductionSignature,
      _membershipRoutesName, termSignature, provenancePkg⟩ := carrier
  exact
    ⟨signatureUnary, termMembership, termReductionSignature, termSignature, provenancePkg,
      hsame_refl name⟩

theorem ClassifierTypingCarrier_subject_reduction_cont_stability [AskSetup] [PackageSetup]
    {term membership reduction signature transport routes provenance name targetMembership : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClassifierTypingCarrier term membership reduction signature transport routes provenance name
        bundle pkg ->
      Cont signature routes targetMembership ->
        PkgSig bundle targetMembership pkg ->
          UnaryHistory term ∧ UnaryHistory membership ∧ UnaryHistory signature ∧
            UnaryHistory targetMembership ∧ Ext term BMark.b0 membership ∧
              Cont term reduction signature ∧ Cont signature routes targetMembership ∧
                SigRel bundle term signature ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle targetMembership pkg := by
  intro carrier signatureRoutesTarget targetPkg
  obtain
    ⟨termUnary, membershipUnary, _reductionUnary, signatureUnary, _transportUnary,
      routesUnary, _provenanceUnary, _nameUnary, termMembership, termReductionSignature,
      _membershipRoutesName, termSignature, provenancePkg⟩ := carrier
  have targetUnary : UnaryHistory targetMembership :=
    unary_cont_closed signatureUnary routesUnary signatureRoutesTarget
  exact
    ⟨termUnary, membershipUnary, signatureUnary, targetUnary, termMembership,
      termReductionSignature, signatureRoutesTarget, termSignature, provenancePkg, targetPkg⟩

theorem ClassifierTypingCarrier_visible_answer_determinacy [AskSetup] [PackageSetup]
    {term membership reduction signature transport routes provenance name term' membership'
      reduction' signature' transport' routes' provenance' name' answer answer' : BHist}
    {bundle bundle' : ProbeBundle ProbeName} {pkg pkg' : Pkg} :
    ClassifierTypingCarrier term membership reduction signature transport routes provenance name
        bundle pkg ->
      ClassifierTypingCarrier term' membership' reduction' signature' transport' routes'
          provenance' name' bundle' pkg' ->
        hsame signature signature' ->
          Cont signature routes answer ->
            Cont signature' routes' answer' ->
              hsame routes routes' ->
                hsame answer answer' ∧ SigRel bundle term signature ∧
                  SigRel bundle' term' signature' := by
  -- BEDC touchpoint anchor: BHist Cont hsame SigRel ProbeBundle
  intro carrier carrier' sameSignature answerRoute answerRoute' sameRoutes
  obtain
    ⟨_termUnary, _membershipUnary, _reductionUnary, _signatureUnary, _transportUnary,
      _routesUnary, _provenanceUnary, _nameUnary, _termMembership, _termReductionSignature,
      _membershipRoutesName, termSignature, _provenancePkg⟩ := carrier
  obtain
    ⟨_termUnary', _membershipUnary', _reductionUnary', _signatureUnary', _transportUnary',
      _routesUnary', _provenanceUnary', _nameUnary', _termMembership',
      _termReductionSignature', _membershipRoutesName', termSignature', _provenancePkg'⟩ :=
    carrier'
  have sameAnswer : hsame answer answer' :=
    cont_respects_hsame sameSignature sameRoutes answerRoute answerRoute'
  exact ⟨sameAnswer, termSignature, termSignature'⟩

end BEDC.Derived.ClassifierTypingUp
