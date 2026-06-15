import BEDC.Derived.AnalogyCertificateGateUp.NameCertObligations

namespace BEDC.Derived.AnalogyCertificateGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AnalogyCertificateGateCarrier [AskSetup] [PackageSetup]
    (source carrier classifier relation preserved refused ledger exactness failure transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory source ∧ UnaryHistory carrier ∧ UnaryHistory classifier ∧
    UnaryHistory relation ∧ UnaryHistory preserved ∧ UnaryHistory refused ∧
      UnaryHistory ledger ∧ UnaryHistory exactness ∧ UnaryHistory failure ∧
        UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
          UnaryHistory localName ∧ Cont source carrier classifier ∧
            Cont classifier relation preserved ∧ Cont preserved refused ledger ∧
              Cont ledger exactness transport ∧ Cont transport replay provenance ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem AnalogyCertificateGateFalsifiablePrediction [AskSetup] [PackageSetup]
    {source carrier classifier relation preserved refused ledger exactness failure transport replay
      provenance localName admittedRead refusedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalogyCertificateGateCarrier source carrier classifier relation preserved refused ledger
        exactness failure transport replay provenance localName bundle pkg →
      Cont preserved refused admittedRead →
        Cont failure refused refusedRead →
          PkgSig bundle refusedRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row refusedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row preserved ∨ hsame row refused ∨ hsame row failure ∨
                    hsame row admittedRead ∨ hsame row refusedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont preserved refused admittedRead ∧
                    Cont failure refused refusedRead ∧ PkgSig bundle refusedRead pkg)
                hsame ∧
              UnaryHistory admittedRead ∧ UnaryHistory refusedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro gateCarrier preservedRefusedAdmitted failureRefusedRead refusedPkg
  obtain ⟨_sourceUnary, _carrierUnary, _classifierUnary, _relationUnary, preservedUnary,
    refusedUnary, _ledgerUnary, _exactnessUnary, failureUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _sourceCarrierClassifier, _classifierRelationPreserved,
    _preservedRefusedLedger, _ledgerExactnessTransport, _transportReplayProvenance,
    _provenancePkg, _localNamePkg⟩ := gateCarrier
  have admittedUnary : UnaryHistory admittedRead :=
    unary_cont_closed preservedUnary refusedUnary preservedRefusedAdmitted
  have refusedReadUnary : UnaryHistory refusedRead :=
    unary_cont_closed failureUnary refusedUnary failureRefusedRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row preserved ∨ hsame row refused ∨ hsame row failure ∨
              hsame row admittedRead ∨ hsame row refusedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont preserved refused admittedRead ∧
              Cont failure refused refusedRead ∧ PkgSig bundle refusedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusedRead ⟨hsame_refl refusedRead, refusedReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, preservedRefusedAdmitted, failureRefusedRead, refusedPkg⟩
  }
  exact ⟨cert, admittedUnary, refusedReadUnary⟩

end BEDC.Derived.AnalogyCertificateGateUp
