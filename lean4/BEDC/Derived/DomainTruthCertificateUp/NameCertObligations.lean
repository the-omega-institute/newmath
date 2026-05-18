import BEDC.Derived.DomainTruthCertificateUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DomainTruthCertificateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DomainTruthCertificateNameCertObligations [AskSetup] [PackageSetup]
    {truth domain openFit observerInvariant continuation failure transport replay provenance
      package localName domainRead failureRead _replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory truth →
      UnaryHistory domain →
        UnaryHistory openFit →
            UnaryHistory observerInvariant →
              UnaryHistory continuation →
                UnaryHistory failure →
                  UnaryHistory replay →
                    UnaryHistory localName →
                      Cont truth domain domainRead →
                        Cont continuation failure failureRead →
                          Cont replay localName namedRead →
                            PkgSig bundle namedRead pkg →
                              domainTruthCertificateFields
                                  (DomainTruthCertificateUp.mk truth domain openFit
                                    observerInvariant continuation failure transport replay
                                    provenance package localName) =
                                [truth, domain, openFit, observerInvariant, continuation,
                                  failure, transport, replay, provenance, package, localName] ∧
                                UnaryHistory domainRead ∧ UnaryHistory failureRead ∧
                                  UnaryHistory namedRead ∧
                                    SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row namedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row domainRead ∨ hsame row failureRead ∨
                                          hsame row namedRead)
                                      (fun row : BHist =>
                                        PkgSig bundle namedRead pkg ∧ hsame row namedRead)
                                      hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro truthUnary domainUnary _openFitUnary _observerInvariantUnary continuationUnary
    failureUnary replayUnary localNameUnary truthDomainRead continuationFailureRead
    replayLocalNamed namedPkg
  have domainReadUnary : UnaryHistory domainRead :=
    unary_cont_closed truthUnary domainUnary truthDomainRead
  have failureReadUnary : UnaryHistory failureRead :=
    unary_cont_closed continuationUnary failureUnary continuationFailureRead
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary localNameUnary replayLocalNamed
  have sourceNamed :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead := by
    exact ⟨hsame_refl namedRead, namedReadUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row domainRead ∨ hsame row failureRead ∨ hsame row namedRead)
        (fun row : BHist => PkgSig bundle namedRead pkg ∧ hsame row namedRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro namedRead sourceNamed
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
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨namedPkg, source.left⟩
    }
  exact ⟨rfl, domainReadUnary, failureReadUnary, namedReadUnary, cert⟩

end BEDC.Derived.DomainTruthCertificateUp
