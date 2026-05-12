import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteMapCarrier [AskSetup] [PackageSetup]
    (spine query lookupRoute result duplicateLedger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory spine ∧ UnaryHistory query ∧ UnaryHistory lookupRoute ∧ UnaryHistory result ∧
    UnaryHistory duplicateLedger ∧ UnaryHistory provenance ∧ Cont spine query lookupRoute ∧
      Cont lookupRoute duplicateLedger result ∧ PkgSig bundle provenance pkg

theorem FiniteMapCarrier_ledger_transport [AskSetup] [PackageSetup]
    {spine query lookupRoute result duplicateLedger provenance spine' query' lookupRoute' result'
      duplicateLedger' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteMapCarrier spine query lookupRoute result duplicateLedger provenance bundle pkg ->
      hsame spine spine' ->
        hsame query query' ->
          hsame duplicateLedger duplicateLedger' ->
            hsame provenance provenance' ->
              Cont spine' query' lookupRoute' ->
                Cont lookupRoute' duplicateLedger' result' ->
                  FiniteMapCarrier spine' query' lookupRoute' result' duplicateLedger'
                      provenance' bundle pkg ∧
                    hsame lookupRoute lookupRoute' ∧ hsame result result' := by
  intro carrier sameSpine sameQuery sameDuplicateLedger sameProvenance spineQueryLookup'
    lookupDuplicateResult'
  rcases carrier with
    ⟨spineUnary, queryUnary, lookupUnary, resultUnary, duplicateUnary, provenanceUnary,
      spineQueryLookup, lookupDuplicateResult, pkgSig⟩
  have sameLookup : hsame lookupRoute lookupRoute' :=
    cont_respects_hsame sameSpine sameQuery spineQueryLookup spineQueryLookup'
  have sameResult : hsame result result' :=
    cont_respects_hsame sameLookup sameDuplicateLedger lookupDuplicateResult
      lookupDuplicateResult'
  have spineUnary' : UnaryHistory spine' :=
    unary_transport spineUnary sameSpine
  have queryUnary' : UnaryHistory query' :=
    unary_transport queryUnary sameQuery
  have lookupUnary' : UnaryHistory lookupRoute' :=
    unary_transport lookupUnary sameLookup
  have resultUnary' : UnaryHistory result' :=
    unary_transport resultUnary sameResult
  have duplicateUnary' : UnaryHistory duplicateLedger' :=
    unary_transport duplicateUnary sameDuplicateLedger
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  cases sameProvenance
  exact And.intro
    (And.intro spineUnary'
      (And.intro queryUnary'
        (And.intro lookupUnary'
          (And.intro resultUnary'
            (And.intro duplicateUnary'
              (And.intro provenanceUnary'
                (And.intro spineQueryLookup'
                  (And.intro lookupDuplicateResult' pkgSig))))))))
    (And.intro sameLookup sameResult)

theorem FiniteMapCarrier_lookup_option_exactness [AskSetup] [PackageSetup]
    {spine query lookupRoute result duplicateLedger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteMapCarrier spine query lookupRoute result duplicateLedger provenance bundle pkg ->
      Cont lookupRoute (BHist.e0 duplicateLedger) result -> False := by
  intro carrier extendedDuplicateLedger
  rcases carrier with
    ⟨_, _, _, _, _, _, _, lookupDuplicateResult, _⟩
  have sameDuplicateLedger : hsame duplicateLedger (BHist.e0 duplicateLedger) :=
    cont_left_cancel lookupDuplicateResult extendedDuplicateLedger
  exact hsame_extension_self_absurd.left duplicateLedger (hsame_symm sameDuplicateLedger)

theorem FiniteMapCarrier_public_support_lookup_boundary [AskSetup] [PackageSetup]
    {spine query lookupRoute result duplicateLedger provenance supportBoundary supportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteMapCarrier spine query lookupRoute result duplicateLedger provenance bundle pkg ->
      Cont spine duplicateLedger supportBoundary ->
        Cont supportBoundary provenance supportRead ->
          PkgSig bundle supportRead pkg ->
            UnaryHistory spine ∧ UnaryHistory query ∧ UnaryHistory lookupRoute ∧
              UnaryHistory result ∧ UnaryHistory duplicateLedger ∧ UnaryHistory provenance ∧
                UnaryHistory supportBoundary ∧ UnaryHistory supportRead ∧
                  Cont spine query lookupRoute ∧ Cont lookupRoute duplicateLedger result ∧
                    Cont spine duplicateLedger supportBoundary ∧
                      Cont supportBoundary provenance supportRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle supportRead pkg := by
  intro carrier spineDuplicateSupport supportProvenanceRead supportReadPkg
  rcases carrier with
    ⟨spineUnary, queryUnary, lookupUnary, resultUnary, duplicateUnary, provenanceUnary,
      spineQueryLookup, lookupDuplicateResult, provenancePkg⟩
  have supportBoundaryUnary : UnaryHistory supportBoundary :=
    unary_cont_closed spineUnary duplicateUnary spineDuplicateSupport
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed supportBoundaryUnary provenanceUnary supportProvenanceRead
  exact
    ⟨spineUnary, queryUnary, lookupUnary, resultUnary, duplicateUnary, provenanceUnary,
      supportBoundaryUnary, supportReadUnary, spineQueryLookup, lookupDuplicateResult,
      spineDuplicateSupport, supportProvenanceRead, provenancePkg, supportReadPkg⟩

end BEDC.Derived.FiniteMapUp
