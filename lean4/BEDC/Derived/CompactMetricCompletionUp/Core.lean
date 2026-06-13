import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompactMetricCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompactMetricCompletionCarrier [AskSetup] [PackageSetup]
    (totallyBoundedCompletion completeUniformSpace totallyBoundedLedger compactExport
      realSeal transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory totallyBoundedCompletion ∧ UnaryHistory completeUniformSpace ∧
    UnaryHistory totallyBoundedLedger ∧ UnaryHistory compactExport ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont totallyBoundedLedger totallyBoundedCompletion transport ∧
            Cont transport completeUniformSpace replay ∧ Cont replay realSeal compactExport ∧
              Cont compactExport provenance localName ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localName pkg

theorem CompactMetricCompletionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {totallyBoundedCompletion completeUniformSpace totallyBoundedLedger compactExport
      realSeal transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactMetricCompletionCarrier totallyBoundedCompletion completeUniformSpace
        totallyBoundedLedger compactExport realSeal transport replay provenance localName
        bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CompactMetricCompletionCarrier totallyBoundedCompletion completeUniformSpace
            totallyBoundedLedger compactExport realSeal transport replay provenance localName
            bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          hsame row totallyBoundedCompletion ∨ hsame row completeUniformSpace ∨
            hsame row totallyBoundedLedger ∨ hsame row compactExport ∨
              hsame row realSeal ∨ hsame row localName)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier
  have localUnary : UnaryHistory localName :=
    carrier.right.right.right.right.right.right.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have localPkg : PkgSig bundle localName pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro localName (And.intro carrier (hsame_refl localName))
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
          And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.right))))
    ledger_sound := by
      intro _row source
      exact
        And.intro (unary_transport localUnary (hsame_symm source.right))
          (And.intro provenancePkg localPkg)
  }

theorem CompactMetricCompletionFiniteNetSeal [AskSetup] [PackageSetup]
    {totallyBoundedCompletion completeUniformSpace totallyBoundedLedger compactExport
      realSeal transport replay provenance localName finiteNet compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactMetricCompletionCarrier totallyBoundedCompletion completeUniformSpace
        totallyBoundedLedger compactExport realSeal transport replay provenance localName
        bundle pkg →
      Cont totallyBoundedLedger totallyBoundedCompletion finiteNet →
        Cont finiteNet completeUniformSpace compactRead →
          PkgSig bundle compactRead pkg →
            UnaryHistory totallyBoundedLedger ∧ UnaryHistory totallyBoundedCompletion ∧
              UnaryHistory completeUniformSpace ∧ UnaryHistory compactExport ∧
                UnaryHistory realSeal ∧ UnaryHistory finiteNet ∧ UnaryHistory compactRead ∧
                  Cont totallyBoundedLedger totallyBoundedCompletion finiteNet ∧
                    Cont finiteNet completeUniformSpace compactRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier ledgerCompletion finiteComplete compactReadPkg
  have completionUnary : UnaryHistory totallyBoundedCompletion := carrier.left
  have uniformUnary : UnaryHistory completeUniformSpace := carrier.right.left
  have ledgerUnary : UnaryHistory totallyBoundedLedger := carrier.right.right.left
  have compactUnary : UnaryHistory compactExport := carrier.right.right.right.left
  have realUnary : UnaryHistory realSeal := carrier.right.right.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have finiteNetUnary : UnaryHistory finiteNet :=
    unary_cont_closed ledgerUnary completionUnary ledgerCompletion
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed finiteNetUnary uniformUnary finiteComplete
  exact
    And.intro ledgerUnary
      (And.intro completionUnary
        (And.intro uniformUnary
          (And.intro compactUnary
            (And.intro realUnary
              (And.intro finiteNetUnary
                (And.intro compactReadUnary
                  (And.intro ledgerCompletion
                    (And.intro finiteComplete
                      (And.intro provenancePkg compactReadPkg)))))))))

end BEDC.Derived.CompactMetricCompletionUp
