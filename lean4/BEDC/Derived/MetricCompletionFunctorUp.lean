import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetricCompletionFunctorCarrier [AskSetup] [PackageSetup]
    (sourceCompletion targetCompletion mapRow extension functoriality transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceCompletion ∧ UnaryHistory targetCompletion ∧ UnaryHistory mapRow ∧
    UnaryHistory extension ∧ UnaryHistory functoriality ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont sourceCompletion mapRow extension ∧
          Cont extension targetCompletion functoriality ∧ hsame transport localName ∧
            PkgSig bundle provenance pkg

theorem MetricCompletionFunctorCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {sourceCompletion targetCompletion mapRow extension functoriality transport replay
      provenance localName extensionRead functorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionFunctorCarrier sourceCompletion targetCompletion mapRow extension
        functoriality transport replay provenance localName bundle pkg →
      Cont sourceCompletion mapRow extensionRead →
        Cont extensionRead targetCompletion functorRead →
          PkgSig bundle provenance pkg →
            PkgSig bundle functorRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row functorRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row sourceCompletion ∨ hsame row targetCompletion ∨
                      hsame row mapRow ∨ hsame row extension ∨ hsame row functoriality ∨
                        hsame row functorRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle functorRead pkg)
                  hsame ∧
                UnaryHistory extensionRead ∧ UnaryHistory functorRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier sourceMapExtension extensionTargetFunctor provenancePkg functorPkg
  obtain ⟨sourceUnary, targetUnary, mapUnary, _extensionUnary, _functorialityUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _carrierExtensionRoute, _carrierFunctorRoute, _transportLocalName,
    _carrierProvenancePkg⟩ := carrier
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed sourceUnary mapUnary sourceMapExtension
  have functorReadUnary : UnaryHistory functorRead :=
    unary_cont_closed extensionReadUnary targetUnary extensionTargetFunctor
  have sourceFunctor :
      (fun row : BHist => hsame row functorRead ∧ UnaryHistory row) functorRead := by
    exact ⟨hsame_refl functorRead, functorReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row functorRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceCompletion ∨ hsame row targetCompletion ∨ hsame row mapRow ∨
              hsame row extension ∨ hsame row functoriality ∨ hsame row functorRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle functorRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro functorRead sourceFunctor
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, functorPkg⟩
  }
  exact ⟨cert, extensionReadUnary, functorReadUnary⟩

end BEDC.Derived.MetricCompletionFunctorUp
