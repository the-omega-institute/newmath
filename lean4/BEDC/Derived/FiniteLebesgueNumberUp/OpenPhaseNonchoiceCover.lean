import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberOpenPhaseNonchoiceCover [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow classifierRead compactRead
      uniformRead outsideRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont cover radius classifierRead →
        Cont classifierRead mesh compactRead →
          Cont compactRead nameRow uniformRead →
            hsame outsideRead uniformRead →
              PkgSig bundle uniformRead pkg →
                UnaryHistory outsideRead ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row cover ∨ hsame row radius ∨ hsame row outsideRead ∨
                        hsame row uniformRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg ∧
                        hsame row uniformRead)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier coverRadiusClassifier classifierMeshCompact compactNameUniform
    sameOutsideUniform uniformPkg
  obtain ⟨coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed coverUnary radiusUnary coverRadiusClassifier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed classifierUnary meshUnary classifierMeshCompact
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary nameRowUnary compactNameUniform
  have outsideUnary : UnaryHistory outsideRead :=
    unary_transport_symm uniformUnary sameOutsideUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row cover ∨ hsame row radius ∨ hsame row outsideRead ∨
            hsame row uniformRead)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg ∧
            hsame row uniformRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro uniformRead sourceUniform
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
      exact ⟨provenancePkg, uniformPkg, source.left⟩
  }
  exact ⟨outsideUnary, cert⟩

end BEDC.Derived.FiniteLebesgueNumberUp
