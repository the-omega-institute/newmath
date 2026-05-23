import BEDC.Derived.FiniteLebesgueNumberUp.RootRadiusWindowObligationSurface

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRadiusLedgerExactness [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow carrierSource classifierRead
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont cover window carrierSource →
        Cont carrierSource radius classifierRead →
          Cont classifierRead nameRow ledgerRead →
            PkgSig bundle ledgerRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row cover ∨ hsame row window ∨ hsame row radius ∨
                      hsame row classifierRead ∨ hsame row ledgerRead)
                  (fun row : BHist => hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg)
                  hsame ∧
                UnaryHistory carrierSource ∧ UnaryHistory classifierRead ∧
                  UnaryHistory ledgerRead ∧ Cont cover window carrierSource ∧
                    Cont carrierSource radius classifierRead ∧
                      Cont classifierRead nameRow ledgerRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier coverWindowSource sourceRadiusClassifier classifierNameLedger ledgerPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, _meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory carrierSource :=
    unary_cont_closed coverUnary windowUnary coverWindowSource
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed sourceUnary radiusUnary sourceRadiusClassifier
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed classifierUnary nameRowUnary classifierNameLedger
  have sourceLedger :
      (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row) ledgerRead := by
    exact ⟨hsame_refl ledgerRead, ledgerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row window ∨ hsame row radius ∨
              hsame row classifierRead ∨ hsame row ledgerRead)
          (fun row : BHist => hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro ledgerRead sourceLedger
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
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, ledgerPkg⟩
    }
  exact
    ⟨cert, sourceUnary, classifierUnary, ledgerUnary, coverWindowSource,
      sourceRadiusClassifier, classifierNameLedger, provenancePkg, ledgerPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
