import BEDC.Derived.CauchyConvergenceCriterionUp.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp.CofinalModulusExtraction

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyConvergenceCriterionCarrier_cofinal_modulus_extraction [AskSetup]
    [PackageSetup]
    {stream modulus dyadic regular realSeal transport replay provenance localName
      toleranceRead thresholdRead regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier stream modulus dyadic regular realSeal transport replay
        provenance localName bundle pkg →
      Cont stream modulus toleranceRead → Cont toleranceRead dyadic thresholdRead →
      Cont thresholdRead regular regularRead → PkgSig bundle regularRead pkg →
      SemanticNameCert
          (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row modulus ∨ hsame row dyadic ∨ hsame row regular ∨
              hsame row regularRead)
          (fun row : BHist => hsame row regularRead ∧ PkgSig bundle regularRead pkg)
          hsame ∧
        UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
          UnaryHistory regular ∧ UnaryHistory regularRead ∧
            Cont stream modulus toleranceRead ∧ Cont toleranceRead dyadic thresholdRead ∧
              Cont thresholdRead regular regularRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier streamModulusRead toleranceDyadicRead thresholdRegularRead regularPkg
  obtain ⟨streamUnary, modulusUnary, dyadicUnary, regularUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _carrierStreamModulusDyadic, _carrierDyadicRegularSeal, _carrierSealTransportReplay,
    _carrierReplayProvenanceLocal, _sameSealRegular, _sameSealProvenance,
    _provenancePkg⟩ := carrier
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed streamUnary modulusUnary streamModulusRead
  have thresholdReadUnary : UnaryHistory thresholdRead :=
    unary_cont_closed toleranceReadUnary dyadicUnary toleranceDyadicRead
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed thresholdReadUnary regularUnary thresholdRegularRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row modulus ∨ hsame row dyadic ∨ hsame row regular ∨
              hsame row regularRead)
          (fun row : BHist => hsame row regularRead ∧ PkgSig bundle regularRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro regularRead ⟨hsame_refl regularRead, regularReadUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, regularPkg⟩
  }
  exact
    ⟨cert, streamUnary, modulusUnary, dyadicUnary, regularUnary, regularReadUnary,
      streamModulusRead, toleranceDyadicRead, thresholdRegularRead⟩

end BEDC.Derived.CauchyConvergenceCriterionUp.CofinalModulusExtraction
