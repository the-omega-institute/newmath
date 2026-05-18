import BEDC.Derived.UniformCauchyCriterionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_real_completion_finite_envelope_no_choice_extraction
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name consumer
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail consumer ->
        Cont tail sealRow sealRead ->
          PkgSig bundle consumer pkg ->
            PkgSig bundle sealRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row index ∨ hsame row windows ∨ hsame row modulus ∨
                      hsame row tolerance ∨ hsame row tail ∨ hsame row sealRow ∨
                        hsame row consumer ∨ hsame row sealRead)
                  (fun row : BHist => PkgSig bundle consumer pkg ∧ hsame row consumer)
                  hsame ∧
                UnaryHistory consumer ∧ UnaryHistory sealRead ∧ Cont index tail consumer ∧
                  Cont tail sealRow sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro packet indexTailConsumer tailSealRead consumerPkg _sealReadPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, _namePkg⟩ :=
    packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed indexUnary tailUnary indexTailConsumer
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row index ∨ hsame row windows ∨ hsame row modulus ∨
              hsame row tolerance ∨ hsame row tail ∨ hsame row sealRow ∨
                hsame row consumer ∨ hsame row sealRead)
          (fun row : BHist => PkgSig bundle consumer pkg ∧ hsame row consumer)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))))
      ledger_sound := by
        intro _row source
        exact ⟨consumerPkg, source.left⟩
    }
  exact ⟨cert, consumerUnary, sealReadUnary, indexTailConsumer, tailSealRead⟩

end BEDC.Derived.UniformCauchyCriterionUp
