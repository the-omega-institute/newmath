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

theorem UniformCauchyCriterionPacket_real_completion_exact_boundary_handoff
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name phaseRead
      exactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail phaseRead ->
        Cont phaseRead sealRow exactRead ->
          PkgSig bundle phaseRead pkg ->
            PkgSig bundle exactRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row exactRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row windows ∨ hsame row tolerance ∨ hsame row tail ∨
                      hsame row sealRow ∨ hsame row exactRead)
                  (fun row : BHist =>
                    PkgSig bundle exactRead pkg ∧ hsame row exactRead)
                  hsame ∧
                UnaryHistory phaseRead ∧ UnaryHistory exactRead ∧
                  Cont index tail phaseRead ∧ Cont phaseRead sealRow exactRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro packet indexTailPhase phaseSealExact _phasePkg exactPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, _namePkg⟩ := packet
  have phaseReadUnary : UnaryHistory phaseRead :=
    unary_cont_closed indexUnary tailUnary indexTailPhase
  have exactReadUnary : UnaryHistory exactRead :=
    unary_cont_closed phaseReadUnary sealRowUnary phaseSealExact
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row windows ∨ hsame row tolerance ∨ hsame row tail ∨
              hsame row sealRow ∨ hsame row exactRead)
          (fun row : BHist => PkgSig bundle exactRead pkg ∧ hsame row exactRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro exactRead ⟨hsame_refl exactRead, exactReadUnary⟩
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
        exact ⟨exactPkg, source.left⟩
    }
  exact ⟨cert, phaseReadUnary, exactReadUnary, indexTailPhase, phaseSealExact⟩

end BEDC.Derived.UniformCauchyCriterionUp
