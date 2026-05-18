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

theorem UniformCauchyCriterionPacket_real_envelope_source_minimality
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name windowRead
      sourceRead toleranceRead meetRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows windowRead ->
        Cont windowRead tail sourceRead ->
          Cont modulus tolerance toleranceRead ->
            Cont toleranceRead tail meetRead ->
              Cont meetRead sealRow completionRead ->
                PkgSig bundle completionRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row windows ∨ hsame row sourceRead ∨
                          hsame row toleranceRead ∨ hsame row meetRead ∨
                            hsame row completionRead)
                      (fun row : BHist =>
                        PkgSig bundle completionRead pkg ∧ hsame row completionRead)
                      hsame ∧
                    UnaryHistory windowRead ∧ UnaryHistory sourceRead ∧
                      UnaryHistory toleranceRead ∧ UnaryHistory meetRead ∧
                        UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro packet indexWindowsRead windowTailRead modulusToleranceRead toleranceTailRead
    meetSealRead completionPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, _namePkg⟩ :=
    packet
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsRead
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed windowReadUnary tailUnary windowTailRead
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed modulusUnary toleranceUnary modulusToleranceRead
  have meetReadUnary : UnaryHistory meetRead :=
    unary_cont_closed toleranceReadUnary tailUnary toleranceTailRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed meetReadUnary sealRowUnary meetSealRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row windows ∨ hsame row sourceRead ∨ hsame row toleranceRead ∨
              hsame row meetRead ∨ hsame row completionRead)
          (fun row : BHist =>
            PkgSig bundle completionRead pkg ∧ hsame row completionRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro completionRead ⟨hsame_refl completionRead, completionReadUnary⟩
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
        exact ⟨completionPkg, source.left⟩
    }
  exact
    ⟨cert, windowReadUnary, sourceReadUnary, toleranceReadUnary, meetReadUnary,
      completionReadUnary⟩

end BEDC.Derived.UniformCauchyCriterionUp
