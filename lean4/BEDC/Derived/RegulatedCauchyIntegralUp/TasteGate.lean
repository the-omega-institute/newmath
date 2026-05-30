import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegulatedCauchyIntegralUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegulatedCauchyIntegralCarrier [AskSetup] [PackageSetup]
    (integrand partition step windows readback realSeal transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory integrand ∧ UnaryHistory partition ∧ UnaryHistory step ∧
    UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont transport replay provenance ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem RegulatedCauchyIntegralWindowReadbackExactness [AskSetup] [PackageSetup]
    {integrand partition step windows readback realSeal transport replay provenance localName
      partitionRead stepRead windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegulatedCauchyIntegralCarrier integrand partition step windows readback realSeal transport
        replay provenance localName bundle pkg →
      Cont integrand partition partitionRead →
        Cont partition step stepRead →
          Cont step windows windowRead →
            Cont windowRead readback sealRead →
              PkgSig bundle provenance pkg →
                PkgSig bundle localName pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row integrand ∨ hsame row partition ∨ hsame row step ∨
                          hsame row windows ∨ hsame row readback ∨ hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle localName pkg)
                      hsame ∧
                    UnaryHistory partitionRead ∧ UnaryHistory stepRead ∧
                      UnaryHistory windowRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier integrandPartition partitionStep stepWindows windowReadReadback
    provenancePkg localNamePkg
  obtain ⟨integrandUnary, partitionUnary, stepUnary, windowsUnary, readbackUnary,
    _realSealUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _transportReplayProvenance, _carrierProvenancePkg, _carrierLocalNamePkg⟩ := carrier
  have partitionReadUnary : UnaryHistory partitionRead :=
    unary_cont_closed integrandUnary partitionUnary integrandPartition
  have stepReadUnary : UnaryHistory stepRead :=
    unary_cont_closed partitionUnary stepUnary partitionStep
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed stepUnary windowsUnary stepWindows
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary readbackUnary windowReadReadback
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row integrand ∨ hsame row partition ∨ hsame row step ∨
              hsame row windows ∨ hsame row readback ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, partitionReadUnary, stepReadUnary, windowReadUnary, sealReadUnary⟩

end BEDC.Derived.RegulatedCauchyIntegralUp
