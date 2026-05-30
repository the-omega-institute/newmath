import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealNameClassifierUp [AskSetup] [PackageSetup]
    (source stream rat dyadic tolerance refinement sealRow transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  UnaryHistory source ∧ UnaryHistory stream ∧ UnaryHistory rat ∧ UnaryHistory dyadic ∧
    UnaryHistory tolerance ∧ UnaryHistory refinement ∧ UnaryHistory sealRow ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont source stream replay ∧ Cont rat dyadic tolerance ∧
          Cont tolerance refinement sealRow ∧ hsame transport replay ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

namespace RealNameClassifierUp

theorem RealNameClassifierSource_tolerance_obligation [AskSetup] [PackageSetup]
    {source stream rat dyadic tolerance refinement sealRow transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealNameClassifierUp source stream rat dyadic tolerance refinement sealRow transport replay
        provenance localName bundle pkg →
      Cont source tolerance refinement →
        PkgSig bundle provenance pkg →
          SemanticNameCert
            (fun row : BHist =>
              RealNameClassifierUp source stream rat dyadic tolerance refinement sealRow transport
                replay provenance localName bundle pkg ∧ hsame row localName)
            (fun row : BHist =>
              RealNameClassifierUp source stream rat dyadic tolerance refinement sealRow transport
                replay provenance localName bundle pkg ∧ hsame row localName)
            (fun row : BHist =>
              RealNameClassifierUp source stream rat dyadic tolerance refinement sealRow transport
                replay provenance localName bundle pkg ∧ hsame row localName)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier _sourceToleranceRefinement _provenancePkg
  have carrierWitness :
      RealNameClassifierUp source stream rat dyadic tolerance refinement sealRow transport replay
        provenance localName bundle pkg :=
    carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro localName ⟨carrierWitness, hsame_refl localName⟩
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
        intro _row _other same sourceData
        exact ⟨sourceData.left, hsame_trans (hsame_symm same) sourceData.right⟩
    }
    pattern_sound := by
      intro _row sourceData
      exact sourceData
    ledger_sound := by
      intro _row sourceData
      exact sourceData
  }

end RealNameClassifierUp
end BEDC.Derived
