import BEDC.Derived.RegulatedIntegralUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.RegulatedIntegralUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

def RegulatedIntegralNonescapeLedger [AskSetup] [PackageSetup]
    (interval integrand approximation stepPrimitive compatibility realHandoff errorLedger
      transport replay provenance localName read : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont interval integrand approximation ∧
    Cont approximation stepPrimitive compatibility ∧
      Cont compatibility errorLedger realHandoff ∧
        Cont transport replay provenance ∧
          Cont realHandoff localName read ∧
            hsame read realHandoff ∧
              PkgSig bundle read pkg

theorem RegulatedIntegralNonescape [AskSetup] [PackageSetup]
    {interval integrand approximation stepPrimitive compatibility realHandoff errorLedger
      transport replay provenance localName read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegulatedIntegralNonescapeLedger interval integrand approximation stepPrimitive
        compatibility realHandoff errorLedger transport replay provenance localName read
        bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row realHandoff ∨ hsame row read)
          (fun row : BHist =>
            hsame row interval ∨ hsame row integrand ∨ hsame row stepPrimitive ∨
              hsame row compatibility ∨ hsame row realHandoff)
          (fun row : BHist =>
            PkgSig bundle read pkg ∧ (hsame row realHandoff ∨ hsame row read))
          hsame ∧
        PkgSig bundle read pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert hsame ProbeBundle
  intro ledger
  obtain ⟨_intervalIntegrandApproximation, _approximationStepPrimitiveCompatibility,
    _compatibilityErrorLedgerRealHandoff, _transportReplayProvenance,
    _realHandoffLocalNameRead, readSameRealHandoff, readPkg⟩ := ledger
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realHandoff ∨ hsame row read)
          (fun row : BHist =>
            hsame row interval ∨ hsame row integrand ∨ hsame row stepPrimitive ∨
              hsame row compatibility ∨ hsame row realHandoff)
          (fun row : BHist =>
            PkgSig bundle read pkg ∧ (hsame row realHandoff ∨ hsame row read))
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro read (Or.inr (hsame_refl read))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' same same'
        exact hsame_trans same same'
      carrier_respects_equiv := by
        intro _row _row' same source
        cases source with
        | inl sameReal =>
            exact Or.inl (hsame_trans (hsame_symm same) sameReal)
        | inr sameRead =>
            exact Or.inr (hsame_trans (hsame_symm same) sameRead)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameReal =>
          exact Or.inr (Or.inr (Or.inr (Or.inr sameReal)))
      | inr sameRead =>
          have sameReal : hsame _ realHandoff :=
            hsame_trans sameRead readSameRealHandoff
          exact Or.inr (Or.inr (Or.inr (Or.inr sameReal)))
    ledger_sound := by
      intro _row source
      exact And.intro readPkg source
  }
  exact And.intro cert readPkg

end BEDC.Derived.RegulatedIntegralUp
