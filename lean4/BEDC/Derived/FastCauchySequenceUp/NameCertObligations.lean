import BEDC.Derived.FastCauchySequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FastCauchySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FastCauchySequenceCarrier [AskSetup] [PackageSetup]
    (dyadic stream modulus readback transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory modulus ∧
    UnaryHistory readback ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont dyadic stream modulus ∧
        Cont modulus readback replay ∧ Cont replay provenance localName ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem FastCauchySequenceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {dyadic stream modulus readback transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySequenceCarrier dyadic stream modulus readback transport replay provenance
        localName bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          FastCauchySequenceCarrier dyadic stream modulus readback transport replay provenance
              localName bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          FastCauchySequenceCarrier dyadic stream modulus readback transport replay provenance
              localName bundle pkg ∧
            (hsame row dyadic ∨ hsame row stream ∨ hsame row modulus ∨
              hsame row readback ∨ hsame row transport ∨ hsame row replay ∨
                hsame row provenance ∨ hsame row localName))
        (fun row : BHist =>
          FastCauchySequenceCarrier dyadic stream modulus readback transport replay provenance
              localName bundle pkg ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg ∧ hsame row localName)
        hsame ∧
        UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory modulus ∧
          UnaryHistory readback ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
            UnaryHistory provenance ∧ UnaryHistory localName ∧
              Cont dyadic stream modulus ∧ Cont modulus readback replay ∧
                Cont replay provenance localName ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier
  obtain ⟨dyadicUnary, streamUnary, modulusUnary, readbackUnary, transportUnary,
    replayUnary, provenanceUnary, localNameUnary, modulusRoute, replayRoute,
    localNameRoute, provenancePkg, localNamePkg⟩ := carrier
  have carrierFields :
      FastCauchySequenceCarrier dyadic stream modulus readback transport replay provenance
        localName bundle pkg :=
    ⟨dyadicUnary, streamUnary, modulusUnary, readbackUnary, transportUnary, replayUnary,
      provenanceUnary, localNameUnary, modulusRoute, replayRoute, localNameRoute, provenancePkg,
      localNamePkg⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          FastCauchySequenceCarrier dyadic stream modulus readback transport replay provenance
              localName bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          FastCauchySequenceCarrier dyadic stream modulus readback transport replay provenance
              localName bundle pkg ∧
            (hsame row dyadic ∨ hsame row stream ∨ hsame row modulus ∨
              hsame row readback ∨ hsame row transport ∨ hsame row replay ∨
                hsame row provenance ∨ hsame row localName))
        (fun row : BHist =>
          FastCauchySequenceCarrier dyadic stream modulus readback transport replay provenance
              localName bundle pkg ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg ∧ hsame row localName)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro localName (And.intro carrierFields (hsame_refl localName))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact And.intro source.left
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.right)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, localNamePkg, source.right⟩
  }
  exact
    ⟨cert, dyadicUnary, streamUnary, modulusUnary, readbackUnary, transportUnary, replayUnary,
      provenanceUnary, localNameUnary, modulusRoute, replayRoute, localNameRoute, provenancePkg,
      localNamePkg⟩

end BEDC.Derived.FastCauchySequenceUp
