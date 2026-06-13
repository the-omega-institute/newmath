import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.Package

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CriticalLineWitnessRootComponentwiseNamecertTransport [AskSetup] [PackageSetup]
    {zero strip modulus realPart comparison transport replay provenance localName readback
      bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalLineWitnessCarrier zero strip modulus realPart comparison transport replay provenance
        localName →
      Cont zero strip readback →
        Cont readback transport bridge →
          PkgSig bundle provenance pkg →
            PkgSig bundle bridge pkg →
            SemanticNameCert
                (fun row : BHist => hsame row bridge ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row zero ∨ hsame row strip ∨ hsame row modulus ∨
                    hsame row comparison ∨ hsame row transport ∨ hsame row bridge)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont zero strip readback ∧
                    Cont readback transport bridge ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle bridge pkg)
                hsame ∧
              UnaryHistory readback ∧ UnaryHistory bridge := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet readbackRoute bridgeRoute provenancePkg bridgePkg
  obtain ⟨zeroUnary, stripUnary, modulusUnary, realPartUnary, provenanceUnary,
    sameTransport, comparisonRoute, replayRoute, _localNameRoute⟩ := packet
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed modulusUnary realPartUnary comparisonRoute
  have transportSourceUnary : UnaryHistory (append zero strip) :=
    unary_cont_closed zeroUnary stripUnary (cont_intro rfl)
  have transportUnary : UnaryHistory transport :=
    unary_transport transportSourceUnary (hsame_symm sameTransport)
  have _replayUnary : UnaryHistory replay :=
    unary_cont_closed comparisonUnary transportUnary replayRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed zeroUnary stripUnary readbackRoute
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed readbackUnary transportUnary bridgeRoute
  have _provenanceUnaryCopy : UnaryHistory provenance :=
    unary_transport provenanceUnary (hsame_refl provenance)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridge ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row zero ∨ hsame row strip ∨ hsame row modulus ∨
              hsame row comparison ∨ hsame row transport ∨ hsame row bridge)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont zero strip readback ∧
              Cont readback transport bridge ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle bridge pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridge ⟨hsame_refl bridge, bridgeUnary⟩
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
      exact ⟨source.right, readbackRoute, bridgeRoute, provenancePkg, bridgePkg⟩
  }
  exact ⟨cert, readbackUnary, bridgeUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
