import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BHistHendecaSequenceNameCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BHistHendecaSequenceNameCertCarrier [AskSetup] [PackageSetup]
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 order route provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig
  UnaryHistory r0 ∧ UnaryHistory r1 ∧ UnaryHistory r2 ∧ UnaryHistory r3 ∧
    UnaryHistory r4 ∧ UnaryHistory r5 ∧ UnaryHistory r6 ∧ UnaryHistory r7 ∧
      UnaryHistory r8 ∧ UnaryHistory r9 ∧ UnaryHistory r10 ∧ UnaryHistory order ∧
        UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont route provenance localName ∧ PkgSig bundle localName pkg

theorem BHistHendecaSequenceNameCertCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 order route provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BHistHendecaSequenceNameCertCarrier r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 order
        route provenance localName bundle pkg ->
      PkgSig bundle localName pkg ->
        SemanticNameCert
            (fun row : BHist =>
              BHistHendecaSequenceNameCertCarrier r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
                order route provenance localName bundle pkg ∧ hsame row localName)
            (fun row : BHist => UnaryHistory row ∧ hsame row localName)
            (fun _row : BHist => Cont route provenance localName ∧ PkgSig bundle localName pkg)
            hsame ∧
          UnaryHistory r0 ∧ UnaryHistory r1 ∧ UnaryHistory r2 ∧ UnaryHistory r3 ∧
            UnaryHistory r4 ∧ UnaryHistory r5 ∧ UnaryHistory r6 ∧ UnaryHistory r7 ∧
              UnaryHistory r8 ∧ UnaryHistory r9 ∧ UnaryHistory r10 ∧ UnaryHistory order := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier localPkg
  have carrierWitness := carrier
  obtain ⟨unaryR0, unaryR1, unaryR2, unaryR3, unaryR4, unaryR5, unaryR6, unaryR7,
    unaryR8, unaryR9, unaryR10, orderUnary, _routeUnary, _provenanceUnary, localNameUnary,
    routeLocalName, _carrierPkg⟩ := carrier
  have certCore :
      NameCert
        (fun row : BHist =>
          BHistHendecaSequenceNameCertCarrier r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
            order route provenance localName bundle pkg ∧ hsame row localName)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro localName
        (And.intro carrierWitness (hsame_refl localName))
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
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            BHistHendecaSequenceNameCertCarrier r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
              order route provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist => UnaryHistory row ∧ hsame row localName)
          (fun _row : BHist => Cont route provenance localName ∧ PkgSig bundle localName pkg)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact
          And.intro
            (unary_transport localNameUnary (hsame_symm sourceRow.right))
            sourceRow.right
      ledger_sound := by
        intro _row _sourceRow
        exact And.intro routeLocalName localPkg
    }
  exact
    ⟨semantic, unaryR0, unaryR1, unaryR2, unaryR3, unaryR4, unaryR5, unaryR6, unaryR7,
      unaryR8, unaryR9, unaryR10, orderUnary⟩

end BEDC.Derived.BHistHendecaSequenceNameCertUp
