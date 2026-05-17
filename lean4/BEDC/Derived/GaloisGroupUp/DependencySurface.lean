import BEDC.Derived.GaloisGroupUp

namespace BEDC.Derived.GaloisGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem GaloisGroupAutomorphismActionPacket_dependency_surface [AskSetup] [PackageSetup]
    {galoisExt group fixedBase action composition inverse classifier provenance ledger endpoint
      dependencySurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisGroupAutomorphismActionPacket galoisExt group fixedBase action composition inverse
        classifier provenance ledger endpoint bundle pkg →
      Cont galoisExt group provenance →
        Cont provenance ledger dependencySurface →
          PkgSig bundle dependencySurface pkg →
            UnaryHistory provenance ∧ UnaryHistory ledger ∧ UnaryHistory dependencySurface ∧
              hsame provenance (append galoisExt group) ∧
                hsame dependencySurface (append provenance ledger) ∧
                  PkgSig bundle endpoint pkg ∧ PkgSig bundle dependencySurface pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro packet galoisGroupProvenance provenanceLedgerSurface surfacePkg
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed packet.left packet.right.left galoisGroupProvenance
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed packet.right.right.right.right.left
      packet.right.right.right.right.right.left
      packet.right.right.right.right.right.right.right.right.left
  have dependencyUnary : UnaryHistory dependencySurface :=
    unary_cont_closed provenanceUnary ledgerUnary provenanceLedgerSurface
  exact
    ⟨provenanceUnary, ledgerUnary, dependencyUnary, galoisGroupProvenance,
      provenanceLedgerSurface, packet.right.right.right.right.right.right.right.right.right.right,
      surfacePkg⟩

end BEDC.Derived.GaloisGroupUp
