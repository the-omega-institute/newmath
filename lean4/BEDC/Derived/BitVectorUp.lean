import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BitVectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BitVectorSourcePacket [AskSetup] [PackageSetup]
    (n spine ledger route provenance source : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  UnaryHistory n ∧ UnaryHistory spine ∧ UnaryHistory route ∧ Cont n spine ledger ∧
    Cont ledger route provenance ∧ PkgSig bundle source pkg

theorem BitVectorSourcePacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {n spine ledger route provenance source : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    BitVectorSourcePacket n spine ledger route provenance source bundle pkg →
      UnaryHistory n ∧ UnaryHistory spine ∧ Cont n spine ledger ∧
        Cont ledger route provenance ∧ hsame ledger (append n spine) ∧
          hsame provenance (append ledger route) ∧ PkgSig bundle source pkg := by
  intro packet
  obtain ⟨nUnary, spineUnary, _routeUnary, ledgerRow, provenanceRow, pkgRow⟩ := packet
  exact ⟨nUnary, spineUnary, ledgerRow, provenanceRow, ledgerRow, provenanceRow, pkgRow⟩

end BEDC.Derived.BitVectorUp
