import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RelationalFrameAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RelationalFrameAuditLayeredRelationCertCarrier [AskSetup] [PackageSetup]
    (SA SB layer preserved missing ledger exact boundary H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  UnaryHistory SA ∧ UnaryHistory SB ∧ UnaryHistory layer ∧
    UnaryHistory preserved ∧ UnaryHistory missing ∧ UnaryHistory ledger ∧
      UnaryHistory exact ∧ UnaryHistory boundary ∧ UnaryHistory H ∧ UnaryHistory C ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
          SemanticNameCert
            (fun row : BHist => hsame row exact ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row SA ∨ hsame row SB ∨ hsame row layer ∨
                hsame row preserved ∨ hsame row missing ∨ hsame row ledger ∨
                  hsame row exact ∨ hsame row boundary ∨ hsame row H ∨
                    hsame row C ∨ hsame row P ∨ hsame row N)
            (fun row : BHist =>
              UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
            hsame

end BEDC.Derived.RelationalFrameAuditUp
