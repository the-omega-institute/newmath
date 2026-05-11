import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.GradedAlgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GradedAlgebraPacket [AskSetup] [PackageSetup]
    (ring degree left right product tensorWindow componentWindow ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory ring ∧ UnaryHistory degree ∧ UnaryHistory left ∧ UnaryHistory right ∧
    UnaryHistory product ∧ UnaryHistory tensorWindow ∧ UnaryHistory componentWindow ∧
      UnaryHistory ledger ∧ UnaryHistory provenance ∧ Cont left right tensorWindow ∧
        Cont degree tensorWindow componentWindow ∧ Cont componentWindow product ledger ∧
          Cont ring ledger provenance ∧ PkgSig bundle ledger pkg

theorem GradedAlgebraPacket_product_ledger [AskSetup] [PackageSetup]
    {ring degree left right product tensorWindow componentWindow ledger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GradedAlgebraPacket ring degree left right product tensorWindow componentWindow ledger
        provenance bundle pkg ->
      Cont left right tensorWindow ->
        Cont degree tensorWindow componentWindow ->
          Cont componentWindow product ledger ->
            PkgSig bundle ledger pkg ->
              UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory product ∧
                UnaryHistory tensorWindow ∧ UnaryHistory componentWindow ∧ UnaryHistory ledger ∧
                  Cont left right tensorWindow ∧ Cont degree tensorWindow componentWindow ∧
                    Cont componentWindow product ledger ∧ PkgSig bundle ledger pkg := by
  intro packet tensorRow componentRow ledgerRow pkgRow
  cases packet with
  | intro _ringUnary rest =>
      cases rest with
      | intro degreeUnary rest =>
          cases rest with
          | intro leftUnary rest =>
              cases rest with
              | intro rightUnary rest =>
                  cases rest with
                  | intro productUnary _rest =>
                      have tensorUnary : UnaryHistory tensorWindow :=
                        unary_cont_closed leftUnary rightUnary tensorRow
                      have componentUnary : UnaryHistory componentWindow :=
                        unary_cont_closed degreeUnary tensorUnary componentRow
                      have ledgerUnary : UnaryHistory ledger :=
                        unary_cont_closed componentUnary productUnary ledgerRow
                      exact
                        ⟨leftUnary, rightUnary, productUnary, tensorUnary, componentUnary,
                          ledgerUnary, tensorRow, componentRow, ledgerRow, pkgRow⟩

end BEDC.Derived.GradedAlgebraUp
