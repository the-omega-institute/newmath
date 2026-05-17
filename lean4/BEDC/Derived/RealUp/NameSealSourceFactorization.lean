import BEDC.Derived.RealUp.Core
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Package

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealNameSealCarrier [AskSetup] [PackageSetup]
    (dyadic stream regular ledger sealRow transport route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory regular ∧
    UnaryHistory ledger ∧ UnaryHistory nameRow ∧ Cont stream dyadic regular ∧
      Cont regular ledger sealRow ∧ Cont sealRow transport route ∧
        Cont route nameRow provenance ∧ PkgSig bundle sealRow pkg

theorem RealNameSeal_source_factorization [AskSetup] [PackageSetup]
    {dyadic stream regular ledger sealRow transport route provenance nameRow sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealNameSealCarrier dyadic stream regular ledger sealRow transport route provenance nameRow
        bundle pkg ->
      Cont stream dyadic sourceRead ->
        PkgSig bundle sourceRead pkg ->
          UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory regular ∧
            UnaryHistory ledger ∧ UnaryHistory sealRow ∧ UnaryHistory sourceRead ∧
              Cont stream dyadic regular ∧ Cont regular ledger sealRow ∧
                Cont sealRow transport route ∧ Cont route nameRow provenance ∧
                  Cont stream dyadic sourceRead ∧ PkgSig bundle sealRow pkg ∧
                    PkgSig bundle sourceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier streamDyadicSource sourceReadPkg
  obtain ⟨dyadicUnary, streamUnary, regularUnary, ledgerUnary, _nameRowUnary,
    streamDyadicRegular, regularLedgerSeal, sealTransportRoute, routeNameProvenance,
    sealPkg⟩ := carrier
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed regularUnary ledgerUnary regularLedgerSeal
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed streamUnary dyadicUnary streamDyadicSource
  exact
    ⟨dyadicUnary, streamUnary, regularUnary, ledgerUnary, sealUnary, sourceReadUnary,
      streamDyadicRegular, regularLedgerSeal, sealTransportRoute, routeNameProvenance,
      streamDyadicSource, sealPkg, sourceReadPkg⟩

end BEDC.Derived.RealUp
