import BEDC.Derived.LocatedInfimumUp

namespace BEDC.Derived.LocatedInfimumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedInfimumLowerCutStability [AskSetup] [PackageSetup]
    {family lower greatest window regseq realSeal transport route provenance name family' lower'
      greatest' window' regseq' realSeal' lowerRead stableRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedInfimumCarrier family lower greatest window regseq realSeal transport route
        provenance name bundle pkg ->
      hsame family family' ->
      hsame lower lower' ->
      hsame greatest greatest' ->
      hsame window window' ->
      hsame regseq regseq' ->
      hsame realSeal realSeal' ->
      Cont family' lower' lowerRead ->
      Cont lowerRead greatest' stableRead ->
      Cont stableRead realSeal' sealRead ->
      PkgSig bundle sealRead pkg ->
      UnaryHistory family' ∧ UnaryHistory lower' ∧ UnaryHistory greatest' ∧
        UnaryHistory window' ∧ UnaryHistory regseq' ∧ UnaryHistory realSeal' ∧
          UnaryHistory lowerRead ∧ UnaryHistory stableRead ∧ UnaryHistory sealRead ∧
            Cont family' lower' lowerRead ∧ Cont lowerRead greatest' stableRead ∧
              Cont stableRead realSeal' sealRead ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame
  intro carrier familySame lowerSame greatestSame windowSame regseqSame realSealSame
    familyLower lowerGreatest stableSeal sealPkg
  obtain ⟨familyUnary, lowerUnary, greatestUnary, windowUnary, regseqUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _regseqRealSealRoute,
    _provenancePkg, _namePkg⟩ := carrier
  have familyPrimeUnary : UnaryHistory family' :=
    unary_transport familyUnary familySame
  have lowerPrimeUnary : UnaryHistory lower' :=
    unary_transport lowerUnary lowerSame
  have greatestPrimeUnary : UnaryHistory greatest' :=
    unary_transport greatestUnary greatestSame
  have windowPrimeUnary : UnaryHistory window' :=
    unary_transport windowUnary windowSame
  have regseqPrimeUnary : UnaryHistory regseq' :=
    unary_transport regseqUnary regseqSame
  have realSealPrimeUnary : UnaryHistory realSeal' :=
    unary_transport realSealUnary realSealSame
  have lowerReadUnary : UnaryHistory lowerRead :=
    unary_cont_closed familyPrimeUnary lowerPrimeUnary familyLower
  have stableReadUnary : UnaryHistory stableRead :=
    unary_cont_closed lowerReadUnary greatestPrimeUnary lowerGreatest
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed stableReadUnary realSealPrimeUnary stableSeal
  exact
    ⟨familyPrimeUnary, lowerPrimeUnary, greatestPrimeUnary, windowPrimeUnary,
      regseqPrimeUnary, realSealPrimeUnary, lowerReadUnary, stableReadUnary, sealReadUnary,
      familyLower, lowerGreatest, stableSeal, sealPkg⟩

end BEDC.Derived.LocatedInfimumUp
