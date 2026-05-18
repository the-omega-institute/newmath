import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AxiomDependencyTupleCarrier [AskSetup] [PackageSetup]
    (mode witness supply transport route provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  (((hsame mode BHist.Empty ∧ UnaryHistory witness) ∨
      (hsame mode (BHist.e0 BHist.Empty) ∧ UnaryHistory supply)) ∨
        (hsame mode (BHist.e1 BHist.Empty) ∧ UnaryHistory supply)) ∧
    UnaryHistory mode ∧ UnaryHistory witness ∧ UnaryHistory supply ∧
      UnaryHistory localCert ∧ Cont witness supply transport ∧ Cont transport route provenance ∧
        PkgSig bundle provenance pkg

theorem AxiomDependencyTupleModeExhaustion [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localCert modeRead supplyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localCert
        bundle pkg →
      Cont mode supply modeRead →
        Cont supply localCert supplyRead →
          PkgSig bundle supplyRead pkg →
            ((hsame mode BHist.Empty ∧ UnaryHistory witness) ∨
              (hsame mode (BHist.e0 BHist.Empty) ∧ UnaryHistory supply) ∨
                (hsame mode (BHist.e1 BHist.Empty) ∧ UnaryHistory supply)) ∧
              UnaryHistory modeRead ∧ UnaryHistory supplyRead ∧ Cont mode supply modeRead ∧
                Cont supply localCert supplyRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle supplyRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier modeSupplyRead supplyLocalRead supplyReadPkg
  rcases carrier with
    ⟨modeCases, modeUnary, _witnessUnary, supplyUnary, localCertUnary, _witnessSupplyTransport,
      _transportRouteProvenance, provenancePkg⟩
  cases modeCases with
  | inl zeroOrRestricted =>
      cases zeroOrRestricted with
      | inl zeroMode =>
          have modeReadUnary : UnaryHistory modeRead :=
            unary_cont_closed modeUnary supplyUnary modeSupplyRead
          have supplyReadUnary : UnaryHistory supplyRead :=
            unary_cont_closed supplyUnary localCertUnary supplyLocalRead
          exact
            ⟨Or.inl zeroMode, modeReadUnary, supplyReadUnary, modeSupplyRead,
              supplyLocalRead, provenancePkg, supplyReadPkg⟩
      | inr restrictedMode =>
          cases restrictedMode.left
          cases modeUnary
  | inr socketMode =>
      have modeReadUnary : UnaryHistory modeRead :=
        unary_cont_closed modeUnary supplyUnary modeSupplyRead
      have supplyReadUnary : UnaryHistory supplyRead :=
        unary_cont_closed supplyUnary localCertUnary supplyLocalRead
      exact
        ⟨Or.inr (Or.inr socketMode), modeReadUnary, supplyReadUnary, modeSupplyRead,
          supplyLocalRead, provenancePkg, supplyReadPkg⟩

end BEDC.Derived.AxiomDependencyTupleUp
