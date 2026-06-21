import BEDC.Derived.LocatedInfimumUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedInfimumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedInfimumBoundedFamilyHandoff [AskSetup] [PackageSetup]
    {family lower greatest window regseq realSeal transport route provenance name familyRead
      witnessRead boundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedInfimumCarrier family lower greatest window regseq realSeal transport route provenance
        name bundle pkg →
      Cont family lower familyRead →
        Cont familyRead greatest witnessRead →
          Cont witnessRead window boundedRead →
            PkgSig bundle boundedRead pkg →
              UnaryHistory familyRead ∧ UnaryHistory witnessRead ∧
                UnaryHistory boundedRead ∧ Cont family lower familyRead ∧
                  Cont familyRead greatest witnessRead ∧ Cont witnessRead window boundedRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle boundedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier familyRoute witnessRoute boundedRoute boundedPkg
  obtain ⟨familyUnary, lowerUnary, greatestUnary, windowUnary, _regseqUnary, _realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _regseqRealSealRoute,
    provenancePkg, _namePkg⟩ := carrier
  have familyReadUnary : UnaryHistory familyRead :=
    unary_cont_closed familyUnary lowerUnary familyRoute
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed familyReadUnary greatestUnary witnessRoute
  have boundedReadUnary : UnaryHistory boundedRead :=
    unary_cont_closed witnessReadUnary windowUnary boundedRoute
  exact
    ⟨familyReadUnary, witnessReadUnary, boundedReadUnary, familyRoute, witnessRoute,
      boundedRoute, provenancePkg, boundedPkg⟩

end BEDC.Derived.LocatedInfimumUp
