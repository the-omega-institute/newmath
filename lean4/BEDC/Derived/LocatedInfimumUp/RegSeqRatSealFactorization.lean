import BEDC.Derived.LocatedInfimumUp

namespace BEDC.Derived.LocatedInfimumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedInfimumRegSeqRatSealFactorization [AskSetup] [PackageSetup]
    {family lower greatest window regseq realSeal transport route provenance name sealRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedInfimumCarrier family lower greatest window regseq realSeal transport route provenance
        name bundle pkg →
      Cont window regseq sealRead →
        Cont regseq realSeal route →
          PkgSig bundle provenance pkg →
            UnaryHistory family ∧ UnaryHistory lower ∧ UnaryHistory greatest ∧
              UnaryHistory window ∧ UnaryHistory regseq ∧ UnaryHistory realSeal ∧
                UnaryHistory sealRead ∧ Cont window regseq sealRead ∧
                  Cont regseq realSeal route ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory LocatedInfimumCarrier
  intro carrier windowRegseqSealRead regseqRealSealRoute provenancePkg
  obtain ⟨familyUnary, lowerUnary, greatestUnary, windowUnary, regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _storedRegseqRealSealRoute, _storedProvenancePkg, _storedNamePkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary regseqUnary windowRegseqSealRead
  exact
    ⟨familyUnary, lowerUnary, greatestUnary, windowUnary, regseqUnary, realSealUnary,
      sealReadUnary, windowRegseqSealRead, regseqRealSealRoute, provenancePkg⟩

end BEDC.Derived.LocatedInfimumUp
