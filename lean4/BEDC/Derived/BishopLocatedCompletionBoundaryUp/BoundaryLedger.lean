import BEDC.Derived.BishopLocatedCompletionBoundaryUp.RegularCauchyExtraction

namespace BEDC.Derived.BishopLocatedCompletionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopLocatedCompletionBoundaryLedger [AskSetup] [PackageSetup]
    {regular locatedLimit realSeal boundary transport replay provenance localName ledgerRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory regular →
      UnaryHistory locatedLimit →
        UnaryHistory realSeal →
          UnaryHistory boundary →
            UnaryHistory transport →
              UnaryHistory replay →
                UnaryHistory provenance →
                  UnaryHistory localName →
                    Cont regular locatedLimit realSeal →
                      Cont realSeal boundary ledgerRead →
                        PkgSig bundle provenance pkg →
                          PkgSig bundle ledgerRead pkg →
                            UnaryHistory regular ∧ UnaryHistory locatedLimit ∧
                              UnaryHistory realSeal ∧ UnaryHistory boundary ∧
                                UnaryHistory ledgerRead ∧
                                  Cont regular locatedLimit realSeal ∧
                                    Cont realSeal boundary ledgerRead ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BishopLocatedCompletionBoundaryUp BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro regularUnary locatedLimitUnary realSealUnary boundaryUnary _transportUnary
    _replayUnary _provenanceUnary _localNameUnary sealRoute ledgerRoute provenancePkg ledgerPkg
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed realSealUnary boundaryUnary ledgerRoute
  exact
    ⟨regularUnary, locatedLimitUnary, realSealUnary, boundaryUnary, ledgerUnary, sealRoute,
      ledgerRoute, provenancePkg, ledgerPkg⟩

end BEDC.Derived.BishopLocatedCompletionBoundaryUp
