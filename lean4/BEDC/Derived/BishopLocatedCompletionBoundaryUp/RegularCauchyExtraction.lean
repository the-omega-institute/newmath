import BEDC.Derived.BishopLocatedCompletionBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopLocatedCompletionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BishopLocatedCompletionBoundaryCarrier [AskSetup] [PackageSetup]
    (stream regseq dyadic regular locatedLimit locatedReal realSeal transport route
      provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BishopLocatedCompletionBoundaryUp BHist ProbeBundle Pkg PkgSig UnaryHistory Cont
  UnaryHistory stream ∧ UnaryHistory regseq ∧ UnaryHistory dyadic ∧
    UnaryHistory regular ∧ UnaryHistory locatedLimit ∧ UnaryHistory locatedReal ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory route ∧
        UnaryHistory provenance ∧ UnaryHistory name ∧ Cont stream regseq dyadic ∧
          Cont dyadic regular locatedLimit ∧ Cont locatedLimit locatedReal realSeal ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem BishopLocatedCompletionBoundaryRegularCauchyExtraction [AskSetup] [PackageSetup]
    {stream regular dyadic regularLocated locatedLimit locatedReal realSeal transport replay
      provenance localName streamRegularRead dyadicRead extractionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory stream →
      UnaryHistory regular →
        UnaryHistory dyadic →
          UnaryHistory regularLocated →
            UnaryHistory locatedLimit →
              UnaryHistory locatedReal →
                UnaryHistory realSeal →
                  UnaryHistory transport →
                    UnaryHistory replay →
                      UnaryHistory provenance →
                        UnaryHistory localName →
                          Cont stream regular streamRegularRead →
                            Cont streamRegularRead dyadic dyadicRead →
                              Cont dyadicRead regularLocated extractionRead →
                                PkgSig bundle provenance pkg →
                                  PkgSig bundle localName pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row extractionRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row stream ∨ hsame row regular ∨
                                            hsame row dyadic ∨ hsame row regularLocated ∨
                                              hsame row extractionRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧
                                            Cont stream regular streamRegularRead ∧
                                              Cont streamRegularRead dyadic dyadicRead ∧
                                                Cont dyadicRead regularLocated
                                                  extractionRead ∧
                                                  PkgSig bundle provenance pkg ∧
                                                    PkgSig bundle localName pkg)
                                        hsame ∧
                                      UnaryHistory streamRegularRead ∧
                                        UnaryHistory dyadicRead ∧
                                          UnaryHistory extractionRead := by
  -- BEDC touchpoint anchor: BishopLocatedCompletionBoundaryUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro streamUnary regularUnary dyadicUnary regularLocatedUnary _locatedLimitUnary
    _locatedRealUnary _realSealUnary _transportUnary _replayUnary _provenanceUnary
    _localNameUnary streamRegularRoute dyadicRoute extractionRoute provenancePkg localNamePkg
  have streamRegularUnary : UnaryHistory streamRegularRead :=
    unary_cont_closed streamUnary regularUnary streamRegularRoute
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed streamRegularUnary dyadicUnary dyadicRoute
  have extractionUnary : UnaryHistory extractionRead :=
    unary_cont_closed dyadicReadUnary regularLocatedUnary extractionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row extractionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row regular ∨ hsame row dyadic ∨
              hsame row regularLocated ∨ hsame row extractionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont stream regular streamRegularRead ∧
              Cont streamRegularRead dyadic dyadicRead ∧
                Cont dyadicRead regularLocated extractionRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro extractionRead ⟨hsame_refl extractionRead, extractionUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, streamRegularRoute, dyadicRoute, extractionRoute,
          provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, streamRegularUnary, dyadicReadUnary, extractionUnary⟩

theorem BishopLocatedCompletionBoundaryLocatedLimitRoute [AskSetup] [PackageSetup]
    {stream regseq dyadic regular locatedLimit locatedReal realSeal transport route
      provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopLocatedCompletionBoundaryCarrier stream regseq dyadic regular locatedLimit locatedReal
        realSeal transport route provenance name bundle pkg →
      Cont locatedReal realSeal endpoint →
        PkgSig bundle endpoint pkg →
          UnaryHistory stream ∧ UnaryHistory regseq ∧ UnaryHistory dyadic ∧
            UnaryHistory regular ∧ UnaryHistory locatedLimit ∧ UnaryHistory locatedReal ∧
              UnaryHistory realSeal ∧ UnaryHistory endpoint ∧ Cont stream regseq dyadic ∧
                Cont dyadic regular locatedLimit ∧ Cont locatedLimit locatedReal realSeal ∧
                  Cont locatedReal realSeal endpoint ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BishopLocatedCompletionBoundaryCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier endpointRoute endpointPkg
  obtain ⟨streamUnary, regseqUnary, dyadicUnary, regularUnary, locatedLimitUnary,
    locatedRealUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _nameUnary, streamRegseqDyadic, dyadicRegularLocatedLimit,
    locatedLimitLocatedRealRealSeal, provenancePkg, _namePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed locatedRealUnary realSealUnary endpointRoute
  exact
    ⟨streamUnary, regseqUnary, dyadicUnary, regularUnary, locatedLimitUnary,
      locatedRealUnary, realSealUnary, endpointUnary, streamRegseqDyadic,
      dyadicRegularLocatedLimit, locatedLimitLocatedRealRealSeal, endpointRoute,
      provenancePkg, endpointPkg⟩

end BEDC.Derived.BishopLocatedCompletionBoundaryUp
