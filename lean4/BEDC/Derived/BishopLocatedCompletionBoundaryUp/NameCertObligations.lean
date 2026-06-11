import BEDC.Derived.BishopLocatedCompletionBoundaryUp.RegularCauchyExtraction

namespace BEDC.Derived.BishopLocatedCompletionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopLocatedCompletionBoundaryNameCertObligations [AskSetup] [PackageSetup]
    {stream regular dyadic regularLocated locatedLimit locatedReal realSeal transport replay
      provenance localName streamRegularRead dyadicRead extractionRead locatedRead
      enclosureRead sealRead : BHist}
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
                                Cont extractionRead locatedLimit locatedRead →
                                  Cont locatedRead locatedReal enclosureRead →
                                    Cont enclosureRead realSeal sealRead →
                                      PkgSig bundle provenance pkg →
                                        PkgSig bundle localName pkg →
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row sealRead ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row stream ∨ hsame row regular ∨
                                                  hsame row dyadic ∨
                                                    hsame row regularLocated ∨
                                                      hsame row locatedLimit ∨
                                                        hsame row locatedReal ∨
                                                          hsame row realSeal ∨
                                                            hsame row sealRead)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧
                                                  Cont stream regular streamRegularRead ∧
                                                    Cont streamRegularRead dyadic
                                                      dyadicRead ∧
                                                      Cont dyadicRead regularLocated
                                                        extractionRead ∧
                                                        Cont extractionRead locatedLimit
                                                          locatedRead ∧
                                                          Cont locatedRead locatedReal
                                                            enclosureRead ∧
                                                            Cont enclosureRead realSeal
                                                              sealRead ∧
                                                              PkgSig bundle provenance
                                                                pkg ∧
                                                                PkgSig bundle localName
                                                                  pkg)
                                              hsame ∧
                                            UnaryHistory streamRegularRead ∧
                                              UnaryHistory dyadicRead ∧
                                                UnaryHistory extractionRead ∧
                                                  UnaryHistory locatedRead ∧
                                                    UnaryHistory enclosureRead ∧
                                                      UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BishopLocatedCompletionBoundaryUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro streamUnary regularUnary dyadicUnary regularLocatedUnary locatedLimitUnary
    locatedRealUnary realSealUnary _transportUnary _replayUnary _provenanceUnary
    _localNameUnary streamRegularRoute dyadicRoute extractionRoute locatedRoute
    enclosureRoute sealRoute provenancePkg localNamePkg
  have streamRegularUnary : UnaryHistory streamRegularRead :=
    unary_cont_closed streamUnary regularUnary streamRegularRoute
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed streamRegularUnary dyadicUnary dyadicRoute
  have extractionUnary : UnaryHistory extractionRead :=
    unary_cont_closed dyadicReadUnary regularLocatedUnary extractionRoute
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed extractionUnary locatedLimitUnary locatedRoute
  have enclosureReadUnary : UnaryHistory enclosureRead :=
    unary_cont_closed locatedReadUnary locatedRealUnary enclosureRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed enclosureReadUnary realSealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row regular ∨ hsame row dyadic ∨
              hsame row regularLocated ∨ hsame row locatedLimit ∨ hsame row locatedReal ∨
                hsame row realSeal ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont stream regular streamRegularRead ∧
              Cont streamRegularRead dyadic dyadicRead ∧
                Cont dyadicRead regularLocated extractionRead ∧
                  Cont extractionRead locatedLimit locatedRead ∧
                    Cont locatedRead locatedReal enclosureRead ∧
                      Cont enclosureRead realSeal sealRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, streamRegularRoute, dyadicRoute, extractionRoute, locatedRoute,
          enclosureRoute, sealRoute, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, streamRegularUnary, dyadicReadUnary, extractionUnary, locatedReadUnary,
      enclosureReadUnary, sealReadUnary⟩

end BEDC.Derived.BishopLocatedCompletionBoundaryUp
