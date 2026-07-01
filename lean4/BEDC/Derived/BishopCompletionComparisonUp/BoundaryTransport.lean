import BEDC.Derived.BishopCompletionComparisonUp
import BEDC.Derived.BishopCompletionComparisonUp.RealRoute

namespace BEDC.Derived.BishopCompletionComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopCompletionComparisonCarrier_boundary_transport [AskSetup] [PackageSetup]
    {regular boundary located enclosure sealRow transport replay provenance localName midRead
      sealRead auditRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopCompletionComparisonCarrier regular boundary located enclosure sealRow transport replay
        provenance localName bundle pkg →
      Cont regular boundary midRead →
        Cont midRead located enclosure →
          Cont enclosure sealRow sealRead →
            Cont provenance localName auditRead →
              Cont auditRead sealRow realRead →
                PkgSig bundle realRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row regular ∨ hsame row boundary ∨ hsame row located ∨
                          hsame row enclosure ∨ hsame row sealRow ∨ hsame row transport ∨
                            hsame row replay ∨ hsame row realRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont regular boundary midRead ∧
                          Cont midRead located enclosure ∧ Cont enclosure sealRow sealRead ∧
                            PkgSig bundle realRead pkg)
                      hsame ∧
                    UnaryHistory midRead ∧ UnaryHistory sealRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier regularBoundary midLocated enclosureSeal provenanceAudit auditReal realPkg
  obtain ⟨regularUnary, boundaryUnary, locatedUnary, _enclosureUnary, sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, localNameUnary, _provenancePkg,
    _localNamePkg⟩ := carrier
  have midReadUnary : UnaryHistory midRead :=
    unary_cont_closed regularUnary boundaryUnary regularBoundary
  have enclosureUnary : UnaryHistory enclosure :=
    unary_cont_closed midReadUnary locatedUnary midLocated
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed enclosureUnary sealUnary enclosureSeal
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed provenanceUnary localNameUnary provenanceAudit
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed auditReadUnary sealUnary auditReal
  have realSource :
      (fun row : BHist => hsame row realRead ∧ UnaryHistory row) realRead := by
    exact ⟨hsame_refl realRead, realReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row regular ∨ hsame row boundary ∨ hsame row located ∨
              hsame row enclosure ∨ hsame row sealRow ∨ hsame row transport ∨
                hsame row replay ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont regular boundary midRead ∧
              Cont midRead located enclosure ∧ Cont enclosure sealRow sealRead ∧
                PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead realSource
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, regularBoundary, midLocated, enclosureSeal, realPkg⟩
  }
  exact ⟨cert, midReadUnary, sealReadUnary, realReadUnary⟩

theorem BishopCompletionComparisonCarrier_boundary_real_nonescape [AskSetup] [PackageSetup]
    {regular boundary locatedLimit locatedReal realSeal replayToBoundary replayToLimit
      replayToLocated provenance localName transport replay auditRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory regular ->
      UnaryHistory boundary ->
        UnaryHistory locatedLimit ->
          UnaryHistory locatedReal ->
            UnaryHistory localName ->
              BishopCompletionComparisonCarrier regular boundary locatedLimit locatedReal realSeal
                  transport replay provenance localName bundle pkg ->
                Cont regular boundary replayToBoundary ->
                  Cont replayToBoundary locatedLimit replayToLimit ->
                    Cont replayToLimit locatedReal replayToLocated ->
                      Cont replayToLocated localName realSeal ->
                        Cont transport replay provenance ->
                          Cont provenance localName auditRead ->
                            Cont auditRead realSeal realRead ->
                              PkgSig bundle realRead pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row regular ∨ hsame row boundary ∨
                                        hsame row locatedLimit ∨ hsame row locatedReal ∨
                                          hsame row realSeal ∨ hsame row transport ∨
                                            hsame row replay ∨ hsame row provenance ∨
                                              hsame row localName ∨ hsame row realRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont transport replay provenance ∧
                                        Cont provenance localName auditRead ∧
                                          Cont auditRead realSeal realRead ∧
                                            PkgSig bundle realRead pkg)
                                    hsame ∧
                                  SemanticNameCert
                                      (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row regular ∨ hsame row boundary ∨
                                          hsame row locatedLimit ∨ hsame row locatedReal ∨
                                            hsame row realSeal ∨ hsame row replayToBoundary ∨
                                              hsame row replayToLimit ∨
                                                hsame row replayToLocated ∨
                                                  hsame row provenance ∨ hsame row localName)
                                      (fun row : BHist =>
                                        hsame row realSeal ∧
                                          Cont replayToLocated localName realSeal)
                                      hsame ∧
                                    UnaryHistory replayToBoundary ∧
                                      UnaryHistory replayToLimit ∧
                                        UnaryHistory replayToLocated ∧ UnaryHistory realSeal ∧
                                          UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro regularUnary boundaryUnary locatedLimitUnary locatedRealUnary localNameUnary carrier
    boundaryRoute limitRoute locatedRoute sealRoute transportReplay provenanceAudit auditReal
    realPkg
  have sealNonescape :=
    BishopCompletionComparisonCarrier_seal_nonescape (regular := regular) (boundary := boundary)
      (locatedLimit := locatedLimit) (locatedReal := locatedReal) (realSeal := realSeal)
      (replayToBoundary := replayToBoundary) (replayToLimit := replayToLimit)
      (replayToLocated := replayToLocated) (provenance := provenance) (localName := localName)
      regularUnary boundaryUnary locatedLimitUnary locatedRealUnary localNameUnary boundaryRoute
      limitRoute locatedRoute sealRoute
  have realRoute :=
    BishopCompletionComparisonCarrier_real_route carrier transportReplay provenanceAudit auditReal
      realPkg
  exact
    ⟨realRoute.left, sealNonescape.left, sealNonescape.right.left,
      sealNonescape.right.right.left, sealNonescape.right.right.right.left,
      sealNonescape.right.right.right.right, realRoute.right.right⟩

end BEDC.Derived.BishopCompletionComparisonUp
