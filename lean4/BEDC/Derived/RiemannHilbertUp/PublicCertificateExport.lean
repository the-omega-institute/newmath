import BEDC.Derived.RiemannHilbertUp

namespace BEDC.Derived.RiemannHilbertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RiemannHilbertBHistBridgePacket_public_certificate_export
    [AskSetup] [PackageSetup]
    {derivedSource sheafTarget regularBranch deRhamReadback localSystem gluing transport
      provenance endpoint publicBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannHilbertBHistBridgePacket derivedSource sheafTarget regularBranch deRhamReadback
        localSystem gluing transport provenance endpoint bundle pkg ->
      Cont endpoint localSystem publicBoundary ->
        SemanticNameCert
            (fun row : BHist =>
              UnaryHistory row ∧ (hsame row endpoint ∨ hsame row publicBoundary))
            (fun row : BHist =>
              UnaryHistory row ∧ (hsame row endpoint ∨ hsame row publicBoundary))
            (fun row : BHist =>
              UnaryHistory row ∧ (hsame row endpoint ∨ hsame row publicBoundary))
            (fun row other : BHist =>
              (UnaryHistory row ∧ (hsame row endpoint ∨ hsame row publicBoundary)) ∧
                (UnaryHistory other ∧ (hsame other endpoint ∨ hsame other publicBoundary)) ∧
                  hsame row other) ∧
          UnaryHistory publicBoundary ∧
            hsame deRhamReadback (append derivedSource sheafTarget) ∧
              hsame gluing (append (append derivedSource sheafTarget) localSystem) ∧
                hsame endpoint
                    (append
                      (append regularBranch
                        (append (append derivedSource sheafTarget) localSystem))
                      provenance) ∧
                  hsame publicBoundary (append endpoint localSystem) ∧
                    PkgSig bundle endpoint pkg := by
  intro packet publicBoundaryCont
  have derivedUnary : UnaryHistory derivedSource := packet.left
  have sheafUnary : UnaryHistory sheafTarget := packet.right.left
  have regularUnary : UnaryHistory regularBranch := packet.right.right.left
  have localUnary : UnaryHistory localSystem := packet.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.right.left
  have deRhamCont : Cont derivedSource sheafTarget deRhamReadback :=
    packet.right.right.right.right.right.left
  have gluingCont : Cont deRhamReadback localSystem gluing :=
    packet.right.right.right.right.right.right.left
  have transportCont : Cont regularBranch gluing transport :=
    packet.right.right.right.right.right.right.right.left
  have endpointCont : Cont transport provenance endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right
  have deRhamUnary : UnaryHistory deRhamReadback :=
    unary_cont_closed derivedUnary sheafUnary deRhamCont
  have gluingUnary : UnaryHistory gluing :=
    unary_cont_closed deRhamUnary localUnary gluingCont
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed regularUnary gluingUnary transportCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed transportUnary provenanceUnary endpointCont
  have publicBoundaryUnary : UnaryHistory publicBoundary :=
    unary_cont_closed endpointUnary localUnary publicBoundaryCont
  have semantic :
      SemanticNameCert
        (fun row : BHist =>
          UnaryHistory row ∧ (hsame row endpoint ∨ hsame row publicBoundary))
        (fun row : BHist =>
          UnaryHistory row ∧ (hsame row endpoint ∨ hsame row publicBoundary))
        (fun row : BHist =>
          UnaryHistory row ∧ (hsame row endpoint ∨ hsame row publicBoundary))
        (fun row other : BHist =>
          (UnaryHistory row ∧ (hsame row endpoint ∨ hsame row publicBoundary)) ∧
            (UnaryHistory other ∧ (hsame other endpoint ∨ hsame other publicBoundary)) ∧
              hsame row other) := by
    constructor
    · constructor
      · exact Exists.intro endpoint ⟨endpointUnary, Or.inl (hsame_refl endpoint)⟩
      · intro row carrier
        exact ⟨carrier, carrier, hsame_refl row⟩
      · intro row other classified
        exact ⟨classified.right.left, classified.left, hsame_symm classified.right.right⟩
      · intro row other third leftClass rightClass
        exact
          ⟨leftClass.left, rightClass.right.left,
            hsame_trans leftClass.right.right rightClass.right.right⟩
      · intro row other classified _carrier
        exact classified.right.left
    · intro _row source
      exact source
    · intro _row source
      exact source
  have deRhamReadbackRow : hsame deRhamReadback (append derivedSource sheafTarget) :=
    deRhamCont
  have gluingRow : hsame gluing (append (append derivedSource sheafTarget) localSystem) := by
    cases deRhamCont
    exact gluingCont
  have endpointRow :
      hsame endpoint
        (append
          (append regularBranch (append (append derivedSource sheafTarget) localSystem))
          provenance) := by
    cases deRhamCont
    cases gluingCont
    cases transportCont
    cases endpointCont
    rfl
  exact
    ⟨semantic,
      publicBoundaryUnary,
      deRhamReadbackRow,
      gluingRow,
      endpointRow,
      publicBoundaryCont,
      pkgSig⟩

end BEDC.Derived.RiemannHilbertUp
