import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathFourFaceConfluenceBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadic stream regseq realSeal confluenceRead boundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont route localName dyadic ->
        Cont dyadic localName stream ->
          Cont stream localName regseq ->
            Cont regseq localName realSeal ->
              Cont realSeal handoff confluenceRead ->
                Cont confluenceRead obstruction boundedRead ->
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                          hsame row realSeal ∨ hsame row confluenceRead ∨
                            hsame row boundedRead) ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                          hsame row realSeal ∨ hsame row confluenceRead ∨
                            hsame row boundedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧
                          (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                            hsame row realSeal ∨ hsame row confluenceRead ∨
                              hsame row boundedRead))
                      hsame ∧
                    UnaryHistory boundedRead ∧ Cont handoff obstruction dischargeSocket := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro packet routeLocalDyadic dyadicLocalStream streamLocalRegseq regseqLocalSeal
    sealHandoffConfluence confluenceObstructionBounded
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have dyadicUnary : UnaryHistory dyadic :=
    unary_cont_closed routeUnary localNameUnary routeLocalDyadic
  have streamUnary : UnaryHistory stream :=
    unary_cont_closed dyadicUnary localNameUnary dyadicLocalStream
  have regseqUnary : UnaryHistory regseq :=
    unary_cont_closed streamUnary localNameUnary streamLocalRegseq
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqUnary localNameUnary regseqLocalSeal
  have confluenceUnary : UnaryHistory confluenceRead :=
    unary_cont_closed realSealUnary handoffUnary sealHandoffConfluence
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed confluenceUnary obstructionUnary confluenceObstructionBounded
  have sourceBounded :
      (fun row : BHist =>
        (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
          hsame row realSeal ∨ hsame row confluenceRead ∨ hsame row boundedRead) ∧
          UnaryHistory row) boundedRead := by
    exact
      ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl boundedRead))))),
        boundedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row confluenceRead ∨ hsame row boundedRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row confluenceRead ∨ hsame row boundedRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                hsame row realSeal ∨ hsame row confluenceRead ∨ hsame row boundedRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundedRead sourceBounded
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
        constructor
        · cases source.left with
          | inl sameDyadic =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameDyadic)
          | inr rest =>
              cases rest with
              | inl sameStream =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameStream))
              | inr rest =>
                  cases rest with
                  | inl sameRegseq =>
                      exact
                        Or.inr (Or.inr (Or.inl
                          (hsame_trans (hsame_symm sameRows) sameRegseq)))
                  | inr rest =>
                      cases rest with
                      | inl sameSeal =>
                          exact
                            Or.inr (Or.inr (Or.inr (Or.inl
                              (hsame_trans (hsame_symm sameRows) sameSeal))))
                      | inr rest =>
                          cases rest with
                          | inl sameConfluence =>
                              exact
                                Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                                  (hsame_trans (hsame_symm sameRows) sameConfluence)))))
                          | inr sameBounded =>
                              exact
                                Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                  (hsame_trans (hsame_symm sameRows) sameBounded)))))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, source.left⟩
  }
  exact ⟨cert, boundedUnary, handoffObstructionSocket⟩

end BEDC.Derived.MetaCICCriticalPathUp
