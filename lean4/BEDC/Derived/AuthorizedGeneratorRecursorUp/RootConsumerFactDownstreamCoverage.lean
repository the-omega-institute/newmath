import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootConsumerFactDownstreamCoverage [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead publicRead outputRead auditRead boundaryRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont B D branchRead →
        Cont branchRead C publicRead →
          Cont O A outputRead →
            Cont outputRead N auditRead →
              Cont G N boundaryRead →
                PkgSig bundle publicRead pkg →
                  PkgSig bundle auditRead pkg →
                    SemanticNameCert
                        (fun row : BHist =>
                          (hsame row publicRead ∨ hsame row auditRead ∨
                              hsame row boundaryRead) ∧
                            UnaryHistory row)
                        (fun row : BHist =>
                          hsame row I ∨ hsame row B ∨ hsame row D ∨ hsame row O ∨
                            hsame row A ∨ hsame row G ∨ hsame row N ∨
                              hsame row publicRead ∨ hsame row auditRead ∨
                                hsame row boundaryRead)
                        (fun row : BHist =>
                          (hsame row publicRead ∨ hsame row auditRead ∨
                              hsame row boundaryRead) ∧
                            PkgSig bundle P pkg)
                        hsame ∧
                      UnaryHistory publicRead ∧ UnaryHistory auditRead ∧
                        UnaryHistory boundaryRead ∧ hsame H (append A C) ∧
                          PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier branchRoute publicRoute outputRoute auditRoute boundaryRoute _publicPkg _auditPkg
  rcases carrier with
    ⟨unaryI, _unaryE, _unaryM, unaryB, unaryD, unaryO, unaryA, _unaryH, unaryC,
      provenancePkg, unaryG, unaryN, _carrierBranch, _carrierDescent, _carrierOutput,
      transportSame, provenanceSig⟩
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryB unaryD branchRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed branchReadUnary unaryC publicRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary unaryN auditRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryG unaryN boundaryRoute
  have sourcePublic :
      (fun row : BHist =>
        (hsame row publicRead ∨ hsame row auditRead ∨ hsame row boundaryRead) ∧
          UnaryHistory row) publicRead := by
    exact ⟨Or.inl (hsame_refl publicRead), publicReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row publicRead ∨ hsame row auditRead ∨ hsame row boundaryRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row B ∨ hsame row D ∨ hsame row O ∨ hsame row A ∨
              hsame row G ∨ hsame row N ∨ hsame row publicRead ∨
                hsame row auditRead ∨ hsame row boundaryRead)
          (fun row : BHist =>
            (hsame row publicRead ∨ hsame row auditRead ∨ hsame row boundaryRead) ∧
              PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        rcases source with ⟨surface, unaryRow⟩
        refine ⟨?_, unary_transport unaryRow same⟩
        rcases surface with samePublic | sameAudit | sameBoundary
        · exact Or.inl (hsame_trans (hsame_symm same) samePublic)
        · exact Or.inr (Or.inl (hsame_trans (hsame_symm same) sameAudit))
        · exact Or.inr (Or.inr (hsame_trans (hsame_symm same) sameBoundary))
    }
    pattern_sound := by
      intro row source
      rcases source.left with samePublic | sameAudit | sameBoundary
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl samePublic)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl sameAudit))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr sameBoundary))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenanceSig⟩
  }
  have _carrierWitness : UnaryHistory I ∧ PkgSig bundle P pkg :=
    ⟨unaryI, provenanceSig⟩
  have _provenanceUnary : UnaryHistory P := provenancePkg
  exact
    ⟨cert, publicReadUnary, auditReadUnary, boundaryReadUnary, transportSame,
      provenanceSig⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
