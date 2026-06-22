import BEDC.Derived.FiniteCoverNerveUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteCoverNerveUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteCoverNerveCarrier [AskSetup] [PackageSetup]
    (cover member overlap face radius fold uniform transport replay provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory cover ∧ UnaryHistory member ∧ UnaryHistory overlap ∧
    UnaryHistory face ∧ UnaryHistory radius ∧ UnaryHistory fold ∧
      UnaryHistory uniform ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory name ∧ Cont cover member overlap ∧
          Cont overlap face radius ∧ Cont radius fold uniform ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem FiniteCoverNerveCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {K V O F R B U H C P Q : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory K ->
      UnaryHistory V ->
        UnaryHistory O ->
          UnaryHistory F ->
            UnaryHistory R ->
              UnaryHistory B ->
                UnaryHistory U ->
                  UnaryHistory H ->
                    UnaryHistory C ->
                      UnaryHistory P ->
                        UnaryHistory Q ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle Q pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row Q ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row K ∨ hsame row V ∨ hsame row O ∨
                                      hsame row F ∨ hsame row R ∨ hsame row B ∨
                                        hsame row U ∨ hsame row H ∨ hsame row C ∨
                                          hsame row P ∨ hsame row Q)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle Q pkg)
                                  hsame ∧ UnaryHistory K ∧ UnaryHistory V ∧
                                UnaryHistory O ∧ UnaryHistory F ∧ UnaryHistory R ∧
                                  UnaryHistory B ∧ UnaryHistory U := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig hsame SemanticNameCert
  intro kUnary vUnary oUnary fUnary rUnary bUnary uUnary _hUnary _cUnary _pUnary qUnary
    provenancePkg localPkg
  have sourceLocal :
      (fun row : BHist => hsame row Q ∧ UnaryHistory row) Q := by
    exact ⟨hsame_refl Q, qUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row Q ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row V ∨ hsame row O ∨ hsame row F ∨ hsame row R ∨
              hsame row B ∨ hsame row U ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row Q)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle Q pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro Q sourceLocal
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, provenancePkg, localPkg⟩
  }
  exact ⟨cert, kUnary, vUnary, oUnary, fUnary, rUnary, bUnary, uUnary⟩

theorem FiniteCoverNerveVisionRealization [AskSetup] [PackageSetup]
    {cover member overlap face radius fold uniform transport replay provenance name visionRead
      realizationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteCoverNerveCarrier cover member overlap face radius fold uniform transport replay
        provenance name bundle pkg ->
      Cont cover member visionRead ->
        Cont visionRead uniform realizationRead ->
          PkgSig bundle realizationRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row realizationRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row cover ∨ hsame row member ∨ hsame row overlap ∨ hsame row face ∨
                    hsame row radius ∨ hsame row fold ∨ hsame row uniform ∨
                      hsame row realizationRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont cover member visionRead ∧
                    Cont visionRead uniform realizationRead ∧ PkgSig bundle realizationRead pkg)
                hsame ∧
              UnaryHistory visionRead ∧ UnaryHistory realizationRead := by
  -- BEDC touchpoint anchor: FiniteCoverNerveCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro nerveCarrier coverMemberVision visionUniformRealization realizationPkg
  obtain ⟨coverUnary, memberUnary, overlapUnary, faceUnary, radiusUnary, foldUnary,
    uniformUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _coverMemberOverlap, _overlapFaceRadius, _radiusFoldUniform, _provenancePkg,
    _namePkg⟩ := nerveCarrier
  have visionUnary : UnaryHistory visionRead :=
    unary_cont_closed coverUnary memberUnary coverMemberVision
  have realizationUnary : UnaryHistory realizationRead :=
    unary_cont_closed visionUnary uniformUnary visionUniformRealization
  have sourceRealization :
      (fun row : BHist => hsame row realizationRead ∧ UnaryHistory row) realizationRead := by
    exact ⟨hsame_refl realizationRead, realizationUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realizationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row member ∨ hsame row overlap ∨ hsame row face ∨
              hsame row radius ∨ hsame row fold ∨ hsame row uniform ∨
                hsame row realizationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont cover member visionRead ∧
              Cont visionRead uniform realizationRead ∧ PkgSig bundle realizationRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realizationRead sourceRealization
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
      exact ⟨source.right, coverMemberVision, visionUniformRealization, realizationPkg⟩
  }
  exact ⟨cert, visionUnary, realizationUnary⟩

end BEDC.Derived.FiniteCoverNerveUp
