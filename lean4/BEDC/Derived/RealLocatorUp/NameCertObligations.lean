import BEDC.Derived.RealLocatorUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealLocatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealLocatorNameCertObligations [AskSetup] [PackageSetup]
    {realSeal request stream readback dyadic apartness transport replay provenance localName
      decision : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory realSeal →
      UnaryHistory request →
        UnaryHistory stream →
          UnaryHistory dyadic →
            UnaryHistory replay →
              UnaryHistory provenance →
                Cont request stream readback →
                  Cont readback dyadic apartness →
                    Cont apartness replay decision →
                      Cont decision provenance localName →
                        PkgSig bundle provenance pkg →
                          PkgSig bundle localName pkg →
                            SemanticNameCert
                                (fun row : BHist =>
                                  (hsame row apartness ∨ hsame row decision ∨
                                    hsame row localName) ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row realSeal ∨ hsame row request ∨ hsame row stream ∨
                                    hsame row readback ∨ hsame row dyadic ∨ hsame row apartness ∨
                                      hsame row decision ∨ hsame row localName)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                    PkgSig bundle localName pkg)
                                hsame ∧
                              UnaryHistory readback ∧ UnaryHistory apartness ∧
                                UnaryHistory decision := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro _realSealUnary requestUnary streamUnary dyadicUnary replayUnary provenanceUnary
    requestStreamReadback readbackDyadicApartness apartnessReplayDecision
    decisionProvenanceLocalName provenancePkg localNamePkg
  have _transportSelf : hsame transport transport :=
    hsame_refl transport
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed requestUnary streamUnary requestStreamReadback
  have apartnessUnary : UnaryHistory apartness :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadicApartness
  have decisionUnary : UnaryHistory decision :=
    unary_cont_closed apartnessUnary replayUnary apartnessReplayDecision
  have localNameUnary : UnaryHistory localName :=
    unary_cont_closed decisionUnary provenanceUnary decisionProvenanceLocalName
  have sourceApartness :
      (fun row : BHist =>
        (hsame row apartness ∨ hsame row decision ∨ hsame row localName) ∧ UnaryHistory row)
          apartness := by
    exact ⟨Or.inl (hsame_refl apartness), apartnessUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row apartness ∨ hsame row decision ∨ hsame row localName) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row realSeal ∨ hsame row request ∨ hsame row stream ∨ hsame row readback ∨
              hsame row dyadic ∨ hsame row apartness ∨ hsame row decision ∨
                hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro apartness sourceApartness
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
          | inl sameApartness =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameApartness)
          | inr rest =>
              cases rest with
              | inl sameDecision =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameDecision))
              | inr sameName =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameName))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameApartness =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameApartness)))))
      | inr rest =>
          cases rest with
          | inl sameDecision =>
              exact Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameDecision))))))
          | inr sameName =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameName))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, readbackUnary, apartnessUnary, decisionUnary⟩

end BEDC.Derived.RealLocatorUp
