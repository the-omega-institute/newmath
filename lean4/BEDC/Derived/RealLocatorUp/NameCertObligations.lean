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

def RealLocatorCarrier [AskSetup] [PackageSetup]
    (X Q S R D A H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory X ∧ UnaryHistory Q ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory D ∧
    UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      Cont Q S R ∧ Cont R D A ∧ Cont A H C ∧ Cont C P N ∧ PkgSig bundle N pkg

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

theorem RealLocatorApartnessDecisionWindow [AskSetup] [PackageSetup]
    {X Q S R D A H C P N requestRead regularRead dyadicRead apartnessRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealLocatorCarrier X Q S R D A H C P N bundle pkg ->
      Cont Q S requestRead ->
        Cont requestRead R regularRead ->
          Cont regularRead D dyadicRead ->
            Cont dyadicRead A apartnessRead ->
              Cont apartnessRead N named ->
                PkgSig bundle named pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row named ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row Q ∨ hsame row S ∨ hsame row R ∨
                          hsame row D ∨ hsame row A ∨ hsame row named)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont Q S requestRead ∧
                          Cont requestRead R regularRead ∧ Cont regularRead D dyadicRead ∧
                            Cont dyadicRead A apartnessRead ∧ PkgSig bundle named pkg)
                      hsame ∧
                    UnaryHistory requestRead ∧ UnaryHistory regularRead ∧
                      UnaryHistory dyadicRead ∧ UnaryHistory apartnessRead ∧
                        UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier requestRoute regularRoute dyadicRoute apartnessRoute namedRoute namedPkg
  obtain
    ⟨_xUnary, qUnary, sUnary, rUnary, dUnary, aUnary, _hUnary, _cUnary, _pUnary, nUnary,
      _carrierRequestRoute, _carrierDyadicRoute, _carrierReplayRoute, _carrierNameRoute,
      _carrierPkg⟩ := carrier
  have requestReadUnary : UnaryHistory requestRead :=
    unary_cont_closed qUnary sUnary requestRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed requestReadUnary rUnary regularRoute
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed regularReadUnary dUnary dyadicRoute
  have apartnessReadUnary : UnaryHistory apartnessRead :=
    unary_cont_closed dyadicReadUnary aUnary apartnessRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed apartnessReadUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
              hsame row A ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q S requestRead ∧ Cont requestRead R regularRead ∧
              Cont regularRead D dyadicRead ∧ Cont dyadicRead A apartnessRead ∧
                PkgSig bundle named pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, requestRoute, regularRoute, dyadicRoute, apartnessRoute, namedPkg⟩
  }
  exact
    ⟨cert, requestReadUnary, regularReadUnary, dyadicReadUnary, apartnessReadUnary, namedUnary⟩

end BEDC.Derived.RealLocatorUp
