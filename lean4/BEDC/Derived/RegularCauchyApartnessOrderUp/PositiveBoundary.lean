import BEDC.Derived.RegularCauchyApartnessOrderUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyApartnessOrderUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyApartnessOrderPositiveBoundary [AskSetup] [PackageSetup]
    {X A O M W D R E H C P N budgetRead directionRead windowRead dyadicRead regularRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X ->
      UnaryHistory A ->
        UnaryHistory O ->
          UnaryHistory W ->
            UnaryHistory D ->
              UnaryHistory R ->
                UnaryHistory E ->
                  Cont X A budgetRead ->
                    Cont budgetRead O directionRead ->
                      Cont directionRead W windowRead ->
                        Cont windowRead D dyadicRead ->
                          Cont dyadicRead R regularRead ->
                            Cont regularRead E sealRead ->
                              PkgSig bundle N pkg ->
                                (exists packet : RegularCauchyApartnessOrderUp,
                                  packet =
                                    RegularCauchyApartnessOrderUp.mk X A O M W D R E H C P N) ∧
                                  SemanticNameCert
                                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row X ∨ hsame row A ∨ hsame row O ∨
                                        hsame row W ∨ hsame row D ∨ hsame row R ∨
                                          hsame row E ∨ hsame row sealRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont X A budgetRead ∧
                                        Cont budgetRead O directionRead ∧
                                          Cont directionRead W windowRead ∧
                                            Cont windowRead D dyadicRead ∧
                                              Cont dyadicRead R regularRead ∧
                                                Cont regularRead E sealRead ∧
                                                  PkgSig bundle N pkg)
                                    hsame ∧
                                    UnaryHistory budgetRead ∧ UnaryHistory directionRead ∧
                                      UnaryHistory windowRead ∧ UnaryHistory dyadicRead ∧
                                        UnaryHistory regularRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro xUnary aUnary oUnary wUnary dUnary rUnary eUnary budgetRoute directionRoute
    windowRoute dyadicRoute regularRoute sealRoute namePkg
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed xUnary aUnary budgetRoute
  have directionUnary : UnaryHistory directionRead :=
    unary_cont_closed budgetUnary oUnary directionRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed directionUnary wUnary windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary dUnary dyadicRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed dyadicUnary rUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary eUnary sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row X ∨ hsame row A ∨ hsame row O ∨ hsame row W ∨ hsame row D ∨
            hsame row R ∨ hsame row E ∨ hsame row sealRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont X A budgetRead ∧ Cont budgetRead O directionRead ∧
            Cont directionRead W windowRead ∧ Cont windowRead D dyadicRead ∧
              Cont dyadicRead R regularRead ∧ Cont regularRead E sealRead ∧
                PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact
        ⟨source.right, budgetRoute, directionRoute, windowRoute, dyadicRoute, regularRoute,
          sealRoute, namePkg⟩
  }
  exact
    ⟨Exists.intro (RegularCauchyApartnessOrderUp.mk X A O M W D R E H C P N) rfl,
      cert, budgetUnary, directionUnary, windowUnary, dyadicUnary, regularUnary,
      sealUnary⟩

theorem RegularCauchyApartnessOrderLocatedComparisonScope [AskSetup] [PackageSetup]
    {X A O M W D R E H C P N budgetWindow positiveBound regularRead realSeal named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X ->
      UnaryHistory A ->
      UnaryHistory W ->
          UnaryHistory D ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory N ->
                  Cont A W budgetWindow ->
                    Cont budgetWindow D positiveBound ->
                      Cont positiveBound R regularRead ->
                        Cont regularRead E realSeal ->
                          Cont realSeal N named ->
                            PkgSig bundle P pkg ->
                              UnaryHistory budgetWindow ∧
                                UnaryHistory positiveBound ∧
                                  UnaryHistory regularRead ∧
                                    UnaryHistory realSeal ∧
                                      UnaryHistory named ∧
                                        Cont A W budgetWindow ∧
                                          Cont budgetWindow D positiveBound ∧
                                            Cont positiveBound R regularRead ∧
                                              Cont regularRead E realSeal ∧
                                                Cont realSeal N named ∧
                                                  PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro _xUnary aUnary wUnary dUnary rUnary eUnary nUnary budgetRoute positiveRoute
    regularRoute sealRoute namedRoute pkgSig
  have budgetUnary : UnaryHistory budgetWindow :=
    unary_cont_closed aUnary wUnary budgetRoute
  have positiveUnary : UnaryHistory positiveBound :=
    unary_cont_closed budgetUnary dUnary positiveRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed positiveUnary rUnary regularRoute
  have sealUnary : UnaryHistory realSeal :=
    unary_cont_closed regularUnary eUnary sealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed sealUnary nUnary namedRoute
  exact
    ⟨budgetUnary, positiveUnary, regularUnary, sealUnary, namedUnary, budgetRoute,
      positiveRoute, regularRoute, sealRoute, namedRoute, pkgSig⟩

def RegularCauchyApartnessOrderCarrier [AskSetup] [PackageSetup]
    (source budget direction modulus window positiveBound readback realSeal transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory source ∧ UnaryHistory budget ∧ UnaryHistory direction ∧
    UnaryHistory modulus ∧ UnaryHistory window ∧ UnaryHistory positiveBound ∧
      UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
        UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont window positiveBound readback ∧ Cont transport replay localName ∧
            PkgSig bundle provenance pkg

theorem RegularCauchyApartnessOrderRefusalBoundary [AskSetup] [PackageSetup]
    {source budget direction modulus window positiveBound readback realSeal transport replay
      provenance localName sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyApartnessOrderCarrier source budget direction modulus window positiveBound
        readback realSeal transport replay provenance localName bundle pkg ->
      Cont readback realSeal sealRead ->
        PkgSig bundle sealRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row source ∨ hsame row budget ∨ hsame row direction ∨
                  hsame row window ∨ hsame row positiveBound ∨ hsame row readback ∨
                    hsame row realSeal ∨ hsame row sealRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont window positiveBound readback ∧
                  Cont readback realSeal sealRead ∧ PkgSig bundle sealRead pkg ∧
                    PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier sealRoute sealPkg
  obtain
    ⟨_sourceUnary, _budgetUnary, _directionUnary, _modulusUnary, _windowUnary,
      _positiveUnary, readbackUnary, realSealUnary, _transportUnary, _replayUnary,
      _provenanceUnary, _localNameUnary, windowPositiveRoute, _replayLocalRoute,
      provenancePkg⟩ := carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary realSealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row budget ∨ hsame row direction ∨
              hsame row window ∨ hsame row positiveBound ∨ hsame row readback ∨
                hsame row realSeal ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont window positiveBound readback ∧
              Cont readback realSeal sealRead ∧ PkgSig bundle sealRead pkg ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact ⟨source.right, windowPositiveRoute, sealRoute, sealPkg, provenancePkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.RegularCauchyApartnessOrderUp
